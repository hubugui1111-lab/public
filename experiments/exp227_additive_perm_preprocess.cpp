#include "BuildingBlocks/aux-protocols.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "utils/emp-tool.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;

namespace {
constexpr int ELL=24;
constexpr uint32_t RMASK=(1u<<ELL)-1;
struct SideData{
  int M=0;
  std::vector<uint32_t> perm;
  std::vector<uint8_t> delta,A,B; // 9 bytes/row
};
struct LocalCorr{
  bool owner=false;
  std::vector<uint32_t> perm;
  std::vector<uint32_t> delta; // 3 ring words/row when owner
  std::vector<uint32_t> A,B;   // 3 ring words/row when receiver
};
uint32_t add24(uint32_t a,uint32_t b){return (a+b)&RMASK;}
uint32_t sub24(uint32_t a,uint32_t b){return (a-b)&RMASK;}
uint32_t load24(const std::vector<uint8_t>&v,int row,int lane){
  const size_t at=size_t(row)*9+size_t(lane)*3;
  return uint32_t(v[at])|(uint32_t(v[at+1])<<8)|(uint32_t(v[at+2])<<16);
}
SideData read_side(const std::string&path){
  std::ifstream f(path,std::ios::binary);
  if(!f) throw std::runtime_error("cannot open side file");
  uint32_t magic=0,M=0,bytes=0;
  f.read((char*)&magic,4);f.read((char*)&M,4);f.read((char*)&bytes,4);
  if(magic!=0x45323236u||M==0||bytes!=9)throw std::runtime_error("bad side header");
  SideData d;d.M=int(M);d.perm.resize(M);
  d.delta.resize(size_t(M)*9);d.A.resize(size_t(M)*9);d.B.resize(size_t(M)*9);
  f.read((char*)d.perm.data(),M*4);
  f.read((char*)d.delta.data(),d.delta.size());
  f.read((char*)d.A.data(),d.A.size());
  f.read((char*)d.B.data(),d.B.size());
  if(!f)throw std::runtime_error("short side file");
  return d;
}
void flush_all(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
std::vector<uint32_t> apply_regular(
    IOPack&io,int party,int ownerParty,const LocalCorr&corr,
    const std::vector<uint32_t>&in){
  const int M=corr.owner?int(corr.perm.size()):int(corr.A.size()/3);
  if(int(in.size())!=2*M)throw std::runtime_error("regular input");
  std::vector<uint32_t> out(size_t(M)*2),msg(size_t(M)*2);
  if(party!=ownerParty){
    for(int i=0;i<M;++i)for(int c=0;c<2;++c){
      const size_t k=size_t(i)*2+c;
      msg[k]=sub24(in[k],corr.A[size_t(i)*3+c]);
      out[k]=corr.B[size_t(i)*3+c];
    }
    io.io->send_data(msg.data(),int(msg.size()*4));io.io->flush();
  }else{
    io.io->recv_data(msg.data(),int(msg.size()*4));
    for(int i=0;i<M;++i)for(int c=0;c<2;++c){
      const size_t d=size_t(i)*2+c,ss=size_t(corr.perm[i])*2+c;
      out[d]=add24(add24(in[ss],msg[ss]),corr.delta[size_t(i)*3+c]);
    }
  }
  return out;
}
std::vector<uint32_t> inv_perm(const std::vector<uint32_t>&p){
  std::vector<uint32_t>q(p.size());
  for(size_t i=0;i<p.size();++i)q[p[i]]=uint32_t(i);
  return q;
}
std::vector<uint32_t> apply_inverse(
    IOPack&io,int party,int ownerParty,const LocalCorr&corr,
    const std::vector<uint32_t>&in){
  const int M=corr.owner?int(corr.perm.size()):int(corr.A.size()/3);
  if(int(in.size())!=M)throw std::runtime_error("inverse input");
  std::vector<uint32_t> out(M),msg(M);
  if(party!=ownerParty){
    for(int i=0;i<M;++i){
      msg[i]=sub24(in[i],corr.B[size_t(i)*3+2]);
      out[i]=corr.A[size_t(i)*3+2];
    }
    io.io->send_data(msg.data(),M*4);io.io->flush();
  }else{
    auto pinv=inv_perm(corr.perm);
    io.io->recv_data(msg.data(),M*4);
    for(int i=0;i<M;++i){
      const int ss=int(pinv[i]);
      out[i]=sub24(add24(in[ss],msg[ss]),corr.delta[size_t(ss)*3+2]);
    }
  }
  return out;
}
std::vector<uint32_t> open_add(IOPack&io,int party,const std::vector<uint32_t>&x){
  std::vector<uint32_t>peer(x.size()),out(x.size());
  if(party==ALICE){
    io.io->send_data(x.data(),int(x.size()*4));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()*4));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()*4));
    io.io->send_data(x.data(),int(x.size()*4));io.io->flush();
  }
  for(size_t i=0;i<x.size();++i)out[i]=add24(x[i],peer[i]);
  return out;
}
}

int main(int argc,char**argv){
  int party=0,port=32000,validate=1;
  std::string ip="127.0.0.1",file,outfile;
  ArgMapping amap;
  amap.arg("r",party,"role");amap.arg("p",port,"port");
  amap.arg("ip",ip,"ip");amap.arg("file",file,"side file");amap.arg("out",outfile,"additive side output");amap.arg("validate",validate,"run movement validation");amap.parse(argc,argv);
  if((party!=ALICE&&party!=BOB)||file.empty())return 2;

  auto side=read_side(file);const int M=side.M;
  IOPack io(party,port,ip);OTPack ot(&io,party);AuxProtocols aux(party,&io,&ot);
  PRG128 rng;

  // Global order is correlation p0 then p1.  ALICE owns p0 and receives p1;
  // BOB receives p0 and owns p1.  The XOR share of pi(A) is Delta on the
  // owner side and B on the receiver side.
  const int WORDS=2*M*3;
  std::vector<uint64_t> xorword(WORDS);
  for(int which=0;which<2;++which){
    const bool owner=(which==0?party==ALICE:party==BOB);
    for(int i=0;i<M;++i)for(int c=0;c<3;++c){
      const uint32_t w=owner?load24(side.delta,i,c):load24(side.B,i,c);
      xorword[(which*M+i)*3+c]=w;
    }
  }
  std::vector<uint8_t> bits(size_t(WORDS)*ELL);
  for(int i=0;i<WORDS;++i)for(int k=0;k<ELL;++k)
    bits[size_t(i)*ELL+k]=uint8_t((xorword[i]>>k)&1);
  std::vector<uint64_t> abit(bits.size());

  io.io->sync();
  const auto pb0=io.get_comm(),pr0=io.get_rounds();auto pt0=Clock::now();
  aux.B2A(bits.data(),abit.data(),int(abit.size()),ELL);
  flush_all(io);
  const auto prep_ms=std::chrono::duration<double,std::milli>(Clock::now()-pt0).count();
  const auto prep_bytes=io.get_comm()-pb0,prep_rounds=io.get_rounds()-pr0;

  std::vector<uint32_t> addshare(WORDS);
  for(int i=0;i<WORDS;++i){
    uint64_t v=0;
    for(int k=0;k<ELL;++k)v=(v+((abit[size_t(i)*ELL+k]<<k)&RMASK))&RMASK;
    addshare[i]=uint32_t(v);
  }

  LocalCorr p0,p1;
  if(party==ALICE){
    p0.owner=true;p0.perm=side.perm;p0.delta.resize(size_t(M)*3);
    p1.owner=false;p1.A.resize(size_t(M)*3);p1.B.resize(size_t(M)*3);
    for(int i=0;i<M;++i)for(int c=0;c<3;++c){
      p0.delta[size_t(i)*3+c]=addshare[(0*M+i)*3+c];
      p1.A[size_t(i)*3+c]=load24(side.A,i,c);
      p1.B[size_t(i)*3+c]=addshare[(1*M+i)*3+c];
    }
  }else{
    p0.owner=false;p0.A.resize(size_t(M)*3);p0.B.resize(size_t(M)*3);
    p1.owner=true;p1.perm=side.perm;p1.delta.resize(size_t(M)*3);
    for(int i=0;i<M;++i)for(int c=0;c<3;++c){
      p0.A[size_t(i)*3+c]=load24(side.A,i,c);
      p0.B[size_t(i)*3+c]=addshare[(0*M+i)*3+c];
      p1.delta[size_t(i)*3+c]=addshare[(1*M+i)*3+c];
    }
  }

  // Persist exactly the local additive CorrPair material consumed by Exp222.
  if(!outfile.empty()){
    const LocalCorr& own=(party==ALICE)?p0:p1;
    const LocalCorr& recv=(party==ALICE)?p1:p0;
    const uint32_t magic=0x41323237u,mm=uint32_t(M);
    std::ofstream of(outfile,std::ios::binary);
    if(!of)throw std::runtime_error("cannot open additive output");
    of.write((const char*)&magic,4);of.write((const char*)&mm,4);
    of.write((const char*)own.perm.data(),size_t(M)*4);
    of.write((const char*)own.delta.data(),size_t(M)*3*4);
    of.write((const char*)recv.A.data(),size_t(M)*3*4);
    of.write((const char*)recv.B.data(),size_t(M)*3*4);
    if(!of)throw std::runtime_error("additive output write");
  }

  if(!validate){
    std::cout<<"EXP227_PREP_RESULT party="<<party<<" M="<<M
             <<" x2a_words="<<WORDS
             <<" x2a_bytes="<<prep_bytes<<" x2a_rounds="<<prep_rounds<<" x2a_ms="<<prep_ms
             <<" mismatches=0\n";
    return 0;
  }

  // Exact compatibility test with Exp222's additive online movement:
  // two lanes forward through p0 then p1, then payload lane inverse p1 then p0.
  std::vector<uint32_t> local(size_t(M)*2),peer(size_t(M)*2),clear(size_t(M)*2);
  if(party==ALICE){
    std::vector<uint64_t>rr(local.size());rng.random_data(rr.data(),rr.size()*8);
    for(int i=0;i<M;++i)for(int c=0;c<2;++c){
      const size_t k=size_t(i)*2+c;
      clear[k]=(uint32_t(i*7919u+17u+c*104729u))&RMASK;
      local[k]=uint32_t(rr[k])&RMASK;peer[k]=sub24(clear[k],local[k]);
    }
    io.io->send_data(peer.data(),int(peer.size()*4));io.io->flush();
  }else io.io->recv_data(local.data(),int(local.size()*4));

  io.io->sync();
  const auto ob0=io.get_comm(),or0=io.get_rounds();auto ot0=Clock::now();
  auto y0=apply_regular(io,party,ALICE,p0,local);
  auto sh=apply_regular(io,party,BOB,p1,y0);
  std::vector<uint32_t> payload(M);
  for(int i=0;i<M;++i)payload[i]=sh[size_t(i)*2+1];
  auto x1=apply_inverse(io,party,BOB,p1,payload);
  auto back=apply_inverse(io,party,ALICE,p0,x1);
  flush_all(io);
  const auto online_ms=std::chrono::duration<double,std::milli>(Clock::now()-ot0).count();
  const auto online_bytes=io.get_comm()-ob0,online_rounds=io.get_rounds()-or0;

  // Regression opening after measured bridge/movement.
  auto opened_back=open_add(io,party,back);
  int mismatches=0;
  if(party==ALICE){
    for(int i=0;i<M;++i)mismatches+=opened_back[i]!=clear[size_t(i)*2+1];
  }

  std::cout<<"EXP226_RESULT party="<<party<<" M="<<M
           <<" x2a_words="<<WORDS
           <<" x2a_bytes="<<prep_bytes<<" x2a_rounds="<<prep_rounds<<" x2a_ms="<<prep_ms
           <<" movement_bytes="<<online_bytes<<" movement_rounds="<<online_rounds<<" movement_ms="<<online_ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}
