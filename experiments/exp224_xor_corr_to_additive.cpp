#include "BuildingBlocks/aux-protocols.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "utils/emp-tool.h"
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;

namespace {
constexpr int BW=24;
constexpr uint32_t MASK=(1u<<BW)-1;

struct XorPrep{
  uint32_t M=0,bpr=0;
  std::vector<uint32_t> own_perm;
  std::vector<uint8_t> own_delta,recvA,recvB;
};

XorPrep read_xor(const std::string&path){
  std::ifstream is(path,std::ios::binary);
  if(!is)throw std::runtime_error("open xor prep");
  char magic[8];is.read(magic,8);
  if(std::string(magic,8)!="E224XOR1")throw std::runtime_error("xor magic");
  XorPrep x;is.read((char*)&x.M,4);is.read((char*)&x.bpr,4);
  if(!x.M||x.bpr!=9)throw std::runtime_error("xor shape");
  x.own_perm.resize(x.M);
  x.own_delta.resize(size_t(x.M)*x.bpr);
  x.recvA.resize(size_t(x.M)*x.bpr);
  x.recvB.resize(size_t(x.M)*x.bpr);
  is.read((char*)x.own_perm.data(),x.own_perm.size()*4);
  is.read((char*)x.own_delta.data(),x.own_delta.size());
  is.read((char*)x.recvA.data(),x.recvA.size());
  is.read((char*)x.recvB.data(),x.recvB.size());
  if(!is)throw std::runtime_error("xor truncated");
  return x;
}
std::vector<uint32_t> words24(const std::vector<uint8_t>&b,uint32_t M){
  if(b.size()!=size_t(M)*9)throw std::runtime_error("word shape");
  std::vector<uint32_t>w(size_t(M)*3);
  for(uint32_t i=0;i<M;++i)for(int k=0;k<3;++k){
    const size_t o=size_t(i)*9+size_t(k)*3;
    w[size_t(i)*3+k]=uint32_t(b[o])|(uint32_t(b[o+1])<<8)|(uint32_t(b[o+2])<<16);
  }
  return w;
}
void write_add(const std::string&path,const XorPrep&x,
               const std::vector<uint32_t>&own_delta,
               const std::vector<uint32_t>&recvA,
               const std::vector<uint32_t>&recvB){
  std::ofstream os(path,std::ios::binary);
  if(!os)throw std::runtime_error("open add prep");
  const char magic[8]={'E','2','2','4','A','D','D','1'};
  os.write(magic,8);os.write((char*)&x.M,4);
  os.write((char*)x.own_perm.data(),x.own_perm.size()*4);
  os.write((char*)own_delta.data(),own_delta.size()*4);
  os.write((char*)recvA.data(),recvA.size()*4);
  os.write((char*)recvB.data(),recvB.size()*4);
  if(!os)throw std::runtime_error("write add prep");
}
void exchange_u32(IOPack&io,int party,const std::vector<uint32_t>&mine,std::vector<uint32_t>&peer){
  peer.resize(mine.size());
  if(party==ALICE){
    io.io->send_data(mine.data(),int(mine.size()*4));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()*4));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()*4));
    io.io->send_data(mine.data(),int(mine.size()*4));io.io->flush();
  }
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1",in_path,out_path;
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");
  amap.arg("ip",ip,"ip");amap.arg("in",in_path,"input");amap.arg("out",out_path,"output");amap.parse(argc,argv);
  if((party!=ALICE&&party!=BOB)||in_path.empty()||out_path.empty())return 2;

  IOPack io(party,port,ip);OTPack ot(&io,party);AuxProtocols aux(party,&io,&ot);
  auto x=read_xor(in_path);const int W=int(x.M)*3;
  auto own_delta_x=words24(x.own_delta,x.M);
  auto recvA=words24(x.recvA,x.M);
  auto recvB_x=words24(x.recvB,x.M);

  // Fixed global ordering: first 3M words are ALICE's permutation relation,
  // second 3M are BOB's.  Each relation is represented as XOR shares
  // sender_delta XOR receiver_B = perm(receiver_A).
  std::vector<uint32_t> local_words(size_t(2)*W);
  if(party==ALICE){
    std::copy(own_delta_x.begin(),own_delta_x.end(),local_words.begin());
    std::copy(recvB_x.begin(),recvB_x.end(),local_words.begin()+W);
  }else{
    std::copy(recvB_x.begin(),recvB_x.end(),local_words.begin());
    std::copy(own_delta_x.begin(),own_delta_x.end(),local_words.begin()+W);
  }

  std::vector<uint8_t> bits(size_t(2)*W*BW);
  for(int i=0;i<2*W;++i)for(int k=0;k<BW;++k)
    bits[size_t(i)*BW+k]=uint8_t((local_words[i]>>k)&1);
  std::vector<uint64_t> arith(bits.size());

  io.io->sync();
  const auto c0=io.get_comm(),r0=io.get_rounds();auto t0=Clock::now();
  aux.B2A(bits.data(),arith.data(),int(arith.size()),BW);
  io.io->flush();io.io_rev->flush();io.io_GC->flush();
  const double ms=std::chrono::duration<double,std::milli>(Clock::now()-t0).count();
  const uint64_t bytes=io.get_comm()-c0,rounds=io.get_rounds()-r0;

  std::vector<uint32_t> add_words(size_t(2)*W);
  for(int i=0;i<2*W;++i){
    uint64_t v=0;
    for(int k=0;k<BW;++k)v=(v+((arith[size_t(i)*BW+k]<<k)&MASK))&MASK;
    add_words[i]=uint32_t(v);
  }
  std::vector<uint32_t> own_delta(W),recvB(W);
  if(party==ALICE){
    std::copy(add_words.begin(),add_words.begin()+W,own_delta.begin());
    std::copy(add_words.begin()+W,add_words.end(),recvB.begin());
  }else{
    std::copy(add_words.begin()+W,add_words.end(),own_delta.begin());
    std::copy(add_words.begin(),add_words.begin()+W,recvB.begin());
  }
  write_add(out_path,x,own_delta,recvA,recvB);

  // Test-only full relation audit after measured conversion.
  std::vector<uint32_t> peerA,peerB;
  exchange_u32(io,party,recvA,peerA);
  exchange_u32(io,party,recvB,peerB);
  int mismatches=0;
  for(uint32_t i=0;i<x.M;++i){
    const uint32_t src=x.own_perm[i];
    if(src>=x.M){++mismatches;continue;}
    for(int k=0;k<3;++k){
      const uint32_t lhs=(own_delta[size_t(i)*3+k]+peerB[size_t(i)*3+k])&MASK;
      const uint32_t rhs=peerA[size_t(src)*3+k]&MASK;
      mismatches+=lhs!=rhs;
    }
  }

  std::cout<<"EXP224_X2A_RESULT party="<<party<<" M="<<x.M
           <<" words="<<(2*W)<<" bit_conversions="<<(uint64_t(2)*W*BW)
           <<" rounds="<<rounds<<" bytes="<<bytes<<" ms="<<ms
           <<" mismatches="<<mismatches<<" out="<<out_path<<"\n";
  return mismatches?3:0;
}
