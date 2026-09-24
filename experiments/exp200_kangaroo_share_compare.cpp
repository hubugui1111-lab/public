#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>

using namespace sci;
using Clock=std::chrono::steady_clock;
namespace {
constexpr int N=6144, ELL=24;
constexpr uint64_t MASK=(1ULL<<ELL)-1;
struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F> Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);auto e=Clock::now();
  return {io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(e-t).count()};
}
uint64_t enc(int64_t x){return uint64_t(x)&MASK;}
int64_t dec(uint64_t x){x&=MASK;return (x&(1ULL<<(ELL-1)))?int64_t(x)-int64_t(1ULL<<ELL):int64_t(x);}

std::vector<uint64_t> open_both(IOPack&io,int party,const std::vector<uint64_t>&x){
  std::vector<uint64_t> p(x.size()),o(x.size());
  if(party==ALICE){io.io->send_data(x.data(),int(x.size()*8));io.io->flush();io.io->recv_data(p.data(),int(p.size()*8));}
  else{io.io->recv_data(p.data(),int(p.size()*8));io.io->send_data(x.data(),int(x.size()*8));io.io->flush();}
  for(size_t i=0;i<x.size();++i)o[i]=(x[i]+p[i])&MASK;
  return o;
}
void share_from_alice(IOPack&io,int party,PRG128&rng,const std::vector<uint64_t>&clear,std::vector<uint64_t>&local){
  local.resize(clear.size());std::vector<uint64_t> peer(clear.size());
  if(party==ALICE){
    rng.random_data(local.data(),local.size()*8);
    for(size_t i=0;i<local.size();++i){local[i]&=MASK;peer[i]=(clear[i]-local[i])&MASK;}
    io.io->send_data(peer.data(),int(peer.size()*8));io.io->flush();
  }else io.io->recv_data(local.data(),int(local.size()*8));
}
struct Prep{
  std::vector<uint64_t> alpha,beta,a,b,c;
  std::vector<uint8_t> flip;
  Phase phase;
};
Prep prepare(FPMath&math,IOPack&io,int party,PRG128&rng){
  Prep p;std::vector<uint64_t> ac(N),bc(N);
  p.flip.assign(N,0);
  auto t=Clock::now();auto b0=io.get_comm(),r0=io.get_rounds();
  if(party==ALICE){
    std::vector<uint64_t> raw(2*N);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<N;++i){
      int A=2+int(raw[2*i]%511); // 2..512
      int B=1+int(raw[2*i+1]%uint64_t(A-1)); // 1..A-1, never zero
      uint8_t f=uint8_t((raw[2*i]>>17)&1);p.flip[i]=f;
      int s=f?-1:1;
      ac[i]=enc(int64_t(s)*A);bc[i]=enc(int64_t(s)*B);
    }
  }
  share_from_alice(io,party,rng,ac,p.alpha);
  share_from_alice(io,party,rng,bc,p.beta);
  if(party==BOB)p.flip.assign(N,0);

  p.a.resize(N);p.b.resize(N);
  rng.random_data(p.a.data(),N*8);rng.random_data(p.b.data(),N*8);
  for(int i=0;i<N;++i){p.a[i]&=MASK;p.b[i]&=MASK;}
  FixArray Aarr(party,N,true,ELL,0),Barr(party,N,true,ELL,0);
  std::copy(p.a.begin(),p.a.end(),Aarr.data);std::copy(p.b.begin(),p.b.end(),Barr.data);
  auto Carr=math.fix->mul(Aarr,Barr,ELL);flush(io);
  p.c.assign(Carr.data,Carr.data+N);
  p.phase={io.get_comm()-b0,io.get_rounds()-r0,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
  return p;
}
}
int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;
  auto prep=prepare(math,io,party,rng);

  std::vector<uint64_t> dclear(N),dshare;
  if(party==ALICE)for(int i=0;i<N;++i){
    int64_t v=int64_t((i*7919)%8191)-4095; // public test range
    dclear[i]=enc(v);
  }
  share_from_alice(io,party,rng,dclear,dshare);

  BoolArray result(party,N);
  auto online=measure(io,[&]{
    // One Beaver product alpha*d.
    std::vector<uint64_t> masked(2*N);
    for(int i=0;i<N;++i){masked[i]=(prep.alpha[i]-prep.a[i])&MASK;masked[N+i]=(dshare[i]-prep.b[i])&MASK;}
    auto opened=open_both(io,party,masked);
    std::vector<uint64_t> tshare(N);
    for(int i=0;i<N;++i){
      __uint128_t v=prep.c[i];
      v+=__uint128_t(opened[i])*prep.b[i];
      v+=__uint128_t(opened[N+i])*prep.a[i];
      if(party==ALICE)v+=__uint128_t(opened[i])*opened[N+i];
      tshare[i]=(uint64_t(v)+prep.beta[i])&MASK;
    }

    // Open only the randomized affine value to the client (BOB).
    std::vector<uint64_t> server_share;
    if(party==ALICE){
      io.io->send_data(tshare.data(),N*8);io.io->flush();
      std::vector<uint8_t> masked_bit(N);
      io.io->recv_data(masked_bit.data(),N);
      for(int i=0;i<N;++i)result.data[i]=uint8_t(masked_bit[i]^prep.flip[i]);
    }else{
      server_share.resize(N);io.io->recv_data(server_share.data(),N*8);
      std::vector<uint8_t> masked_bit(N),client_share(N);
      std::vector<uint64_t> rand(N);rng.random_data(rand.data(),N*8);
      for(int i=0;i<N;++i){
        uint64_t t=(tshare[i]+server_share[i])&MASK;
        uint8_t blinded=uint8_t(dec(t)>=0);
        client_share[i]=uint8_t(rand[i]&1);
        masked_bit[i]=uint8_t(blinded^client_share[i]);
        result.data[i]=client_share[i];
      }
      io.io->send_data(masked_bit.data(),N);io.io->flush();
    }
  });

  auto pub=math.bool_op->output(PUBLIC,result);
  int mismatches=0;
  if(party==ALICE)for(int i=0;i<N;++i)mismatches+=int(bool(pub.data[i])!=(dec(dclear[i])>=0));

  FixArray base(party,N,true,ELL,0);std::copy(dshare.begin(),dshare.end(),base.data);
  BoolArray bcmp;
  auto baseline=measure(io,[&]{bcmp=math.fix->GE(base,uint64_t(0));});
  auto bpub=math.bool_op->output(PUBLIC,bcmp);
  if(party==ALICE)for(int i=0;i<N;++i)mismatches+=int(bool(bpub.data[i])!=(dec(dclear[i])>=0));

  std::cout<<"EXP200_RESULT party="<<party
           <<" n="<<N<<" preprocess_bytes="<<prep.phase.bytes<<" preprocess_rounds="<<prep.phase.rounds<<" preprocess_ms="<<prep.phase.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" sci_bytes="<<baseline.bytes<<" sci_rounds="<<baseline.rounds<<" sci_ms="<<baseline.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}
