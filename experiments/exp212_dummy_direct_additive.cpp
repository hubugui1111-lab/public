#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;
constexpr int N=320,ELL=24;
constexpr uint64_t MASK=(1ULL<<ELL)-1;

struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  std::vector<uint8_t> truth(N),flip(N),masked(N);
  for(int i=0;i<N;++i)truth[i]=uint8_t(i<137);
  if(party==ALICE){
    std::vector<uint64_t>r(N);rng.random_data(r.data(),N*8);
    for(int i=0;i<N;++i){flip[i]=uint8_t(r[i]&1);masked[i]=truth[i]^flip[i];}
    io.io->send_data(masked.data(),N);io.io->flush();
  }else io.io->recv_data(masked.data(),N);

  std::vector<uint64_t> ashare(N,0),recv(N,0),raw(N);
  std::vector<uint8_t> choices(N);
  std::vector<std::array<uint64_t,2>> msgs;
  std::vector<uint64_t*> ptrs;

  auto direct=measure(io,[&]{
    if(party==ALICE){
      rng.random_data(raw.data(),N*8);
      msgs.resize(N);ptrs.resize(N);
      for(int i=0;i<N;++i){
        ashare[i]=raw[i]&MASK;
        for(int ch=0;ch<2;++ch){
          const uint8_t bit=uint8_t(ch)^flip[i];
          msgs[i][ch]=(uint64_t(bit)-ashare[i])&MASK;
        }
        ptrs[i]=msgs[i].data();
      }
      ot.kkot[0]->send(ptrs.data(),N,ELL);
    }else{
      for(int i=0;i<N;++i)choices[i]=masked[i]&1;
      ot.kkot[0]->recv(recv.data(),choices.data(),N,ELL);
      for(int i=0;i<N;++i)ashare[i]=recv[i]&MASK;
    }
  });

  // Current path baseline: reconstruct XOR shares of semantic bits, then B2A.
  BoolArray bits(party,N);
  std::vector<uint8_t> bshare(N),peer(N);
  if(party==ALICE){
    std::vector<uint64_t>r(N);rng.random_data(r.data(),N*8);
    for(int i=0;i<N;++i){bshare[i]=uint8_t(r[i]&1);peer[i]=truth[i]^bshare[i];}
    io.io->send_data(peer.data(),N);io.io->flush();
  }else io.io->recv_data(bshare.data(),N);
  for(int i=0;i<N;++i)bits.data[i]=bshare[i];
  FixArray out;
  auto base=measure(io,[&]{out=math.fix->B2A(bits,false,ELL);});

  std::vector<uint64_t> other(N);
  if(party==ALICE){
    io.io->send_data(ashare.data(),N*8);io.io->flush();
    io.io->recv_data(other.data(),N*8);
  }else{
    io.io->recv_data(other.data(),N*8);
    io.io->send_data(ashare.data(),N*8);io.io->flush();
  }
  int mismatches=0;
  for(int i=0;i<N;++i)mismatches+=int(((ashare[i]+other[i])&MASK)!=truth[i]);

  std::cout<<"EXP212_RESULT party="<<party
           <<" direct_bytes="<<direct.bytes<<" direct_rounds="<<direct.rounds<<" direct_ms="<<direct.ms
           <<" b2a_bytes="<<base.bytes<<" b2a_rounds="<<base.rounds<<" b2a_ms="<<base.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}