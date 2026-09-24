#include "NonLinear/relu-ring.h"
#include "utils/io_pack.h"
#include "utils/emp-tool.h"
#include "OT/emp-ot.h"
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

using namespace sci;

int main(int argc,char**argv){
  int party=0,port=32000,N=320,b=4,l=48;
  std::string address="127.0.0.1";
  ArgMapping amap;
  amap.arg("r",party,"role");
  amap.arg("p",port,"port");
  amap.arg("N",N,"number");
  amap.arg("b",b,"radix");
  amap.arg("ip",address,"ip");
  amap.parse(argc,argv);
  if((party!=ALICE&&party!=BOB)||N<=0) return 2;

  IOPack io(party,port,address);
  OTPack ot(&io,party);
  ReLURingProtocol<uint64_t> relu(party,RING,&io,l,b,&ot);

  const uint64_t mask=(1ULL<<48)-1;
  PRG128 prg;
  std::vector<uint64_t> share(N),out(N),peer(N),out_peer(N);
  if(party==ALICE){
    std::vector<uint64_t> other(N);
    prg.random_data(share.data(),N*8);
    for(int i=0;i<N;++i){
      int64_t clear=(int64_t(i)*7919)%2000001-1000000;
      uint64_t v=uint64_t(clear)&mask;
      share[i]&=mask;
      other[i]=(v-share[i])&mask;
    }
    io.io->send_data(other.data(),N*8);
    io.io->flush();
  }else{
    io.io->recv_data(share.data(),N*8);
  }

  io.io->sync();
  const auto c0=io.get_comm(),r0=io.get_rounds();
  auto t0=std::chrono::steady_clock::now();
  relu.relu(out.data(),share.data(),N,nullptr,false);
  io.io->flush(); io.io_rev->flush(); io.io_GC->flush();
  auto t1=std::chrono::steady_clock::now();
  const auto bytes=io.get_comm()-c0,rounds=io.get_rounds()-r0;
  const double ms=std::chrono::duration<double,std::milli>(t1-t0).count();

  int mismatches=0;
  if(party==ALICE){
    io.io->send_data(share.data(),N*8);
    io.io->send_data(out.data(),N*8);
    io.io->flush();
  }else{
    io.io->recv_data(peer.data(),N*8);
    io.io->recv_data(out_peer.data(),N*8);
    for(int i=0;i<N;++i){
      uint64_t x=(share[i]+peer[i])&mask;
      uint64_t y=(out[i]+out_peer[i])&mask;
      int64_t sx=(x&(1ULL<<47))?int64_t(x-(1ULL<<48)):int64_t(x);
      uint64_t exp=sx>=0?x:0;
      mismatches += y!=exp;
    }
  }
  std::cout<<"EXP193_RESULT party="<<party
           <<" N="<<N<<" radix="<<b
           <<" rounds="<<rounds
           <<" bytes="<<bytes
           <<" ms="<<ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}
