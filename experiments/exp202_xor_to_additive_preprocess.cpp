#include "BuildingBlocks/aux-protocols.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "utils/emp-tool.h"
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>

using namespace sci;
using Clock=std::chrono::steady_clock;

int main(int argc,char**argv){
  int party=0,port=32000,N=20352,bw=24;
  std::string address="127.0.0.1";
  ArgMapping amap;
  amap.arg("r",party,"role");
  amap.arg("p",port,"port");
  amap.arg("N",N,"words");
  amap.arg("bw",bw,"bitwidth");
  amap.arg("ip",address,"ip");
  amap.parse(argc,argv);
  if((party!=ALICE&&party!=BOB)||N<=0||bw<=0||bw>=63) return 2;

  IOPack io(party,port,address);
  OTPack ot(&io,party);
  AuxProtocols aux(party,&io,&ot);
  const uint64_t mask=(uint64_t(1)<<bw)-1;

  std::vector<uint64_t> local(N),clear(N),peer(N),out(N);
  PRG128 prg;
  if(party==ALICE){
    prg.random_data(local.data(),N*8);
    for(int i=0;i<N;++i){
      clear[i]=(uint64_t(i)*7919+17)&mask;
      local[i]&=mask;
      peer[i]=clear[i]^local[i];
    }
    io.io->send_data(peer.data(),int(N*8));
    io.io->flush();
  }else{
    io.io->recv_data(local.data(),int(N*8));
  }

  // Every local word is an XOR share. Decompose locally into XOR-shared bits,
  // then convert all bits in one batched SCI B2A call and recombine mod 2^bw.
  std::vector<uint8_t> bits(size_t(N)*bw);
  for(int i=0;i<N;++i) for(int k=0;k<bw;++k)
    bits[size_t(i)*bw+k]=uint8_t((local[i]>>k)&1);

  std::vector<uint64_t> arith(bits.size());
  io.io->sync();
  const auto c0=io.get_comm(),r0=io.get_rounds();
  auto t0=Clock::now();
  aux.B2A(bits.data(),arith.data(),int(arith.size()),bw);
  io.io->flush();io.io_rev->flush();io.io_GC->flush();
  auto t1=Clock::now();
  const auto bytes=io.get_comm()-c0,rounds=io.get_rounds()-r0;
  const double ms=std::chrono::duration<double,std::milli>(t1-t0).count();

  for(int i=0;i<N;++i){
    uint64_t v=0;
    for(int k=0;k<bw;++k)
      v=(v + ((arith[size_t(i)*bw+k]<<k)&mask))&mask;
    out[i]=v;
  }

  // Regression opening after measured conversion.
  int mismatches=0;
  std::vector<uint64_t> other(N);
  if(party==ALICE){
    io.io->send_data(out.data(),int(N*8));io.io->flush();
    io.io->recv_data(other.data(),int(N*8));
  }else{
    io.io->recv_data(other.data(),int(N*8));
    io.io->send_data(out.data(),int(N*8));io.io->flush();
  }
  for(int i=0;i<N;++i){
    uint64_t got=(out[i]+other[i])&mask;
    uint64_t exp=(uint64_t(i)*7919+17)&mask;
    mismatches+=got!=exp;
  }

  std::cout<<"EXP202_RESULT party="<<party
           <<" N="<<N<<" bw="<<bw
           <<" bit_conversions="<<uint64_t(N)*uint64_t(bw)
           <<" rounds="<<rounds
           <<" bytes="<<bytes
           <<" ms="<<ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}