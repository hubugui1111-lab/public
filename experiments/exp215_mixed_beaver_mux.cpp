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
constexpr int N=3072,ELL=24;
constexpr uint64_t MASK=(1ULL<<ELL)-1;
struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}

struct MuxTriple{
  BoolArray a_xor;
  FixArray a_add,b,c;
  Phase prep;
  MuxTriple(int party,int n):a_xor(party,n),a_add(party,n,false,ELL,0),
    b(party,n,true,ELL,0),c(party,n,true,ELL,0){}
};

MuxTriple prepare_mux_triple(FPMath&math,IOPack&io,PRG128&rng,int party,int n){
  MuxTriple t(party,n);
  std::vector<uint64_t>raw(size_t(2)*n);rng.random_data(raw.data(),raw.size()*8);
  for(int i=0;i<n;++i){
    t.a_xor.data[i]=uint8_t(raw[i]&1);
    t.b.data[i]=raw[n+i]&MASK;
  }
  t.prep=measure(io,[&]{
    t.a_add=math.fix->B2A(t.a_xor,false,ELL);
    t.c=math.fix->if_else(t.a_xor,t.b,uint64_t(0));
  });
  return t;
}

FixArray beaver_mux(IOPack&io,int party,const BoolArray&s,const FixArray&x,
                    const MuxTriple&t){
  const int n=x.size;if(s.size!=n||t.a_xor.size!=n)throw std::runtime_error("size");
  std::vector<uint8_t> emine(n),epeer(n);
  std::vector<uint64_t> dmine(n),dpeer(n);
  for(int i=0;i<n;++i){
    emine[i]=(s.data[i]^t.a_xor.data[i])&1;
    dmine[i]=(x.data[i]-t.b.data[i])&MASK;
  }
  if(party==ALICE){
    io.io->send_data(emine.data(),n);io.io->send_data(dmine.data(),n*8);io.io->flush();
    io.io->recv_data(epeer.data(),n);io.io->recv_data(dpeer.data(),n*8);
  }else{
    io.io->recv_data(epeer.data(),n);io.io->recv_data(dpeer.data(),n*8);
    io.io->send_data(emine.data(),n);io.io->send_data(dmine.data(),n*8);io.io->flush();
  }
  FixArray y(party,n,true,ELL,0);
  for(int i=0;i<n;++i){
    const uint8_t e=(emine[i]^epeer[i])&1;
    const uint64_t d=(dmine[i]+dpeer[i])&MASK;
    const uint64_t ax=(t.c.data[i]+t.a_add.data[i]*d)&MASK;
    y.data[i]=e ? ((x.data[i]-ax)&MASK) : ax;
  }
  return y;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  auto t1=prepare_mux_triple(math,io,rng,party,N);
  auto t2=prepare_mux_triple(math,io,rng,party,N);

  std::vector<uint64_t>xclear(N),xlocal(N),xpeer(N),raw(size_t(3)*N);
  std::vector<uint8_t>s1c(N),s2c(N),s1l(N),s2l(N),s1p(N),s2p(N);
  if(party==ALICE){
    rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<N;++i){
      int64_t v=int64_t((i*7919)%4095)-2047;xclear[i]=uint64_t(v)&MASK;
      xlocal[i]=raw[i]&MASK;xpeer[i]=(xclear[i]-xlocal[i])&MASK;
      s1c[i]=uint8_t((i*7+3)&1);s2c[i]=uint8_t((i*11+5)&1);
      s1l[i]=uint8_t(raw[N+i]&1);s1p[i]=s1c[i]^s1l[i];
      s2l[i]=uint8_t(raw[2*N+i]&1);s2p[i]=s2c[i]^s2l[i];
    }
    io.io->send_data(xpeer.data(),N*8);io.io->send_data(s1p.data(),N);io.io->send_data(s2p.data(),N);io.io->flush();
  }else{
    io.io->recv_data(xlocal.data(),N*8);io.io->recv_data(s1l.data(),N);io.io->recv_data(s2l.data(),N);
  }
  FixArray x(party,N,true,ELL,0);std::copy(xlocal.begin(),xlocal.end(),x.data);
  BoolArray s1(party,N),s2(party,N);std::copy(s1l.begin(),s1l.end(),s1.data);std::copy(s2l.begin(),s2l.end(),s2.data);

  FixArray y1,y2;
  auto online=measure(io,[&]{y1=beaver_mux(io,party,s1,x,t1);y2=beaver_mux(io,party,s2,x,t2);});

  FixArray b1,b2;
  auto base=measure(io,[&]{b1=math.fix->if_else(s1,x,uint64_t(0));b2=math.fix->if_else(s2,x,uint64_t(0));});

  auto py1=math.fix->output(PUBLIC,y1),py2=math.fix->output(PUBLIC,y2);
  auto pb1=math.fix->output(PUBLIC,b1),pb2=math.fix->output(PUBLIC,b2);
  int mismatches=0;
  for(int i=0;i<N;++i){
    mismatches+=int((py1.data[i]&MASK)!=(pb1.data[i]&MASK));
    mismatches+=int((py2.data[i]&MASK)!=(pb2.data[i]&MASK));
  }
  std::cout<<"EXP215_RESULT party="<<party
           <<" prep_bytes="<<(t1.prep.bytes+t2.prep.bytes)
           <<" prep_rounds="<<(t1.prep.rounds+t2.prep.rounds)
           <<" prep_ms="<<(t1.prep.ms+t2.prep.ms)
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" baseline_bytes="<<base.bytes<<" baseline_rounds="<<base.rounds<<" baseline_ms="<<base.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}