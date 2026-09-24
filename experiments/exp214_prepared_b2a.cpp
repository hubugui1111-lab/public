#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
#include <array>
#include <algorithm>

using namespace sci;
using Clock=std::chrono::steady_clock;
namespace {
constexpr int N1=3072,N2=320,ELL=24;
constexpr uint64_t MASK=(1ULL<<ELL)-1;
struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}

FixArray prepared_b2a(IOPack&io,OTPack&ot,PRG128&rng,int party,const BoolArray&x){
  const int n=x.size;
  FixArray y(party,n,false,ELL,0);
  if(party==ALICE){
    std::vector<uint64_t> r(n),raw(n);rng.random_data(raw.data(),size_t(n)*8);
    std::vector<std::array<uint64_t,2>> msgs(n);std::vector<uint64_t*> ptrs(n);
    for(int i=0;i<n;++i){
      r[i]=raw[i]&MASK;
      const uint64_t corr=(-2ULL*uint64_t(x.data[i]&1))&MASK;
      msgs[i][0]=r[i];msgs[i][1]=(r[i]+corr)&MASK;ptrs[i]=msgs[i].data();
      y.data[i]=(uint64_t(x.data[i]&1)-r[i])&MASK;
    }
    ot.iknp_straight->send(ptrs.data(),n,ELL);
  }else{
    std::vector<uint64_t> recv(n);
    ot.iknp_straight->recv(recv.data(),x.data,n,ELL);
    for(int i=0;i<n;++i)y.data[i]=(uint64_t(x.data[i]&1)+recv[i])&MASK;
  }
  return y;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  ot.iknp_straight->set_precomp_batch_size(N1+N2);
  auto prep=measure(io,[&]{ot.iknp_straight->preprocess();});

  std::vector<uint8_t>a1(N1),a2(N2),p1(N1),p2(N2),c1(N1),c2(N2);
  if(party==ALICE){
    std::vector<uint64_t>raw(N1+N2);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<N1;++i){c1[i]=uint8_t((i*7+1)&1);a1[i]=uint8_t(raw[i]&1);p1[i]=c1[i]^a1[i];}
    for(int i=0;i<N2;++i){c2[i]=uint8_t((i*11+3)&1);a2[i]=uint8_t(raw[N1+i]&1);p2[i]=c2[i]^a2[i];}
    io.io->send_data(p1.data(),N1);io.io->send_data(p2.data(),N2);io.io->flush();
  }else{
    io.io->recv_data(a1.data(),N1);io.io->recv_data(a2.data(),N2);
  }
  BoolArray b1(party,N1),b2(party,N2);
  std::copy(a1.begin(),a1.end(),b1.data);std::copy(a2.begin(),a2.end(),b2.data);

  FixArray y1,y2;
  auto online=measure(io,[&]{y1=prepared_b2a(io,ot,rng,party,b1);y2=prepared_b2a(io,ot,rng,party,b2);});

  FixArray z1,z2;
  auto base=measure(io,[&]{z1=math.fix->B2A(b1,false,ELL);z2=math.fix->B2A(b2,false,ELL);});

  auto py1=math.fix->output(PUBLIC,y1),py2=math.fix->output(PUBLIC,y2);
  auto pz1=math.fix->output(PUBLIC,z1),pz2=math.fix->output(PUBLIC,z2);
  int mismatches=0;
  for(int i=0;i<N1;++i)mismatches+=int((py1.data[i]&MASK)!=(pz1.data[i]&MASK));
  for(int i=0;i<N2;++i)mismatches+=int((py2.data[i]&MASK)!=(pz2.data[i]&MASK));

  std::cout<<"EXP214_RESULT party="<<party
           <<" prep_bytes="<<prep.bytes<<" prep_rounds="<<prep.rounds<<" prep_ms="<<prep.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" baseline_bytes="<<base.bytes<<" baseline_rounds="<<base.rounds<<" baseline_ms="<<base.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}