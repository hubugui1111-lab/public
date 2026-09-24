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
constexpr int N1=3072,N2=320,ELL=24;
constexpr uint64_t MASK=(1ULL<<ELL)-1;
struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}
std::vector<uint8_t> pack_bits(const std::vector<uint8_t>&v){
  std::vector<uint8_t> out((v.size()+7)/8,0);
  for(size_t i=0;i<v.size();++i)out[i>>3]|=uint8_t((v[i]&1)<<(i&7));
  return out;
}
void xor_unpack(std::vector<uint8_t>&dst,const std::vector<uint8_t>&peer){
  for(size_t i=0;i<dst.size();++i)dst[i]^=uint8_t((peer[i>>3]>>(i&7))&1);
}
FixArray dabit_b2a(IOPack&io,int party,const BoolArray&x,
                   const BoolArray&a_bool,const FixArray&a_arith){
  const int n=x.size;
  std::vector<uint8_t>d(n);
  for(int i=0;i<n;++i)d[i]=(x.data[i]^a_bool.data[i])&1;
  auto mine=pack_bits(d);
  std::vector<uint8_t> peer(mine.size());
  if(party==ALICE){
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()));
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
  }
  xor_unpack(d,peer);
  FixArray y(party,n,false,ELL,0);
  for(int i=0;i<n;++i){
    if(!d[i])y.data[i]=a_arith.data[i]&MASK;
    else y.data[i]=(((party==ALICE)?1ULL:0ULL)-a_arith.data[i])&MASK;
  }
  return y;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  // Offline daBits: same random global bits represented in XOR and Z_2^ELL additive sharing.
  BoolArray a_all(party,N1+N2);
  std::vector<uint64_t>raw(N1+N2);rng.random_data(raw.data(),raw.size()*8);
  for(int i=0;i<N1+N2;++i)a_all.data[i]=uint8_t(raw[i]&1);
  FixArray aa_all;
  auto prep=measure(io,[&]{aa_all=math.fix->B2A(a_all,false,ELL);});

  BoolArray a1(party,N1),a2(party,N2);
  FixArray aa1(party,N1,false,ELL,0),aa2(party,N2,false,ELL,0);
  for(int i=0;i<N1;++i){a1.data[i]=a_all.data[i];aa1.data[i]=aa_all.data[i];}
  for(int i=0;i<N2;++i){a2.data[i]=a_all.data[N1+i];aa2.data[i]=aa_all.data[N1+i];}

  // Independent test inputs as XOR shares.
  std::vector<uint8_t>x1l(N1),x2l(N2),peer1(N1),peer2(N2),clear1(N1),clear2(N2);
  if(party==ALICE){
    std::vector<uint64_t>rr(N1+N2);rng.random_data(rr.data(),rr.size()*8);
    for(int i=0;i<N1;++i){clear1[i]=uint8_t((i*7+1)&1);x1l[i]=uint8_t(rr[i]&1);peer1[i]=clear1[i]^x1l[i];}
    for(int i=0;i<N2;++i){clear2[i]=uint8_t((i*11+3)&1);x2l[i]=uint8_t(rr[N1+i]&1);peer2[i]=clear2[i]^x2l[i];}
    io.io->send_data(peer1.data(),N1);io.io->send_data(peer2.data(),N2);io.io->flush();
  }else{
    io.io->recv_data(x1l.data(),N1);io.io->recv_data(x2l.data(),N2);
  }
  BoolArray x1(party,N1),x2(party,N2);
  std::copy(x1l.begin(),x1l.end(),x1.data);std::copy(x2l.begin(),x2l.end(),x2.data);

  FixArray y1,y2;
  auto online=measure(io,[&]{
    y1=dabit_b2a(io,party,x1,a1,aa1);
    y2=dabit_b2a(io,party,x2,a2,aa2);
  });

  FixArray b1,b2;
  auto base=measure(io,[&]{b1=math.fix->B2A(x1,false,ELL);b2=math.fix->B2A(x2,false,ELL);});

  auto py1=math.fix->output(PUBLIC,y1),py2=math.fix->output(PUBLIC,y2);
  auto pb1=math.fix->output(PUBLIC,b1),pb2=math.fix->output(PUBLIC,b2);
  int mismatches=0;
  for(int i=0;i<N1;++i)mismatches+=int((py1.data[i]&MASK)!=(pb1.data[i]&MASK));
  for(int i=0;i<N2;++i)mismatches+=int((py2.data[i]&MASK)!=(pb2.data[i]&MASK));

  std::cout<<"EXP217_RESULT party="<<party
           <<" prep_bytes="<<prep.bytes<<" prep_rounds="<<prep.rounds<<" prep_ms="<<prep.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" baseline_bytes="<<base.bytes<<" baseline_rounds="<<base.rounds<<" baseline_ms="<<base.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}