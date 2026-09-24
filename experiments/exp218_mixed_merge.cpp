#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <chrono>
#include <cstdint>
#include <cstring>
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
std::vector<uint8_t> pack_bits(const std::vector<uint8_t>&v){
  std::vector<uint8_t> out((v.size()+7)/8,0);
  for(size_t i=0;i<v.size();++i)out[i>>3]|=uint8_t((v[i]&1)<<(i&7));
  return out;
}
uint8_t packed_bit(const std::vector<uint8_t>&v,int i){return uint8_t((v[i>>3]>>(i&7))&1);}

struct MixedTriple{
  BoolArray a_bool;
  FixArray a_arith,b,c;
  Phase prep;
  MixedTriple(int party):a_bool(party,N),a_arith(party,N,false,ELL,0),
                         b(party,N,true,ELL,0),c(party,N,true,ELL,0){}
};

MixedTriple prepare(IOPack&io,FPMath&math,PRG128&rng,int party){
  MixedTriple t(party);
  std::vector<uint64_t>raw(N);rng.random_data(raw.data(),raw.size()*8);
  for(int i=0;i<N;++i)t.a_bool.data[i]=uint8_t(raw[i]&1);
  t.prep=measure(io,[&]{
    t.a_arith=math.fix->B2A(t.a_bool,false,ELL);
    std::vector<uint64_t>br(N);rng.random_data(br.data(),br.size()*8);
    for(int i=0;i<N;++i)t.b.data[i]=br[i]&MASK;
    t.c=math.fix->mul(t.a_arith,t.b,ELL);
  });
  return t;
}

FixArray mixed_mul(IOPack&io,int party,const BoolArray&s,const FixArray&x,const MixedTriple&t){
  std::vector<uint64_t> e_share(N),e_peer(N),e(N);
  std::vector<uint8_t> d_share(N);
  for(int i=0;i<N;++i){
    d_share[i]=(s.data[i]^t.a_bool.data[i])&1;
    e_share[i]=(x.data[i]-t.b.data[i])&MASK;
  }
  auto pd=pack_bits(d_share);
  const size_t EBYTES=size_t(N)*sizeof(uint64_t),DBYTES=pd.size();
  std::vector<uint8_t> mine(EBYTES+DBYTES),peer(mine.size());
  std::memcpy(mine.data(),e_share.data(),EBYTES);
  std::memcpy(mine.data()+EBYTES,pd.data(),DBYTES);
  if(party==ALICE){
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()));
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
  }
  std::memcpy(e_peer.data(),peer.data(),EBYTES);
  std::vector<uint8_t> pd_peer(DBYTES);
  std::memcpy(pd_peer.data(),peer.data()+EBYTES,DBYTES);

  FixArray y(party,N,true,ELL,0);
  for(int i=0;i<N;++i){
    e[i]=(e_share[i]+e_peer[i])&MASK;
    const uint8_t d=uint8_t(d_share[i]^packed_bit(pd_peer,i));
    const uint64_t ae=(t.a_arith.data[i]*e[i])&MASK;
    if(!d)y.data[i]=(t.c.data[i]+ae)&MASK;
    else y.data[i]=(t.b.data[i]+((party==ALICE)?e[i]:0ULL)-t.c.data[i]-ae)&MASK;
  }
  return y;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  auto triple=prepare(io,math,rng,party);

  std::vector<uint64_t>xclear(N),xlocal(N),xpeer(N);
  std::vector<uint8_t>sclear(N),slocal(N),speer(N);
  if(party==ALICE){
    std::vector<uint64_t>raw(2*N);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<N;++i){
      int64_t v=int64_t((i*7919)%4095)-2047;
      xclear[i]=uint64_t(v)&MASK;
      xlocal[i]=raw[i]&MASK;xpeer[i]=(xclear[i]-xlocal[i])&MASK;
      sclear[i]=uint8_t((i*7+3)&1);slocal[i]=uint8_t(raw[N+i]&1);speer[i]=sclear[i]^slocal[i];
    }
    io.io->send_data(xpeer.data(),N*8);io.io->send_data(speer.data(),N);io.io->flush();
  }else{
    io.io->recv_data(xlocal.data(),N*8);io.io->recv_data(slocal.data(),N);
  }
  FixArray x(party,N,true,ELL,0);std::copy(xlocal.begin(),xlocal.end(),x.data);
  BoolArray s(party,N);std::copy(slocal.begin(),slocal.end(),s.data);

  FixArray y;
  auto online=measure(io,[&]{y=mixed_mul(io,party,s,x,triple);});

  FixArray base;
  auto baseline=measure(io,[&]{base=math.fix->if_else(s,x,uint64_t(0));});

  auto py=math.fix->output(PUBLIC,y),pb=math.fix->output(PUBLIC,base);
  int mismatches=0;
  for(int i=0;i<N;++i)mismatches+=int((py.data[i]&MASK)!=(pb.data[i]&MASK));

  std::cout<<"EXP218_RESULT party="<<party
           <<" prep_bytes="<<triple.prep.bytes<<" prep_rounds="<<triple.prep.rounds<<" prep_ms="<<triple.prep.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" baseline_bytes="<<baseline.bytes<<" baseline_rounds="<<baseline.rounds<<" baseline_ms="<<baseline.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}