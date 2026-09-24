#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "GC/emp-sh2pc.h"
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;

struct PreparedRouteGC{
  FPMath& math;
  OTPack& ot;
  SemiHonestParty<NetIO>* pe=nullptr;
  PreparedRouteGC(FPMath&m,OTPack&o):math(m),ot(o){
    pe=setup_semi_honest<NetIO>(math.iopack->io_GC,math.party,128);
    auto* iknp=ot.iknp_straight;
    if(math.party==ALICE)
      static_cast<SemiHonestGen<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->s);
    else
      static_cast<SemiHonestEva<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->k1);
    // Pre-fill the COT buffer before online input arrives.
    pe->refill();
    math.iopack->io_GC->flush();
  }
  ~PreparedRouteGC(){
    delete circ_exec;delete prot_exec;
    circ_exec=nullptr;prot_exec=nullptr;
  }
  uint8_t run(const std::array<uint8_t,15>&share,uint8_t leaf_mask){
    std::vector<Bit>x;x.reserve(15);
    for(int i=0;i<15;++i){
      Bit a(math.party==ALICE?bool(share[i]):false,ALICE);
      Bit b(math.party==BOB?bool(share[i]):false,BOB);
      x.emplace_back(a^b);
    }
    auto mux=[](const Bit&s,const Bit&a,const Bit&b){return (s&(a^b))^b;};
    Bit b0=x[0];
    Bit b1=mux(b0,x[2],x[1]);
    Bit q0=mux(b1,x[4],x[3]),q1=mux(b1,x[6],x[5]);
    Bit b2=mux(b0,q1,q0);
    Bit r0=mux(b2,x[8],x[7]),r1=mux(b2,x[10],x[9]);
    Bit r2=mux(b2,x[12],x[11]),r3=mux(b2,x[14],x[13]);
    Bit s0=mux(b1,r1,r0),s1=mux(b1,r3,r2);
    Bit b3=mux(b0,s1,s0);
    std::array<Bit,4> bits={b3,b2,b1,b0};
    uint8_t out=0;
    for(int k=0;k<4;++k){
      Bit m((leaf_mask>>k)&1,ALICE);
      bool v=(bits[k]^m).reveal<bool>(BOB);
      if(math.party==BOB&&v)out|=uint8_t(1u<<k);
    }
    math.iopack->io_GC->flush();
    return out;
  }
};

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  constexpr uint8_t TRUE_LEAF=11;
  std::array<uint8_t,15> clear{},local{},peer{};
  // Force the actual tree path to leaf 1011. Non-path nodes arbitrary.
  clear.fill(0);
  clear[0]=1;   // depth0 -> right
  clear[2]=0;   // depth1 -> left
  clear[5]=1;   // depth2 -> right
  clear[12]=1;  // depth3 -> right
  for(int i=0;i<15;++i)if(i!=0&&i!=2&&i!=5&&i!=12)clear[i]=uint8_t((i*7+3)&1);

  uint8_t mask=0;
  if(party==ALICE){
    rng.random_data(local.data(),15);
    rng.random_data(&mask,1);mask&=15;
    for(int i=0;i<15;++i){local[i]&=1;peer[i]=clear[i]^local[i];}
    io.io->send_data(peer.data(),15);io.io->flush();
  }else io.io->recv_data(local.data(),15);

  auto prep_b0=io.get_comm(),prep_r0=io.get_rounds();auto prep_t0=Clock::now();
  PreparedRouteGC prepared(math,ot);
  auto prep_ms=std::chrono::duration<double,std::milli>(Clock::now()-prep_t0).count();
  auto prep_bytes=io.get_comm()-prep_b0,prep_rounds=io.get_rounds()-prep_r0;

  io.io->sync();
  auto b0=io.get_comm(),r0=io.get_rounds();auto t0=Clock::now();
  uint8_t masked=prepared.run(local,mask);
  io.io->flush();io.io_rev->flush();io.io_GC->flush();
  auto ms=std::chrono::duration<double,std::milli>(Clock::now()-t0).count();
  auto bytes=io.get_comm()-b0,rounds=io.get_rounds()-r0;

  int mismatches=0;
  if(party==BOB){io.io->send_data(&masked,1);io.io->flush();}
  else{
    uint8_t got=0;io.io->recv_data(&got,1);
    mismatches+=int(((got^mask)&15)!=TRUE_LEAF);
  }
  std::cout<<"EXP220_RESULT party="<<party
           <<" prep_bytes="<<prep_bytes<<" prep_rounds="<<prep_rounds<<" prep_ms="<<prep_ms<<" bytes="<<bytes<<" rounds="<<rounds<<" ms="<<ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}