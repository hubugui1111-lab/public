#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "GC/emp-sh2pc.h"
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;
constexpr int N=3072;

struct P{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>P measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}

void gc_logic(FPMath&math,OTPack&ot,const BoolArray&lo,const BoolArray&hi,
              const BoolArray&pred,BoolArray&cert,BoolArray&safe){
  auto* pe=setup_semi_honest<NetIO>(math.iopack->io_GC,math.party,8192);
  auto* iknp=ot.iknp_straight;
  if(math.party==ALICE)
    static_cast<SemiHonestGen<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->s);
  else
    static_cast<SemiHonestEva<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->k1);

  cert=BoolArray(math.party,N);safe=BoolArray(math.party,N);
  for(int i=0;i<N;++i){
    Bit loa(math.party==ALICE?bool(lo.data[i]&1):false,ALICE);
    Bit lob(math.party==BOB?bool(lo.data[i]&1):false,BOB);
    Bit hia(math.party==ALICE?bool(hi.data[i]&1):false,ALICE);
    Bit hib(math.party==BOB?bool(hi.data[i]&1):false,BOB);
    Bit pra(math.party==ALICE?bool(pred.data[i]&1):false,ALICE);
    Bit prb(math.party==BOB?bool(pred.data[i]&1):false,BOB);
    Bit L=loa^lob,H=hia^hib,R=pra^prb;
    Bit C=L&H;
    Bit S=C&R;
    cert.data[i]=uint8_t(C.reveal<bool>(XOR));
    safe.data[i]=uint8_t(S.reveal<bool>(XOR));
  }
  math.iopack->io_GC->flush();
  delete circ_exec;delete prot_exec;
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  std::vector<uint8_t> local(3*N),peer(3*N),clear(3*N);
  if(party==ALICE){
    std::vector<uint64_t>raw(3*N);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<3*N;++i){clear[i]=uint8_t((i*13+7)&1);local[i]=uint8_t(raw[i]&1);peer[i]=clear[i]^local[i];}
    io.io->send_data(peer.data(),3*N);io.io->flush();
  }else io.io->recv_data(local.data(),3*N);
  BoolArray lo(party,N),hi(party,N),pred(party,N);
  for(int i=0;i<N;++i){lo.data[i]=local[i];hi.data[i]=local[N+i];pred.data[i]=local[2*N+i];}

  BoolArray c1,s1;
  auto p1=measure(io,[&]{c1=math.bool_op->AND(lo,hi);s1=math.bool_op->AND(c1,pred);});

  BoolArray c2,s2;
  auto p2=measure(io,[&]{gc_logic(math,ot,lo,hi,pred,c2,s2);});

  // Verify after timing.
  auto pc1=math.bool_op->output(PUBLIC,c1),ps1=math.bool_op->output(PUBLIC,s1);
  auto pc2=math.bool_op->output(PUBLIC,c2),ps2=math.bool_op->output(PUBLIC,s2);
  int mismatches=0;
  if(party==ALICE)for(int i=0;i<N;++i){
    bool C=clear[i]&clear[N+i],S=C&clear[2*N+i];
    mismatches+=int(bool(pc1.data[i])!=C)+int(bool(ps1.data[i])!=S);
    mismatches+=int(bool(pc2.data[i])!=C)+int(bool(ps2.data[i])!=S);
  }
  std::cout<<"EXP208_RESULT party="<<party
           <<" sci_bytes="<<p1.bytes<<" sci_rounds="<<p1.rounds<<" sci_ms="<<p1.ms
           <<" gc_bytes="<<p2.bytes<<" gc_rounds="<<p2.rounds<<" gc_ms="<<p2.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}