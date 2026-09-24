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
constexpr int N=3072,ELL=24;
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

  // Public-fixture semantics, but the protocol sees only:
  // ALICE: compare flips f0/f1 and pred XOR-share pA.
  // BOB:   blinded compare bits u/v and pred XOR-share pB.
  std::vector<uint8_t> lo(N),hi(N),pred(N);
  for(int i=0;i<N;++i){
    lo[i]=uint8_t((i*7+1)&1);
    hi[i]=uint8_t((i*11+3)&1);
    pred[i]=uint8_t((i*13+5)&1);
  }
  std::vector<uint8_t> f0(N),f1(N),pA(N),u(N),v(N),pB(N);
  if(party==ALICE){
    std::vector<uint64_t> r(3*N);rng.random_data(r.data(),r.size()*8);
    for(int i=0;i<N;++i){
      f0[i]=uint8_t(r[i]&1);f1[i]=uint8_t(r[N+i]&1);pA[i]=uint8_t(r[2*N+i]&1);
      u[i]=lo[i]^f0[i];v[i]=hi[i]^f1[i];pB[i]=pred[i]^pA[i];
    }
    io.io->send_data(u.data(),N);io.io->send_data(v.data(),N);io.io->send_data(pB.data(),N);io.io->flush();
  }else{
    io.io->recv_data(u.data(),N);io.io->recv_data(v.data(),N);io.io->recv_data(pB.data(),N);
  }

  std::vector<uint64_t> mark_share(N,0),recv(N,0),randw(N);
  std::vector<uint8_t> safe_share(N,0),choices(N,0),safeA(N,0);
  std::vector<std::array<uint64_t,8>> msgs;
  std::vector<uint64_t*> ptrs;

  auto lookup=measure(io,[&]{
    if(party==ALICE){
      rng.random_data(randw.data(),N*8);
      msgs.resize(N);ptrs.resize(N);
      for(int i=0;i<N;++i){
        mark_share[i]=randw[i]&MASK;
        safeA[i]=uint8_t((randw[i]>>ELL)&1);
        safe_share[i]=safeA[i];
        for(int ch=0;ch<8;++ch){
          const uint8_t uu=uint8_t(ch&1);
          const uint8_t vv=uint8_t((ch>>1)&1);
          const uint8_t pb=uint8_t((ch>>2)&1);
          const uint8_t L=uu^f0[i],H=vv^f1[i],P=pb^pA[i];
          const uint8_t cert=L&H;
          const uint8_t mark=cert^1;
          const uint8_t safe=cert&P;
          const uint64_t mb=(uint64_t(mark)-mark_share[i])&MASK;
          const uint64_t sb=uint64_t(safe^safeA[i]);
          msgs[i][ch]=mb|(sb<<ELL);
        }
        ptrs[i]=msgs[i].data();
      }
      ot.kkot[2]->send(ptrs.data(),N,ELL+1);
    }else{
      for(int i=0;i<N;++i)choices[i]=uint8_t(u[i]|(v[i]<<1)|(pB[i]<<2));
      ot.kkot[2]->recv(recv.data(),choices.data(),N,ELL+1);
      for(int i=0;i<N;++i){
        mark_share[i]=recv[i]&MASK;
        safe_share[i]=uint8_t((recv[i]>>ELL)&1);
      }
    }
  });

  // Baseline current-style: secret-shared comparison outputs, two ANDs and B2A mark.
  BoolArray blo(party,N),bhi(party,N),bp(party,N);
  std::vector<uint8_t> peer0(N),peer1(N),peerp(N),l0(N),l1(N),lp(N);
  if(party==ALICE){
    std::vector<uint64_t> r(3*N);rng.random_data(r.data(),r.size()*8);
    for(int i=0;i<N;++i){
      l0[i]=uint8_t(r[i]&1);l1[i]=uint8_t(r[N+i]&1);lp[i]=uint8_t(r[2*N+i]&1);
      peer0[i]=lo[i]^l0[i];peer1[i]=hi[i]^l1[i];peerp[i]=pred[i]^lp[i];
    }
    io.io->send_data(peer0.data(),N);io.io->send_data(peer1.data(),N);io.io->send_data(peerp.data(),N);io.io->flush();
  }else{
    io.io->recv_data(l0.data(),N);io.io->recv_data(l1.data(),N);io.io->recv_data(lp.data(),N);
  }
  for(int i=0;i<N;++i){blo.data[i]=l0[i];bhi.data[i]=l1[i];bp.data[i]=lp[i];}
  BoolArray cert,safe,marks;FixArray marks_a;
  auto base=measure(io,[&]{
    cert=math.bool_op->AND(blo,bhi);
    safe=math.bool_op->AND(cert,bp);
    marks=math.bool_op->NOT(cert);
    marks_a=math.fix->B2A(marks,false,ELL);
  });

  // Verify lookup outputs.
  std::vector<uint64_t> other_mark(N);std::vector<uint8_t> other_safe(N);
  if(party==ALICE){
    io.io->send_data(mark_share.data(),N*8);io.io->send_data(safe_share.data(),N);io.io->flush();
    io.io->recv_data(other_mark.data(),N*8);io.io->recv_data(other_safe.data(),N);
  }else{
    io.io->recv_data(other_mark.data(),N*8);io.io->recv_data(other_safe.data(),N);
    io.io->send_data(mark_share.data(),N*8);io.io->send_data(safe_share.data(),N);io.io->flush();
  }
  int mismatches=0;
  for(int i=0;i<N;++i){
    const uint8_t C=lo[i]&hi[i],M=C^1,S=C&pred[i];
    const uint64_t gotM=(mark_share[i]+other_mark[i])&MASK;
    const uint8_t gotS=safe_share[i]^other_safe[i];
    mismatches+=int(gotM!=M)+int(gotS!=S);
  }

  std::cout<<"EXP210_RESULT party="<<party
           <<" lookup_bytes="<<lookup.bytes<<" lookup_rounds="<<lookup.rounds<<" lookup_ms="<<lookup.ms
           <<" baseline_bytes="<<base.bytes<<" baseline_rounds="<<base.rounds<<" baseline_ms="<<base.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}