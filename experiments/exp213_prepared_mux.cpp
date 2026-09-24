#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
#include <algorithm>
#include <omp.h>

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

FixArray prepared_mux(IOPack&io,OTPack&ot,PRG128&rng,int party,
                      const BoolArray&sel,const FixArray&x){
  if(sel.size!=x.size||x.ell!=ELL)throw std::runtime_error("mux invariant");
  const int n=x.size;
  std::vector<uint64_t> corr(n),send_mask(n),recv_val(n),out(n),raw(n);
  rng.random_data(raw.data(),size_t(n)*8);
  for(int i=0;i<n;++i){
    const uint64_t ss=uint64_t(sel.data[i]&1);
    corr[i]=(x.data[i]*(1ULL-2ULL*ss))&MASK;
    send_mask[i]=raw[i]&MASK;
  }

  std::vector<std::array<uint64_t,2>> messages(n);
  std::vector<uint64_t*> ptrs(n);
  for(int i=0;i<n;++i){
    messages[i][0]=send_mask[i];
    messages[i][1]=(send_mask[i]+corr[i])&MASK;
    ptrs[i]=messages[i].data();
  }

#pragma omp parallel num_threads(2)
  {
    if(omp_get_thread_num()==0){
      if(party==ALICE)
        ot.iknp_straight->send(ptrs.data(),n,ELL);
      else
        ot.iknp_straight->recv(recv_val.data(),sel.data,n,ELL);
    }else{
      if(party==BOB)
        ot.iknp_reversed->send(ptrs.data(),n,ELL);
      else
        ot.iknp_reversed->recv(recv_val.data(),sel.data,n,ELL);
    }
  }

  for(int i=0;i<n;++i)
    out[i]=(x.data[i]*uint64_t(sel.data[i]&1)+recv_val[i]-send_mask[i])&MASK;

  FixArray y(party,n,true,ELL,0);
  std::copy(out.begin(),out.end(),y.data);
  return y;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  // Prepare enough random OTs for two N-element mux calls, both directions.
  const int BATCH=2*N;
  ot.iknp_straight->set_precomp_batch_size(BATCH);
  ot.iknp_reversed->set_precomp_batch_size(BATCH);
  auto prep=measure(io,[&]{
#pragma omp parallel num_threads(2)
    {
      if(omp_get_thread_num()==0)ot.iknp_straight->preprocess();
      else ot.iknp_reversed->preprocess();
    }
  });

  std::vector<uint64_t>xclear(N),xlocal(N),xpeer(N);
  std::vector<uint8_t>s1clear(N),s2clear(N),s1local(N),s2local(N),s1peer(N),s2peer(N);
  if(party==ALICE){
    std::vector<uint64_t>raw(size_t(3)*N);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<N;++i){
      int64_t v=int64_t((i*7919)%4095)-2047;
      xclear[i]=uint64_t(v)&MASK;
      xlocal[i]=raw[i]&MASK;xpeer[i]=(xclear[i]-xlocal[i])&MASK;
      s1clear[i]=uint8_t((i*7+3)&1);s2clear[i]=uint8_t((i*11+5)&1);
      s1local[i]=uint8_t(raw[N+i]&1);s1peer[i]=s1clear[i]^s1local[i];
      s2local[i]=uint8_t(raw[2*N+i]&1);s2peer[i]=s2clear[i]^s2local[i];
    }
    io.io->send_data(xpeer.data(),N*8);
    io.io->send_data(s1peer.data(),N);io.io->send_data(s2peer.data(),N);io.io->flush();
  }else{
    io.io->recv_data(xlocal.data(),N*8);
    io.io->recv_data(s1local.data(),N);io.io->recv_data(s2local.data(),N);
  }
  FixArray x(party,N,true,ELL,0);std::copy(xlocal.begin(),xlocal.end(),x.data);
  BoolArray s1(party,N),s2(party,N);
  std::copy(s1local.begin(),s1local.end(),s1.data);
  std::copy(s2local.begin(),s2local.end(),s2.data);

  FixArray p1,p2;
  auto online=measure(io,[&]{
    p1=prepared_mux(io,ot,rng,party,s1,x);
    p2=prepared_mux(io,ot,rng,party,s2,x);
  });

  FixArray b1,b2;
  auto baseline=measure(io,[&]{
    b1=math.fix->if_else(s1,x,uint64_t(0));
    b2=math.fix->if_else(s2,x,uint64_t(0));
  });

  auto op1=math.fix->output(PUBLIC,p1),op2=math.fix->output(PUBLIC,p2);
  auto ob1=math.fix->output(PUBLIC,b1),ob2=math.fix->output(PUBLIC,b2);
  int mismatches=0;
  for(int i=0;i<N;++i){
    mismatches+=((op1.data[i]&MASK)!=(ob1.data[i]&MASK));
    mismatches+=((op2.data[i]&MASK)!=(ob2.data[i]&MASK));
  }

  std::cout<<"EXP213_RESULT party="<<party
           <<" prep_bytes="<<prep.bytes<<" prep_rounds="<<prep.rounds<<" prep_ms="<<prep.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" baseline_bytes="<<baseline.bytes<<" baseline_rounds="<<baseline.rounds<<" baseline_ms="<<baseline.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}