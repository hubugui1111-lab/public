#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <array>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace sci;
using Clock=std::chrono::steady_clock;
constexpr int N=3072,Q=15,BLOCK=256,BLOCKS=12;
struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
template<class F> Phase measure(IOPack&io,F&&f){
  auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();io.io->flush();io.io_rev->flush();
  return {io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}
int main(int argc,char**argv){
  int party=0,port=32190;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");
  amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  IOPack io(party,port,ip);PRG128 rng;
  SplitKKOT<NetIO> rev16(3-party,io.io_rev,16),rev256(3-party,io.io_rev,256);
  rev16.set_precomp_batch_size(Q*BLOCK);rev256.set_precomp_batch_size(Q);
  auto prep=measure(io,[&]{rev16.preprocess();rev256.preprocess();});

  std::array<uint16_t,Q> idx{};
  if(party==ALICE){
    for(int j=0;j<Q;++j)idx[j]=uint16_t((j*197+53)%N);
  }
  std::vector<uint64_t> clear(N),local(N),peer(N);
  if(party==ALICE){
    for(int i=0;i<N;++i)clear[i]=0x1234567800000000ULL+uint64_t(i)*0x10101ULL;
    rng.random_data(local.data(),N*8);
    for(int i=0;i<N;++i)peer[i]=clear[i]-local[i];
    io.io->send_data(peer.data(),N*8);io.io->flush();
  }else io.io->recv_data(local.data(),N*8);

  // Align both parties after one-use preprocessing so component timing does
  // not accidentally include the other process's preprocessing skew.
  io.io->sync();
  const auto total_b0=io.get_comm(),total_r0=io.get_rounds();
  const auto total_t0=Clock::now();
  std::vector<uint64_t> s1out(Q*BLOCK),r1(Q*BLOCK);
  std::vector<uint8_t> hi(Q*BLOCK);
  std::vector<std::vector<uint64_t>> s1msg;
  std::vector<uint64_t*> s1ptr;
  if(party==ALICE){
    for(int q=0;q<Q;++q)for(int l=0;l<BLOCK;++l)hi[q*BLOCK+l]=uint8_t(idx[q]>>8);
  }else{
    s1msg.assign(Q*BLOCK,std::vector<uint64_t>(16));
    s1ptr.resize(Q*BLOCK);
    rng.random_data(r1.data(),r1.size()*8);
    for(int q=0;q<Q;++q)for(int l=0;l<BLOCK;++l){
      int o=q*BLOCK+l;s1ptr[o]=s1msg[o].data();
      for(int h=0;h<16;++h){
        s1msg[o][h]=(h<BLOCKS)?local[h*BLOCK+l]+r1[o]:r1[o]^uint64_t(h*0x9e3779b9U);
      }
    }
  }
  auto online1=measure(io,[&]{
    if(party==BOB)rev16.send(s1ptr.data(),Q*BLOCK,64);
    else rev16.recv(s1out.data(),hi.data(),Q*BLOCK,64);
  });

  std::array<uint64_t,Q> tq{},s2out{},gather{};
  std::array<uint8_t,Q> lo{};
  std::vector<std::vector<uint64_t>> s2msg;
  std::vector<uint64_t*> s2ptr;
  if(party==ALICE){for(int q=0;q<Q;++q)lo[q]=uint8_t(idx[q]&255);}
  else{
    rng.random_data(tq.data(),Q*8);
    s2msg.assign(Q,std::vector<uint64_t>(256));s2ptr.resize(Q);
    for(int q=0;q<Q;++q){s2ptr[q]=s2msg[q].data();
      for(int l=0;l<256;++l)s2msg[q][l]=uint64_t(0)-r1[q*BLOCK+l]+tq[q];
    }
  }
  auto online2=measure(io,[&]{
    if(party==BOB)rev256.send(s2ptr.data(),Q,64);
    else rev256.recv(s2out.data(),lo.data(),Q,64);
  });
  if(party==ALICE){
    for(int q=0;q<Q;++q)gather[q]=local[idx[q]]+s1out[q*BLOCK+lo[q]]+s2out[q];
  }else{
    for(int q=0;q<Q;++q)gather[q]=uint64_t(0)-tq[q];
  }
  io.io->flush();io.io_rev->flush();
  const Phase total_online{
    io.get_comm()-total_b0,io.get_rounds()-total_r0,
    std::chrono::duration<double,std::milli>(Clock::now()-total_t0).count()};

  std::array<uint64_t,Q> other{},opened{};
  if(party==ALICE){io.io->send_data(gather.data(),Q*8);io.io->flush();io.io->recv_data(other.data(),Q*8);}
  else{io.io->recv_data(other.data(),Q*8);io.io->send_data(gather.data(),Q*8);io.io->flush();}
  int mism=0;
  if(party==ALICE)for(int q=0;q<Q;++q){opened[q]=gather[q]+other[q];mism+=opened[q]!=clear[idx[q]];}
  std::cout<<"EXP250_GATHER party="<<party<<" prep_ms="<<prep.ms<<" prep_bytes="<<prep.bytes
    <<" wire_only_ms="<<(online1.ms+online2.ms)<<" wire_only_bytes="<<(online1.bytes+online2.bytes)
    <<" wire_only_rounds="<<(online1.rounds+online2.rounds)
    <<" total_online_ms="<<total_online.ms<<" total_online_bytes="<<total_online.bytes
    <<" total_online_rounds="<<total_online.rounds<<" mismatches="<<mism<<"\n";
  return mism?3:0;
}