#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "Millionaire/bit-triple-generator.h"
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <vector>

using namespace sci;
using Clock=std::chrono::steady_clock;
constexpr int N=3072;

struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F>Phase measure(IOPack&io,F&&f){
  io.io->sync();auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush(io);return{io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(Clock::now()-t).count()};
}

struct BoolTripleBatch{
  std::vector<uint8_t>a,b,c;
  Phase prep;
};

BoolTripleBatch prepare_triples(IOPack&io,OTPack&ot,int party,int n){
  BoolTripleBatch out;
  out.a.resize(n);out.b.resize(n);out.c.resize(n);
  TripleGenerator gen(party,&io,&ot);
  auto t=measure(io,[&]{
    gen.generate(party,out.a.data(),out.b.data(),out.c.data(),
                 n,_16KKOT_to_4OT,false,1);
  });
  out.prep=t;
  return out;
}

BoolArray beaver_and(IOPack&io,int party,const BoolArray&x,const BoolArray&y,
                     const uint8_t*a,const uint8_t*b,const uint8_t*c){
  if(x.size!=y.size)throw std::runtime_error("size");
  const int n=x.size;
  std::vector<uint8_t> mine(size_t(2)*n),peer(size_t(2)*n);
  for(int i=0;i<n;++i){
    mine[i]=(x.data[i]^a[i])&1;
    mine[n+i]=(y.data[i]^b[i])&1;
  }
  if(party==ALICE){
    io.io->send_data(mine.data(),2*n);io.io->flush();
    io.io->recv_data(peer.data(),2*n);
  }else{
    io.io->recv_data(peer.data(),2*n);
    io.io->send_data(mine.data(),2*n);io.io->flush();
  }
  BoolArray z(party,n);
  for(int i=0;i<n;++i){
    const uint8_t d=(mine[i]^peer[i])&1;
    const uint8_t e=(mine[n+i]^peer[n+i])&1;
    z.data[i]=(c[i]^(d&b[i])^(e&a[i])^((party==ALICE)?(d&e):0))&1;
  }
  return z;
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  auto triples=prepare_triples(io,ot,party,2*N);

  std::vector<uint8_t> local(3*N),peer(3*N),clear(3*N);
  if(party==ALICE){
    std::vector<uint64_t>r(3*N);rng.random_data(r.data(),r.size()*8);
    for(int i=0;i<3*N;++i){
      clear[i]=uint8_t((i*17+5)&1);local[i]=uint8_t(r[i]&1);peer[i]=clear[i]^local[i];
    }
    io.io->send_data(peer.data(),3*N);io.io->flush();
  }else io.io->recv_data(local.data(),3*N);
  BoolArray lo(party,N),hi(party,N),pred(party,N);
  for(int i=0;i<N;++i){lo.data[i]=local[i];hi.data[i]=local[N+i];pred.data[i]=local[2*N+i];}

  BoolArray cert_b,safe_b;
  auto online=measure(io,[&]{
    cert_b=beaver_and(io,party,lo,hi,triples.a.data(),triples.b.data(),triples.c.data());
    safe_b=beaver_and(io,party,cert_b,pred,
      triples.a.data()+N,triples.b.data()+N,triples.c.data()+N);
  });

  BoolArray cert_sci,safe_sci;
  auto baseline=measure(io,[&]{
    cert_sci=math.bool_op->AND(lo,hi);
    safe_sci=math.bool_op->AND(cert_sci,pred);
  });

  auto pc=math.bool_op->output(PUBLIC,cert_b),ps=math.bool_op->output(PUBLIC,safe_b);
  auto pc2=math.bool_op->output(PUBLIC,cert_sci),ps2=math.bool_op->output(PUBLIC,safe_sci);
  int mismatches=0;
  if(party==ALICE)for(int i=0;i<N;++i){
    const bool C=clear[i]&clear[N+i],S=C&clear[2*N+i];
    mismatches+=int(bool(pc.data[i])!=C)+int(bool(ps.data[i])!=S);
    mismatches+=int(bool(pc2.data[i])!=C)+int(bool(ps2.data[i])!=S);
  }

  std::cout<<"EXP209_RESULT party="<<party
           <<" prep_bytes="<<triples.prep.bytes<<" prep_rounds="<<triples.prep.rounds<<" prep_ms="<<triples.prep.ms
           <<" online_bytes="<<online.bytes<<" online_rounds="<<online.rounds<<" online_ms="<<online.ms
           <<" sci_bytes="<<baseline.bytes<<" sci_rounds="<<baseline.rounds<<" sci_ms="<<baseline.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}