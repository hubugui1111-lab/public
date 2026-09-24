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
using Clock = std::chrono::steady_clock;

namespace {
constexpr int N = 3072;
constexpr int DEPTH = 4;
constexpr int INTERNAL = (1<<DEPTH)-1; // 15
constexpr int LEAVES = 1<<DEPTH;       // 16
constexpr int ELL = 24;
constexpr int QELL = 46;
constexpr uint64_t MASK = (1ULL<<ELL)-1;
constexpr uint64_t QMASK = (1ULL<<QELL)-1;
constexpr int TARGET_LEAF = 11;
constexpr int A = 2048;
constexpr int BETA_MAG = 2*A; // beta=-2*s*a

struct Phase {
  uint64_t bytes=0, rounds=0;
  double ms=0;
};

void flush_all(IOPack& io){
  io.io->flush(); io.io_rev->flush(); io.io_GC->flush();
}
template<class F>
Phase measure(IOPack& io, F&& f){
  io.io->sync();
  auto b=io.get_comm(), r=io.get_rounds();
  auto t=Clock::now();
  f();
  flush_all(io);
  auto e=Clock::now();
  return {io.get_comm()-b, io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(e-t).count()};
}
uint64_t enc_signed(int64_t x,int ell){
  const uint64_t m=(ell==64)?~uint64_t(0):((uint64_t(1)<<ell)-1);
  return uint64_t(x)&m;
}
int64_t dec_signed(uint64_t x,int ell){
  const uint64_t mod=uint64_t(1)<<ell, hi=uint64_t(1)<<(ell-1);
  x&=mod-1;
  return (x&hi)?int64_t(x)-int64_t(mod):int64_t(x);
}
uint8_t pred_bit(int leaf,int i){
  uint32_t x=uint32_t(leaf+1)*0x9e3779b9U ^ uint32_t(i+17)*0x85ebca6bU;
  x^=x>>16; x*=0x7feb352dU; x^=x>>15; x*=0x846ca68bU; x^=x>>16;
  return uint8_t(x&1);
}
bool flip_for_unresolved(int i){
  // deterministic ~5.5%, independent of leaf/probe routing
  return ((uint32_t(i)*2654435761U + 17U) % 10000U) < 550U;
}
int path_internal_node(int leaf,int depth){
  // heap node reached before taking branch at depth
  int node=0;
  for(int d=0; d<depth; ++d){
    int bit=(leaf>>(DEPTH-1-d))&1;
    node = 2*node + 1 + bit;
  }
  return node;
}
uint8_t target_branch(int leaf,int depth){
  return uint8_t((leaf>>(DEPTH-1-depth))&1);
}

BoolArray make_leaf_onehot(FPMath& math,const BoolArray& probe_sign){
  // probe_sign[j] is the sign bit of heap internal node j.
  BoolArray cur(math.party,2);
  cur.data[1]=probe_sign.data[0];
  cur.data[0]=probe_sign.data[0]^uint8_t(math.party==ALICE);
  int offset=1;
  for(int depth=1; depth<DEPTH; ++depth){
    const int m=1<<depth;
    BoolArray branch(math.party,m);
    for(int j=0;j<m;++j) branch.data[j]=probe_sign.data[offset+j];
    auto right=math.bool_op->AND(cur,branch); // one batched AND round per level
    BoolArray next(math.party,2*m);
    for(int j=0;j<m;++j){
      next.data[2*j]=cur.data[j]^right.data[j];
      next.data[2*j+1]=right.data[j];
    }
    cur=std::move(next);
    offset+=m;
  }
  return cur;
}

void print_phase(const char* name,int party,const Phase& p){
  std::cout<<"EXP194_PHASE party="<<party<<" name="<<name
           <<" bytes="<<p.bytes<<" rounds="<<p.rounds<<" ms="<<p.ms<<"\n";
}
}

int main(int argc,char**argv){
  int party=0,port=32000;
  std::string address="127.0.0.1";
  ArgMapping amap;
  amap.arg("r",party,"role");
  amap.arg("p",port,"port");
  amap.arg("ip",address,"ip");
  amap.parse(argc,argv);
  if(party!=ALICE && party!=BOB) return 2;

  IOPack io(party,port,address);
  OTPack ot(&io,party);
  FPMath math(party,&io,&ot);
  PRG128 rng;

  // Model-fixed leaf payloads: beta_i=-2*s_i*a and p_i=1{s_i=+1}.
  // They are installed before the query and never opened to the client.
  const int ROW = 2*N;
  std::vector<uint64_t> param_clear(LEAVES*ROW,0);
  if(party==ALICE){
    for(int l=0;l<LEAVES;++l){
      for(int i=0;i<N;++i){
        const bool pos=pred_bit(l,i)!=0;
        const int64_t beta=pos ? -BETA_MAG : BETA_MAG;
        param_clear[l*ROW+i]=enc_signed(beta,ELL);
        param_clear[l*ROW+N+i]=pos?1:0;
      }
    }
  }
  auto params=math.fix->input(ALICE,LEAVES*ROW,param_clear.data(),true,ELL,0);
  flush_all(io);

  // Fresh query is secret-shared only after model payload is fixed.
  std::vector<uint64_t> z_local(N),z_peer(N),z_clear(N);
  if(party==ALICE){
    // Construct a query whose activation state routes to TARGET_LEAF.
    for(int i=0;i<N;++i){
      bool pos=pred_bit(TARGET_LEAF,i)!=0;
      if(flip_for_unresolved(i)) pos=!pos;
      int mag=1+((i*7919)%1000);
      int64_t v=pos?mag:-mag;
      z_clear[i]=enc_signed(v,ELL);
    }
    // Force every internal-node probe on the target path to take the target branch.
    for(int d=0;d<DEPTH;++d){
      const int node=path_internal_node(TARGET_LEAF,d);
      const bool pos=target_branch(TARGET_LEAF,d)!=0;
      const int mag=101+d;
      z_clear[node]=enc_signed(pos?mag:-mag,ELL);
    }
    rng.random_data(z_local.data(),N*sizeof(uint64_t));
    for(int i=0;i<N;++i){
      z_local[i]&=MASK;
      z_peer[i]=(z_clear[i]-z_local[i])&MASK;
    }
    io.io->send_data(z_peer.data(),int(N*sizeof(uint64_t))); io.io->flush();
  } else {
    io.io->recv_data(z_local.data(),int(N*sizeof(uint64_t)));
  }
  FixArray z(party,N,true,ELL,0);
  std::copy(z_local.begin(),z_local.end(),z.data);

  // A. Data-oblivious probe comparisons: all 15 possible depth-4 tree nodes.
  FixArray probe_z(party,INTERNAL,true,ELL,0);
  for(int j=0;j<INTERNAL;++j) probe_z.data[j]=z.data[j];
  BoolArray probe_sign;
  auto ph_probe=measure(io,[&]{ probe_sign=math.fix->GE(probe_z,uint64_t(0)); });

  // B. Secret tree routing. No path/leaf is opened.
  BoolArray leaf_onehot;
  auto ph_route=measure(io,[&]{ leaf_onehot=make_leaf_onehot(math,probe_sign); });

  // C. Secret leaf payload selection, one batched mux over 16*2N values.
  BoolArray cond(party,LEAVES*ROW);
  for(int l=0;l<LEAVES;++l)
    for(int j=0;j<ROW;++j)
      cond.data[l*ROW+j]=leaf_onehot.data[l];
  FixArray masked_params;
  auto ph_leaf=measure(io,[&]{ masked_params=math.fix->if_else(cond,params,uint64_t(0)); });

  FixArray beta(party,N,true,ELL,0), pred_pos_arith(party,N,true,ELL,0);
  for(int i=0;i<N;++i){
    uint64_t b=0,p=0;
    for(int l=0;l<LEAVES;++l){
      b=(b+masked_params.data[l*ROW+i])&MASK;
      p=(p+masked_params.data[l*ROW+N+i])&MASK;
    }
    beta.data[i]=b; pred_pos_arith.data[i]=p;
  }

  // D. Exact integer singleton certificate:
  // q_i = z_i^2 + beta_i*z_i = z_i^2 - 2*s_i*a*z_i.
  // q_i < 0  iff  0 < s_i*z_i < 2a.
  FixArray X(party,2*N,true,ELL,0),Y(party,2*N,true,ELL,0),prod;
  for(int i=0;i<N;++i){
    X.data[i]=z.data[i]; Y.data[i]=z.data[i];
    X.data[N+i]=beta.data[i]; Y.data[N+i]=z.data[i];
  }
  FixArray q(party,N,true,QELL,0);
  auto ph_arith=measure(io,[&]{
    prod=math.fix->mul(X,Y,QELL);
    for(int i=0;i<N;++i) q.data[i]=(prod.data[i]+prod.data[N+i])&QMASK;
  });

  BoolArray cert;
  auto ph_cert=measure(io,[&]{ cert=math.fix->LT(q,uint64_t(0)); });

  // E. Certified output value p_i*z_i (still secret). This is the value used
  // whenever cert_i=1; unresolved coordinates must go to the private tail.
  FixArray predz;
  auto ph_predout=measure(io,[&]{ predz=math.fix->mul(pred_pos_arith,z,QELL); });

  // Matched baseline full ReLU for all 3072 coordinates.
  FixArray baseline;
  auto ph_full=measure(io,[&]{
    auto s=math.fix->GE(z,uint64_t(0));
    baseline=math.fix->if_else(s,z,uint64_t(0));
  });

  // Regression openings are strictly after all timed protocol phases.
  auto pub_leaf=math.bool_op->output(PUBLIC,leaf_onehot);
  auto pub_beta=math.fix->output(PUBLIC,beta);
  auto pub_p=math.fix->output(PUBLIC,pred_pos_arith);
  auto pub_cert=math.bool_op->output(PUBLIC,cert);
  auto pub_predz=math.fix->output(PUBLIC,predz);
  auto pub_full=math.fix->output(PUBLIC,baseline);

  int leaf=-1,onehot_weight=0,mismatches=0,cert_count=0;
  for(int l=0;l<LEAVES;++l){ if(pub_leaf.data[l]) leaf=l; onehot_weight+=pub_leaf.data[l]; }
  mismatches += (leaf!=TARGET_LEAF) + (onehot_weight!=1);
  int expected_cert=0;
  for(int i=0;i<N;++i){
    const bool pp=pred_bit(TARGET_LEAF,i)!=0;
    const int64_t zc=party==ALICE?dec_signed(z_clear[i],ELL):0;
    if(party==ALICE){
      const int64_t exp_beta=pp?-BETA_MAG:BETA_MAG;
      mismatches += (dec_signed(pub_beta.data[i],ELL)!=exp_beta);
      mismatches += (pub_p.data[i]!=(pp?1:0));
      const int64_t x=pp?zc:-zc;
      const bool c=(x>0 && x<2*A);
      expected_cert+=c;
      cert_count+=pub_cert.data[i];
      mismatches += (bool(pub_cert.data[i])!=c);
      const uint64_t exp_pred=c ? (pp?z_clear[i]:0) : (pp?z_clear[i]:0);
      (void)exp_pred;
      const uint64_t exp_pz=pp?enc_signed(zc,QELL):0;
      mismatches += ((pub_predz.data[i]&QMASK)!=(exp_pz&QMASK));
      const uint64_t exp_relu=zc>0?z_clear[i]:0;
      mismatches += ((pub_full.data[i]&MASK)!=(exp_relu&MASK));
    }
  }

  print_phase("probe15",party,ph_probe);
  print_phase("secret_route",party,ph_route);
  print_phase("leaf_param_select",party,ph_leaf);
  print_phase("certificate_arithmetic",party,ph_arith);
  print_phase("certificate_secure_compare",party,ph_cert);
  print_phase("certified_output_mul",party,ph_predout);
  print_phase("full_relu_baseline",party,ph_full);

  const uint64_t ours_bytes=ph_probe.bytes+ph_route.bytes+ph_leaf.bytes+
      ph_arith.bytes+ph_cert.bytes+ph_predout.bytes;
  const uint64_t ours_rounds=ph_probe.rounds+ph_route.rounds+ph_leaf.rounds+
      ph_arith.rounds+ph_cert.rounds+ph_predout.rounds;
  const double ours_ms=ph_probe.ms+ph_route.ms+ph_leaf.ms+
      ph_arith.ms+ph_cert.ms+ph_predout.ms;

  std::cout<<"EXP194_RESULT party="<<party
           <<" N="<<N<<" internal_probes="<<INTERNAL<<" leaves="<<LEAVES
           <<" target_leaf="<<TARGET_LEAF
           <<" cert_count="<<cert_count
           <<" cert_fraction="<<(double(cert_count)/N)
           <<" expected_cert="<<expected_cert
           <<" pre_tail_bytes="<<ours_bytes
           <<" pre_tail_rounds="<<ours_rounds
           <<" pre_tail_ms="<<ours_ms
           <<" full_relu_bytes="<<ph_full.bytes
           <<" full_relu_rounds="<<ph_full.rounds
           <<" full_relu_ms="<<ph_full.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}
