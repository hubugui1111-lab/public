#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "orcompact_scatter.h"
#include "shared_controls.h"
#include "prepared_movement.h"
#include "prepared_movement24.h"
#include "prepared_msb_tree.h"
#include "prepared_shared_leaf_lookup16.h"
#include <memory>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <vector>
#include <algorithm>

using namespace sci;
using Clock = std::chrono::steady_clock;
using namespace shared_residual;

namespace {
constexpr int N=3072, PADN=4096, CAP=320;
constexpr int DEPTH=4, INTERNAL=(1<<DEPTH)-1, LEAVES=1<<DEPTH;
constexpr int ELL=24, QELL=46, COUNTELL=13;
constexpr uint64_t MASK=(1ULL<<ELL)-1, QMASK=(1ULL<<QELL)-1, CMASK=(1ULL<<COUNTELL)-1;
constexpr int TARGET_LEAF=11, A=2048, BOUND=2*A;

struct Phase { uint64_t bytes=0,rounds=0; double ms=0; };
struct SortStage { std::vector<int> a,b; std::vector<uint8_t> swap_share; };

void flush_all(IOPack& io){ io.io->flush(); io.io_rev->flush(); io.io_GC->flush(); }
template<class F> Phase measure(IOPack& io,F&& f){
  io.io->sync(); auto b=io.get_comm(),r=io.get_rounds(); auto t=Clock::now();
  f(); flush_all(io); auto e=Clock::now();
  return {io.get_comm()-b,io.get_rounds()-r,std::chrono::duration<double,std::milli>(e-t).count()};
}
uint64_t enc_signed(int64_t x,int ell){ return uint64_t(x)&((uint64_t(1)<<ell)-1); }
int64_t dec_signed(uint64_t x,int ell){
  const uint64_t mod=uint64_t(1)<<ell, hi=uint64_t(1)<<(ell-1); x&=mod-1;
  return (x&hi)?int64_t(x)-int64_t(mod):int64_t(x);
}
uint8_t pred_bit(int leaf,int i){
  uint32_t x=uint32_t(leaf+1)*0x9e3779b9U ^ uint32_t(i+17)*0x85ebca6bU;
  x^=x>>16; x*=0x7feb352dU; x^=x>>15; x*=0x846ca68bU; x^=x>>16; return uint8_t(x&1);
}
bool flip_for_unresolved(int i){ return ((uint32_t(i)*2654435761U+17U)%10000U)<550U; }
int path_internal_node(int leaf,int depth){
  int node=0; for(int d=0;d<depth;++d){int bit=(leaf>>(DEPTH-1-d))&1; node=2*node+1+bit;} return node;
}
uint8_t target_branch(int leaf,int depth){ return uint8_t((leaf>>(DEPTH-1-depth))&1); }

BoolArray make_leaf_onehot(FPMath& math,const BoolArray& probe_sign){
  BoolArray cur(math.party,2); cur.data[1]=probe_sign.data[0];
  cur.data[0]=probe_sign.data[0]^uint8_t(math.party==ALICE);
  int offset=1;
  for(int depth=1;depth<DEPTH;++depth){
    int m=1<<depth; BoolArray branch(math.party,m);
    for(int j=0;j<m;++j) branch.data[j]=probe_sign.data[offset+j];
    auto right=math.bool_op->AND(cur,branch);
    BoolArray next(math.party,2*m);
    for(int j=0;j<m;++j){ next.data[2*j]=cur.data[j]^right.data[j]; next.data[2*j+1]=right.data[j]; }
    cur=std::move(next); offset+=m;
  }
  return cur;
}

std::vector<SortStage> bitonic_compact(FPMath& math,BoolArray& marks,std::vector<uint64_t>& wires){
  std::vector<SortStage> stages;
  for(int k=2;k<=PADN;k<<=1){
    for(int j=k>>1;j>0;j>>=1){
      SortStage st;
      for(int i=0;i<PADN;++i){ int p=i^j; if(p>i){ st.a.push_back(i); st.b.push_back(p); } }
      const int C=int(st.a.size());
      BoolArray l(math.party,C),r(math.party,C);
      FixArray va(math.party,C,true,ELL,0),vb(math.party,C,true,ELL,0);
      for(int c=0;c<C;++c){
        int i=st.a[c],p=st.b[c]; bool desc=((i&k)==0);
        uint8_t mi=marks.data[i],mp=marks.data[p],one=uint8_t(math.party==ALICE);
        if(desc){ l.data[c]=mi^one; r.data[c]=mp; }
        else { l.data[c]=mi; r.data[c]=mp^one; }
        va.data[c]=wires[i]; vb.data[c]=wires[p];
      }
      auto sw=math.bool_op->AND(l,r);
      auto na=math.fix->if_else(sw,vb,va);
      auto nb=math.fix->if_else(sw,va,vb);
      st.swap_share.assign(sw.data,sw.data+C);
      for(int c=0;c<C;++c){
        int i=st.a[c],p=st.b[c];
        marks.data[i]^=sw.data[c]; marks.data[p]^=sw.data[c];
        wires[i]=na.data[c]; wires[p]=nb.data[c];
      }
      stages.push_back(std::move(st));
    }
  }
  return stages;
}

void reverse_compact(FPMath& math,const std::vector<SortStage>& stages,std::vector<uint64_t>& wires){
  for(auto it=stages.rbegin();it!=stages.rend();++it){
    const auto& st=*it; const int C=int(st.a.size());
    BoolArray sw(math.party,C); FixArray va(math.party,C,true,ELL,0),vb(math.party,C,true,ELL,0);
    for(int c=0;c<C;++c){ sw.data[c]=st.swap_share[c]; va.data[c]=wires[st.a[c]]; vb.data[c]=wires[st.b[c]]; }
    auto na=math.fix->if_else(sw,vb,va);
    auto nb=math.fix->if_else(sw,va,vb);
    for(int c=0;c<C;++c){ wires[st.a[c]]=na.data[c]; wires[st.b[c]]=nb.data[c]; }
  }
}
FixArray native_relu(FPMath& math,const FixArray& x){
  auto sign=math.fix->GE(x,uint64_t(0));
  return math.fix->if_else(sign,x,uint64_t(0));
}
void print_phase(const char* name,int party,const Phase&p){
  std::cout<<"EXP198_PHASE party="<<party<<" name="<<name<<" bytes="<<p.bytes<<" rounds="<<p.rounds<<" ms="<<p.ms<<"\n";
}
}

int main(int argc,char**argv){
  int party=0,port=32000; std::string address="127.0.0.1";
  ArgMapping amap; amap.arg("r",party,"role"); amap.arg("p",port,"port"); amap.arg("ip",address,"ip"); amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB) return 2;
  IOPack io(party,port,address); OTPack ot(&io,party); FPMath math(party,&io,&ot); PRG128 rng;

  std::vector<uint64_t> clear_bounds;
  std::vector<uint8_t> clear_signs;
  if(party==ALICE){
    clear_bounds.resize(size_t(LEAVES)*N);
    clear_signs.resize(size_t(LEAVES)*N);
    for(int l=0;l<LEAVES;++l) for(int i=0;i<N;++i){
      clear_bounds[size_t(l)*N+i]=uint64_t(BOUND);
      clear_signs[size_t(l)*N+i]=pred_bit(l,i);
    }
  }

  const auto leafprep_b0=io.get_comm(),leafprep_r0=io.get_rounds(); auto leafprep_t0=Clock::now();
  auto leaf_lookup=std::make_unique<exp198::PreparedSharedLeafLookup16>(
    math,rng,N,ELL,clear_bounds,clear_signs);
  flush_all(io);
  const Phase ph_leaf_preprocess{io.get_comm()-leafprep_b0,io.get_rounds()-leafprep_r0,
    std::chrono::duration<double,std::milli>(Clock::now()-leafprep_t0).count()};

  // Input-independent one-use preprocessing for the private ORCompact backend.
  h0_orcompact::Plan plan=h0_orcompact::Plan::full_prefix(N,CAP);
  PreparedMovement movement(plan,1);
  BoolArray dummy_marks(party,N); std::fill(dummy_marks.data,dummy_marks.data+N,0);
  Prefix dummy_counts{log2ceil(unsigned(N)+1)+1,std::vector<uint64_t>(N+1,0)};
  uint64_t control_ands=0;
  compile(math,plan,dummy_marks,dummy_counts,true,3,true,&control_ands);
  const auto prep_b0=io.get_comm(),prep_r0=io.get_rounds(); auto prep_t0=Clock::now();
  BatchedAnd engine(math,rng,4,true,4096);
  engine.reserve(control_ands); engine.prepare_words();
  PreparedMovement24 movement_tape(math,rng,plan.switch_count());
  flush_all(io);
  const Phase ph_preprocess{io.get_comm()-prep_b0,io.get_rounds()-prep_r0,
    std::chrono::duration<double,std::milli>(Clock::now()-prep_t0).count()};

  std::vector<uint64_t> z_local(N),z_peer(N),z_clear(N);
  if(party==ALICE){
    for(int i=0;i<N;++i){
      bool pos=pred_bit(TARGET_LEAF,i)!=0; if(flip_for_unresolved(i)) pos=!pos;
      int mag=1+((i*7919)%1000); z_clear[i]=enc_signed(pos?mag:-mag,ELL);
    }
    for(int d=0;d<DEPTH;++d){
      int node=path_internal_node(TARGET_LEAF,d); bool pos=target_branch(TARGET_LEAF,d)!=0;
      z_clear[node]=enc_signed(pos?(101+d):-(101+d),ELL);
    }
    rng.random_data(z_local.data(),N*8);
    for(int i=0;i<N;++i){ z_local[i]&=MASK; z_peer[i]=(z_clear[i]-z_local[i])&MASK; }
    io.io->send_data(z_peer.data(),N*8); io.io->flush();
  }else io.io->recv_data(z_local.data(),N*8);
  FixArray z(party,N,true,ELL,0); std::copy(z_local.begin(),z_local.end(),z.data);

  const auto total_b0=io.get_comm(), total_r0=io.get_rounds(); auto total_t0=Clock::now();

  FixArray probe_z(party,INTERNAL,true,ELL,0); for(int j=0;j<INTERNAL;++j) probe_z.data[j]=z.data[j];
  BoolArray probe_sign; auto ph_probe=measure(io,[&]{probe_sign=math.fix->GE(probe_z,uint64_t(0));});

  BoolArray leaf_onehot; auto ph_route=measure(io,[&]{leaf_onehot=make_leaf_onehot(math,probe_sign);});

  const uint8_t leaf_index_share=exp198::leaf_index_share_from_onehot(leaf_onehot);
  exp198::LeafLookupResult leaf_result;
  FixArray bound(party,N,true,ELL,0);
  BoolArray pred_pos(party,N);
  auto ph_leaf=measure(io,[&]{
    leaf_result=leaf_lookup->query(leaf_index_share);
    std::copy(leaf_result.bound_shares.begin(),leaf_result.bound_shares.end(),bound.data);
    std::copy(leaf_result.sign_shares.begin(),leaf_result.sign_shares.end(),pred_pos.data);
  });

  FixArray negz(party,N,true,ELL,0);
  for(int i=0;i<N;++i) negz.data[i]=(-z.data[i])&MASK;
  FixArray aligned;
  auto ph_align=measure(io,[&]{aligned=math.fix->if_else(pred_pos,z,negz);});

  // Exact certificate: 0 < s*z < 2a. Evaluate both comparisons in one 2N batch.
  FixArray lhs(party,2*N,true,ELL,0),rhs(party,2*N,true,ELL,0);
  for(int i=0;i<N;++i){
    lhs.data[i]=0; rhs.data[i]=aligned.data[i];
    lhs.data[N+i]=aligned.data[i]; rhs.data[N+i]=bound.data[i];
  }
  BoolArray cert;
  auto ph_cert=measure(io,[&]{
    auto cmp=math.fix->LT(lhs,rhs);
    BoolArray lo(party,N),hi(party,N);
    for(int i=0;i<N;++i){lo.data[i]=cmp.data[i];hi.data[i]=cmp.data[N+i];}
    cert=math.bool_op->AND(lo,hi);
  });

  FixArray predz;
  auto ph_predout=measure(io,[&]{predz=math.fix->if_else(pred_pos,z,uint64_t(0));});

  BoolArray marks(party,N);
  for(int i=0;i<N;++i) marks.data[i]=cert.data[i]^uint8_t(party==ALICE);
  bool accepted=false;
  Phase ph_count{};

  FixArray final_out(party,N,true,ELL,0);
  Phase ph_controls{},ph_mask{},ph_gather{},ph_tail{},ph_scatter{},ph_merge{},ph_overflow{};
  Prefix counts{};
  // Recompute the prefix object for control compilation; same secret marks, no opening.
  auto ph_count2=measure(io,[&]{
    counts=prefix(math,marks);
    accepted=shared_residual::accepted(math,counts,CAP);
  });
  // ph_count above is superseded by this canonical count/decision phase.
  ph_count=ph_count2;

  if(accepted){
    std::vector<uint8_t> controls;
    ph_controls=measure(io,[&]{
      AndScope scope(&engine);
      controls=compile(math,plan,marks,counts,true,3,true);
      movement_tape.bind(controls);
    });

    FixArray unresolved_z;
    ph_mask=measure(io,[&]{unresolved_z=math.fix->if_else(marks,z,uint64_t(0));});

    std::vector<uint64_t> packed;
    ph_gather=measure(io,[&]{
      packed=movement.run(movement_tape,
        std::vector<uint64_t>(unresolved_z.data,unresolved_z.data+N),ELL,true);
    });

    std::vector<uint64_t> tail_compact(CAP,0);
    ph_tail=measure(io,[&]{
      FixArray tx(party,CAP,true,ELL,0);
      std::copy(packed.begin(),packed.end(),tx.data);
      auto y=native_relu(math,tx);
      std::copy(y.data,y.data+CAP,tail_compact.begin());
    });

    std::vector<uint64_t> scattered;
    ph_scatter=measure(io,[&]{
      scattered=movement.run(movement_tape,tail_compact,ELL,false);
    });
    if(!movement_tape.exhausted()) return 7;

    ph_merge=measure(io,[&]{
      FixArray cand(party,N,true,ELL,0);
      for(int i=0;i<N;++i)cand.data[i]=predz.data[i]&MASK;
      auto known=math.fix->if_else(cert,cand,uint64_t(0));
      for(int i=0;i<N;++i)final_out.data[i]=(known.data[i]+scattered[i])&MASK;
    });
  }else{
    ph_overflow=measure(io,[&]{final_out=native_relu(math,z);});
  }
  flush_all(io);
  auto total_t1=Clock::now();
  const uint64_t total_bytes=io.get_comm()-total_b0,total_rounds=io.get_rounds()-total_r0;
  const double total_ms=std::chrono::duration<double,std::milli>(total_t1-total_t0).count();

  FixArray baseline;
  auto ph_full=measure(io,[&]{baseline=native_relu(math,z);});

  auto pub_final=math.fix->output(PUBLIC,final_out);
  auto pub_full=math.fix->output(PUBLIC,baseline);
  auto pub_cert=math.bool_op->output(PUBLIC,cert);
  auto pub_leaf=math.bool_op->output(PUBLIC,leaf_onehot);
  int mismatches=0,cert_count=0,expected_cert=0,leaf=-1,onehot=0;
  for(int i=0;i<N;++i){
    cert_count+=pub_cert.data[i];
    mismatches+=((pub_final.data[i]&MASK)!=(pub_full.data[i]&MASK));
    if(party==ALICE){
      const bool pp=pred_bit(TARGET_LEAF,i)!=0;
      const int64_t zc=dec_signed(z_clear[i],ELL);
      const int64_t x=pp?zc:-zc;
      const bool exp=(x>0 && x<BOUND);
      expected_cert+=exp;
      mismatches+=int(bool(pub_cert.data[i])!=exp);
    }
  }
  for(int l=0;l<LEAVES;++l){onehot+=pub_leaf.data[l];if(pub_leaf.data[l])leaf=l;}
  mismatches+=(leaf!=TARGET_LEAF)+(onehot!=1);

  print_phase("probe15",party,ph_probe); print_phase("secret_route",party,ph_route);
  print_phase("leaf_lookup_preprocess",party,ph_leaf_preprocess);
  print_phase("leaf_param_lookup",party,ph_leaf); print_phase("certificate_align",party,ph_align);
  print_phase("certificate_interval_compare",party,ph_cert); print_phase("certified_output_select",party,ph_predout);
  print_phase("preprocess_orcompact",party,ph_preprocess);
  print_phase("secret_count_accept",party,ph_count); print_phase("private_controls",party,ph_controls);
  print_phase("mask_unresolved_payload",party,ph_mask);
  print_phase("private_compaction_gather",party,ph_gather);
  print_phase("native_tail_relu",party,ph_tail); print_phase("private_compaction_scatter",party,ph_scatter);
  print_phase("merge",party,ph_merge); print_phase("overflow_full_relu",party,ph_overflow);
  print_phase("full_relu_baseline",party,ph_full);

  std::cout<<"EXP198_RESULT party="<<party<<" N="<<N<<" capacity="<<CAP
           <<" leaf_preprocess_bytes="<<ph_leaf_preprocess.bytes<<" leaf_preprocess_rounds="<<ph_leaf_preprocess.rounds<<" leaf_preprocess_ms="<<ph_leaf_preprocess.ms
           <<" preprocess_bytes="<<ph_preprocess.bytes<<" preprocess_rounds="<<ph_preprocess.rounds<<" preprocess_ms="<<ph_preprocess.ms
           <<" accepted="<<(accepted?1:0)<<" cert_count="<<cert_count<<" expected_cert="<<expected_cert
           <<" cert_fraction="<<(double(cert_count)/N)
           <<" total_bytes="<<total_bytes<<" total_rounds="<<total_rounds<<" total_ms="<<total_ms
           <<" full_relu_bytes="<<ph_full.bytes<<" full_relu_rounds="<<ph_full.rounds<<" full_relu_ms="<<ph_full.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}