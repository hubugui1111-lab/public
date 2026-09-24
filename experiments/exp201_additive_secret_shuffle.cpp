#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include <seal/seal.h>
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>

using namespace sci;
using namespace seal;
using Clock=std::chrono::steady_clock;

namespace {
constexpr int N=3072, CAP=320, M=N+CAP, ELL=24;
constexpr uint32_t RMASK=(1u<<ELL)-1;

struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush_all(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F> Phase measure(IOPack&io,F&&f){
  io.io->sync(); auto b=io.get_comm(),r=io.get_rounds(); auto t=Clock::now();
  f();flush_all(io);auto e=Clock::now();
  return {io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(e-t).count()};
}
FixArray native_relu(FPMath&math,const FixArray&x){
  auto sign=math.fix->GE(x,uint64_t(0));
  return math.fix->if_else(sign,x,uint64_t(0));
}
uint32_t add24(uint32_t a,uint32_t b){return (a+b)&RMASK;}
uint32_t sub24(uint32_t a,uint32_t b){return (a-b)&RMASK;}

std::vector<uint32_t> random_perm(int n,PRG128&rng){
  std::vector<uint32_t> p(n);std::iota(p.begin(),p.end(),0);
  std::vector<uint64_t> r(n);rng.random_data(r.data(),n*8);
  for(int i=0;i<n;++i){int j=i+int(r[i]%uint64_t(n-i));std::swap(p[i],p[j]);}
  return p;
}
std::vector<uint32_t> inv_perm(const std::vector<uint32_t>&p){
  std::vector<uint32_t> q(p.size());
  for(size_t i=0;i<p.size();++i)q[p[i]]=uint32_t(i);
  return q;
}
void send_blob(NetIO*io,const std::string&s){
  uint64_t n=s.size();io->send_data(&n,8);io->send_data(s.data(),int(n));io->flush();
}
std::string recv_blob(NetIO*io){
  uint64_t n=0;io->recv_data(&n,8);std::string s(n,'\0');io->recv_data(s.data(),int(n));return s;
}
template<class T> std::string save_obj(const T&x){
  std::stringstream ss(std::ios::in|std::ios::out|std::ios::binary);x.save(ss);return ss.str();
}
template<class T> T load_obj(const SEALContext&ctx,const std::string&s){
  T x;std::stringstream ss(s,std::ios::in|std::ios::binary);x.load(ctx,ss);return x;
}

struct HEState{
  EncryptionParameters parms;
  SEALContext ctx;
  BatchEncoder encoder;
  KeyGenerator keygen;
  SecretKey sk;
  GaloisKeys gk_local,gk_peer;
  Evaluator eval;
  Encryptor enc;
  Decryptor dec;
  size_t slots,row;
  uint64_t plain_mod;
  HEState():parms(scheme_type::bfv),
    ctx([&]{
      parms.set_poly_modulus_degree(8192);
      parms.set_coeff_modulus(CoeffModulus::BFVDefault(8192));
      parms.set_plain_modulus(PlainModulus::Batching(8192,40));
      return SEALContext(parms);
    }()),
    encoder(ctx),keygen(ctx),sk(keygen.secret_key()),
    eval(ctx),enc(ctx,sk),dec(ctx,sk){
      keygen.create_galois_keys(gk_local);
      slots=encoder.slot_count();row=slots/2;plain_mod=parms.plain_modulus().value();
      if(row<4096||M>int(row))throw std::runtime_error("slot invariant");
  }
};

void exchange_galois(IOPack&io,int party,HEState&he){
  auto blob=save_obj(he.gk_local);
  std::string peer;
  if(party==ALICE){send_blob(io.io,blob);peer=recv_blob(io.io);}
  else{peer=recv_blob(io.io);send_blob(io.io,blob);}
  he.gk_peer=load_obj<GaloisKeys>(he.ctx,peer);
}

Plaintext encode_cols(HEState&he,const std::vector<uint32_t>&v,int cols){
  std::vector<uint64_t> slots(he.slots,0);
  if(int(v.size())!=M*cols)throw std::runtime_error("encode size");
  for(int i=0;i<M;++i){
    slots[i]=v[size_t(i)*cols];
    if(cols==2)slots[he.row+i]=v[size_t(i)*cols+1];
  }
  Plaintext p;he.encoder.encode(slots,p);return p;
}

std::vector<uint32_t> decode_cols(HEState&he,const Plaintext&p,int cols){
  std::vector<uint64_t> slots;he.encoder.decode(p,slots);
  std::vector<uint32_t> v(size_t(M)*cols);
  const int64_t half=int64_t(he.plain_mod/2);
  for(int i=0;i<M;++i){
    auto cv=[&](uint64_t x){
      int64_t s=x>uint64_t(half)?int64_t(x)-int64_t(he.plain_mod):int64_t(x);
      return uint32_t(uint64_t(s)&RMASK);
    };
    v[size_t(i)*cols]=cv(slots[i]);
    if(cols==2)v[size_t(i)*cols+1]=cv(slots[he.row+i]);
  }
  return v;
}

// out[i] = in[p[i]], for first M positions of both BFV rows.
Ciphertext he_permute(HEState&he,const Ciphertext&ct,
                      const std::vector<uint32_t>&p,int cols){
  std::map<int,std::vector<int>> by_shift;
  const int R=int(he.row);
  for(int i=0;i<M;++i){
    int s=(int(p[i])-i)%R;if(s<0)s+=R;
    by_shift[s].push_back(i);
  }
  Ciphertext acc;bool first=true;
  for(auto&kv:by_shift){
    Ciphertext tmp;
    if(kv.first==0)tmp=ct;
    else he.eval.rotate_rows(ct,kv.first,he.gk_peer,tmp);
    std::vector<uint64_t> mask(he.slots,0);
    for(int i:kv.second){
      mask[i]=1;
      if(cols==2)mask[he.row+i]=1;
    }
    Plaintext pm;he.encoder.encode(mask,pm);
    he.eval.multiply_plain_inplace(tmp,pm);
    if(first){acc=std::move(tmp);first=false;}
    else he.eval.add_inplace(acc,tmp);
  }
  return acc;
}

struct OwnerCorr{std::vector<uint32_t> delta;};
struct RecvCorr{std::vector<uint32_t> A,B;};
struct CorrPair{OwnerCorr owner;RecvCorr recv;};

struct PreparedPerm{
  std::vector<uint32_t> p;
  CorrPair fwd,inv;
};

std::vector<uint32_t> rand_ring(PRG128&rng,int n){
  std::vector<uint32_t> v(n);std::vector<uint64_t> r(n);
  rng.random_data(r.data(),n*8);for(int i=0;i<n;++i)v[i]=uint32_t(r[i])&RMASK;
  return v;
}

void receiver_send_A(IOPack&io,int party,HEState&he,PRG128&rng,int cols,
                     RecvCorr&rc,Ciphertext&sent){
  rc.A=rand_ring(rng,M*cols);
  Plaintext pa=encode_cols(he,rc.A,cols);
  he.enc.encrypt_symmetric(pa,sent);
  send_blob(io.io,save_obj(sent));
}
void owner_process_A(IOPack&io,HEState&he,PRG128&rng,
                     const std::vector<uint32_t>&p,int cols,OwnerCorr&oc){
  auto blob=recv_blob(io.io);
  auto ct=load_obj<Ciphertext>(he.ctx,blob);
  auto pct=he_permute(he,ct,p,cols);
  oc.delta=rand_ring(rng,M*cols);
  Plaintext pd=encode_cols(he,oc.delta,cols);
  he.eval.sub_plain_inplace(pct,pd);
  send_blob(io.io,save_obj(pct));
}
void receiver_recv_B(IOPack&io,HEState&he,int cols,RecvCorr&rc){
  auto blob=recv_blob(io.io);
  auto ct=load_obj<Ciphertext>(he.ctx,blob);
  Plaintext pb;he.dec.decrypt(ct,pb);
  rc.B=decode_cols(he,pb,cols);
}

// Secure input-independent correlation generation for one owner's permutation.
// ownerParty knows p and Delta; receiver knows A,B with Delta+B=p(A).
void generate_corr_set(IOPack&io,int party,HEState&he,PRG128&rng,
                       int ownerParty,const std::vector<uint32_t>&p,
                       CorrPair&fwd,CorrPair&inv){
  if(party==ownerParty){
    owner_process_A(io,he,rng,p,2,fwd.owner);
    owner_process_A(io,he,rng,p,1,inv.owner);
  }else{
    Ciphertext c0,c1;
    receiver_send_A(io,party,he,rng,2,fwd.recv,c0);
    receiver_recv_B(io,he,2,fwd.recv);
    receiver_send_A(io,party,he,rng,1,inv.recv,c1);
    receiver_recv_B(io,he,1,inv.recv);
  }
}

// One-message regular application. Input/output flat [M][cols].
std::vector<uint32_t> apply_regular(IOPack&io,int party,int ownerParty,
 const std::vector<uint32_t>&p,const CorrPair&corr,
 const std::vector<uint32_t>&in,int cols){
  std::vector<uint32_t> out(size_t(M)*cols),msg(size_t(M)*cols);
  if(party!=ownerParty){
    for(size_t i=0;i<msg.size();++i)msg[i]=sub24(in[i],corr.recv.A[i]);
    io.io->send_data(msg.data(),int(msg.size()*4));io.io->flush();
    out=corr.recv.B;
  }else{
    io.io->recv_data(msg.data(),int(msg.size()*4));
    for(int i=0;i<M;++i)for(int c=0;c<cols;++c){
      size_t d=size_t(i)*cols+c,s=size_t(p[i])*cols+c;
      out[d]=add24(add24(in[s],msg[s]),corr.owner.delta[d]);
    }
  }
  return out;
}

// One-message inverse application, p^{-1}.
std::vector<uint32_t> apply_inverse(IOPack&io,int party,int ownerParty,
 const std::vector<uint32_t>&p,const CorrPair&corr,
 const std::vector<uint32_t>&in,int cols){
  std::vector<uint32_t> out(size_t(M)*cols),msg(size_t(M)*cols);
  if(party!=ownerParty){
    for(size_t i=0;i<msg.size();++i)msg[i]=sub24(in[i],corr.recv.B[i]);
    io.io->send_data(msg.data(),int(msg.size()*4));io.io->flush();
    out=corr.recv.A;
  }else{
    auto pinv=inv_perm(p);
    io.io->recv_data(msg.data(),int(msg.size()*4));
    for(int i=0;i<M;++i)for(int c=0;c<cols;++c){
      size_t d=size_t(i)*cols+c,s=size_t(pinv[i])*cols+c;
      // p^{-1}(in + msg - Delta)
      out[d]=sub24(add24(in[s],msg[s]),corr.owner.delta[s]);
    }
  }
  return out;
}

std::vector<uint32_t> share_clear(IOPack&io,int party,PRG128&rng,
 const std::vector<uint32_t>&clear){
  std::vector<uint32_t> local(clear.size()),peer(clear.size());
  if(party==ALICE){
    auto r=rand_ring(rng,int(clear.size()));local=r;
    for(size_t i=0;i<clear.size();++i)peer[i]=sub24(clear[i],local[i]);
    io.io->send_data(peer.data(),int(peer.size()*4));io.io->flush();
  }else io.io->recv_data(local.data(),int(local.size()*4));
  return local;
}

}

int main(int argc,char**argv){
  int party=0,port=32000;std::string ip="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",ip,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,ip);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  HEState he;
  auto setup=measure(io,[&]{exchange_galois(io,party,he);});

  PreparedPerm p0,p1;
  if(party==ALICE)p0.p=random_perm(M,rng);else p0.p.resize(M);
  if(party==BOB)p1.p=random_perm(M,rng);else p1.p.resize(M);

  auto prep=measure(io,[&]{
    generate_corr_set(io,party,he,rng,ALICE,p0.p,p0.fwd,p0.inv);
    generate_corr_set(io,party,he,rng,BOB,p1.p,p1.fwd,p1.inv);
  });

  // Build exact fixed-weight fixture: w real unresolved + CAP-w dummy active.
  constexpr int W=170;
  std::vector<uint32_t> clear(size_t(M)*2,0);
  if(party==ALICE){
    std::vector<int> idx(N);std::iota(idx.begin(),idx.end(),0);
    std::mt19937 gen(201);std::shuffle(idx.begin(),idx.end(),gen);
    for(int k=0;k<W;++k){
      int i=idx[k];clear[size_t(i)*2]=1;
      int32_t z=(i%2?1:-1)*(1+(i*7919)%2000);
      clear[size_t(i)*2+1]=uint32_t(z)&RMASK;
    }
    for(int k=0;k<CAP-W;++k){
      int i=N+k;clear[size_t(i)*2]=1;clear[size_t(i)*2+1]=0;
    }
  }
  auto local=share_clear(io,party,rng,clear);

  int open_weight=0,mismatches=0;
  std::vector<uint32_t> final_share(M);
  std::vector<uint32_t> y1;
  std::vector<int> active;

  // Movement rounds 1--3: two one-message permutation shares, then open only
  // the uniformly shuffled fixed-weight flag vector.
  Phase ph_forward=measure(io,[&]{
    auto y0=apply_regular(io,party,ALICE,p0.p,p0.fwd,local,2);
    y1=apply_regular(io,party,BOB,p1.p,p1.fwd,y0,2);

    std::vector<uint32_t> peer_flags(M),flags(M),my_flags(M);
    for(int i=0;i<M;++i)my_flags[i]=y1[size_t(i)*2];
    if(party==ALICE){
      io.io->send_data(my_flags.data(),M*4);io.io->flush();
      io.io->recv_data(peer_flags.data(),M*4);
    }else{
      io.io->recv_data(peer_flags.data(),M*4);
      io.io->send_data(my_flags.data(),M*4);io.io->flush();
    }
    for(int i=0;i<M;++i){
      flags[i]=add24(my_flags[i],peer_flags[i]);
      if(flags[i]){++open_weight;active.push_back(i);}
      if(flags[i]>1)++mismatches;
    }
    if(int(active.size())!=CAP)mismatches++;
  });

  // Native baseline ReLU, completely unchanged, on exactly CAP public shuffled slots.
  std::vector<uint32_t> shuffled_out(M,0);
  Phase ph_relu=measure(io,[&]{
    FixArray tail(party,CAP,true,ELL,0);
    for(int k=0;k<CAP;++k)tail.data[k]=y1[size_t(active[k])*2+1];
    auto relu=native_relu(math,tail);
    for(int k=0;k<CAP;++k)shuffled_out[active[k]]=uint32_t(relu.data[k])&RMASK;
  });

  // Movement rounds 4--5: inverse the same secret-shared random permutation.
  Phase ph_inverse=measure(io,[&]{
    auto x1=apply_inverse(io,party,BOB,p1.p,p1.inv,shuffled_out,1);
    final_share=apply_inverse(io,party,ALICE,p0.p,p0.inv,x1,1);
  });

  const uint64_t movement_bytes=ph_forward.bytes+ph_inverse.bytes;
  const uint64_t movement_rounds_measured=ph_forward.rounds+ph_inverse.rounds;
  const double movement_ms=ph_forward.ms+ph_inverse.ms;

  // Regression opening AFTER measured path.
  std::vector<uint32_t> peer(M),opened(M);
  if(party==ALICE){io.io->send_data(final_share.data(),M*4);io.io->flush();io.io->recv_data(peer.data(),M*4);}
  else{io.io->recv_data(peer.data(),M*4);io.io->send_data(final_share.data(),M*4);io.io->flush();}
  for(int i=0;i<M;++i)opened[i]=add24(final_share[i],peer[i]);

  if(party==ALICE){
    for(int i=0;i<M;++i){
      uint32_t exp=0;
      if(clear[size_t(i)*2]){
        uint32_t z=clear[size_t(i)*2+1];
        int32_t sv=(z&(1u<<(ELL-1)))?int32_t(z|~RMASK):int32_t(z);
        exp=sv>0?z:0;
      }
      mismatches+=opened[i]!=exp;
    }
  }

  std::cout<<"EXP201_RESULT party="<<party
           <<" N="<<N<<" capacity="<<CAP<<" M="<<M
           <<" setup_bytes="<<setup.bytes<<" setup_rounds="<<setup.rounds<<" setup_ms="<<setup.ms
           <<" preprocess_bytes="<<prep.bytes<<" preprocess_rounds="<<prep.rounds<<" preprocess_ms="<<prep.ms
           <<" movement_conceptual_rounds=5"
           <<" movement_measured_rounds="<<movement_rounds_measured
           <<" movement_bytes="<<movement_bytes<<" movement_ms="<<movement_ms
           <<" forward_measured_rounds="<<ph_forward.rounds
           <<" inverse_measured_rounds="<<ph_inverse.rounds
           <<" native_relu_bytes="<<ph_relu.bytes
           <<" native_relu_rounds="<<ph_relu.rounds
           <<" native_relu_ms="<<ph_relu.ms
           <<" opened_weight="<<open_weight
           <<" native_relu_calls="<<CAP
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}