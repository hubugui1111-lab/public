#include <seal/seal.h>
#include "FloatingPoint/fp-math.h"
#include "utils/io_pack.h"
#include "OT/emp-ot.h"
#include "GC/emp-sh2pc.h"
#include "Millionaire/bit-triple-generator.h"
#include "shared_controls.h"
#include "prepared_shared_leaf_lookup16.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <map>
#include <memory>
#include <numeric>
#include <random>
#include <sstream>
#include <vector>

using namespace sci;
using namespace seal;
using Clock=std::chrono::steady_clock;
using namespace shared_residual;

namespace {
constexpr int N=3072,CAP=320,M=N+CAP,ELL=24,DEPTH=4,INTERNAL=15,LEAVES=16;
constexpr uint64_t MASK=(1ULL<<ELL)-1;
constexpr uint32_t RMASK=(1u<<ELL)-1;
constexpr int TARGET_LEAF=11,A=2048,BOUND=2*A;

struct Phase{uint64_t bytes=0,rounds=0;double ms=0;};
void flush_all(IOPack&io){io.io->flush();io.io_rev->flush();io.io_GC->flush();}
template<class F> Phase measure(IOPack&io,F&&f){
  auto b=io.get_comm(),r=io.get_rounds();auto t=Clock::now();
  f();flush_all(io);auto e=Clock::now();
  return {io.get_comm()-b,io.get_rounds()-r,
    std::chrono::duration<double,std::milli>(e-t).count()};
}
uint64_t enc_signed(int64_t x){return uint64_t(x)&MASK;}
int64_t dec_signed(uint64_t x){x&=MASK;return (x&(1ULL<<(ELL-1)))?int64_t(x)-int64_t(1ULL<<ELL):int64_t(x);}
uint8_t pred_bit(int leaf,int i){
  uint32_t x=uint32_t(leaf+1)*0x9e3779b9U ^ uint32_t(i+17)*0x85ebca6bU;
  x^=x>>16;x*=0x7feb352dU;x^=x>>15;x*=0x846ca68bU;x^=x>>16;return uint8_t(x&1);
}
bool flip_for_unresolved(int i){return ((uint32_t(i)*2654435761U+17U)%10000U)<550U;}
int path_internal_node(int leaf,int depth){
  int node=0;for(int d=0;d<depth;++d){int bit=(leaf>>(DEPTH-1-d))&1;node=2*node+1+bit;}return node;
}
uint8_t target_branch(int leaf,int depth){return uint8_t((leaf>>(DEPTH-1-depth))&1);}

BoolArray make_leaf_onehot(FPMath&math,const BoolArray&probe_sign){
  BoolArray cur(math.party,2);cur.data[1]=probe_sign.data[0];
  cur.data[0]=probe_sign.data[0]^uint8_t(math.party==ALICE);
  int offset=1;
  for(int depth=1;depth<DEPTH;++depth){
    int m=1<<depth;BoolArray branch(math.party,m);
    for(int j=0;j<m;++j)branch.data[j]=probe_sign.data[offset+j];
    auto right=math.bool_op->AND(cur,branch);
    BoolArray next(math.party,2*m);
    for(int j=0;j<m;++j){next.data[2*j]=cur.data[j]^right.data[j];next.data[2*j+1]=right.data[j];}
    cur=std::move(next);offset+=m;
  }
  return cur;
}


struct BoolTriplePack{
  std::vector<uint8_t>a,b,c;
  std::vector<uint64_t>a_add,b_add,c_add;
  Phase prep;
};
BoolTriplePack prepare_bool_triples_dual(FPMath&math,IOPack&io,OTPack&ot,int party,int n){
  // First n/2 triples are Boolean-only.  Last n/2 are also converted
  // offline to Z_2^ELL additive shares, so the final certificate can be
  // emitted in Boolean + arithmetic form in the SAME online Beaver opening.
  BoolTriplePack out;
  out.a.resize(n);out.b.resize(n);out.c.resize(n);
  const int dual=n/2;
  TripleGenerator gen(party,&io,&ot);
  out.prep=measure(io,[&]{
    gen.generate(party,out.a.data(),out.b.data(),out.c.data(),
                 n,_16KKOT_to_4OT,false,1);
    BoolArray packed(party,3*dual);
    for(int i=0;i<dual;++i){
      packed.data[i]=out.a[dual+i];
      packed.data[dual+i]=out.b[dual+i];
      packed.data[2*dual+i]=out.c[dual+i];
    }
    auto add=math.fix->B2A(packed,false,ELL);
    out.a_add.assign(add.data,add.data+dual);
    out.b_add.assign(add.data+dual,add.data+2*dual);
    out.c_add.assign(add.data+2*dual,add.data+3*dual);
  });
  return out;
}
BoolArray beaver_bool_and(IOPack&io,int party,const BoolArray&x,const BoolArray&y,
                         const uint8_t*a,const uint8_t*b,const uint8_t*c){
  if(x.size!=y.size)throw std::runtime_error("beaver size");
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


void beaver_bool_and_dual(IOPack&io,int party,const BoolArray&x,const BoolArray&y,
                         const uint8_t*a,const uint8_t*b,const uint8_t*c,
                         const uint64_t*a_add,const uint64_t*b_add,const uint64_t*c_add,
                         BoolArray&z,FixArray&z_add){
  if(x.size!=y.size)throw std::runtime_error("dual beaver size");
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
  z=BoolArray(party,n);
  z_add=FixArray(party,n,false,ELL,0);
  for(int i=0;i<n;++i){
    const uint8_t d=(mine[i]^peer[i])&1;
    const uint8_t e=(mine[n+i]^peer[n+i])&1;
    z.data[i]=(c[i]^(d&b[i])^(e&a[i])^((party==ALICE)?(d&e):0))&1;
    uint64_t v=0;
    if(!d&&!e) v=c_add[i];
    else if(d&&!e) v=(b_add[i]-c_add[i])&MASK;
    else if(!d&&e) v=(a_add[i]-c_add[i])&MASK;
    else v=((party==ALICE?1ULL:0ULL)-a_add[i]-b_add[i]+c_add[i])&MASK;
    z_add.data[i]=v;
  }
}

std::vector<uint8_t> pack_bits219(const std::vector<uint8_t>&v){
  std::vector<uint8_t> out((v.size()+7)/8,0);
  for(size_t i=0;i<v.size();++i)out[i>>3]|=uint8_t((v[i]&1)<<(i&7));
  return out;
}
uint8_t packed_bit219(const std::vector<uint8_t>&v,int i){
  return uint8_t((v[i>>3]>>(i&7))&1);
}

struct DaBitPack{
  BoolArray a_bool;
  FixArray a_add;
  Phase prep;
  DaBitPack(int party,int n):a_bool(party,n),a_add(party,n,false,ELL,0){}
};
DaBitPack prepare_dabit(FPMath&math,IOPack&io,PRG128&rng,int party,int n){
  DaBitPack d(party,n);
  std::vector<uint64_t>raw(n);rng.random_data(raw.data(),size_t(n)*8);
  for(int i=0;i<n;++i)d.a_bool.data[i]=uint8_t(raw[i]&1);
  d.prep=measure(io,[&]{d.a_add=math.fix->B2A(d.a_bool,false,ELL);});
  return d;
}
FixArray dabit_b2a(IOPack&io,int party,const BoolArray&x,const DaBitPack&d){
  const int n=x.size;
  if(d.a_bool.size!=n||d.a_add.size!=n)throw std::runtime_error("dabit size");
  std::vector<uint8_t> delta(n);
  for(int i=0;i<n;++i)delta[i]=(x.data[i]^d.a_bool.data[i])&1;
  auto mine=pack_bits219(delta);
  std::vector<uint8_t> peer(mine.size());
  if(party==ALICE){
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()));
    io.io->send_data(mine.data(),int(mine.size()));io.io->flush();
  }
  FixArray y(party,n,false,ELL,0);
  for(int i=0;i<n;++i){
    const uint8_t opened=uint8_t(delta[i]^packed_bit219(peer,i));
    y.data[i]=opened
      ? (((party==ALICE)?1ULL:0ULL)-d.a_add.data[i])&MASK
      : d.a_add.data[i]&MASK;
  }
  return y;
}

struct MixedTriple219{
  BoolArray a_bool;
  FixArray a_add,b,c;
  Phase prep;
  MixedTriple219(int party,int n):a_bool(party,n),a_add(party,n,false,ELL,0),
                                  b(party,n,true,ELL,0),c(party,n,true,ELL,0){}
};
MixedTriple219 prepare_mixed219(FPMath&math,IOPack&io,PRG128&rng,int party,int n){
  MixedTriple219 t(party,n);
  std::vector<uint64_t>raw(n);rng.random_data(raw.data(),size_t(n)*8);
  for(int i=0;i<n;++i)t.a_bool.data[i]=uint8_t(raw[i]&1);
  t.prep=measure(io,[&]{
    t.a_add=math.fix->B2A(t.a_bool,false,ELL);
    std::vector<uint64_t>br(n);rng.random_data(br.data(),size_t(n)*8);
    for(int i=0;i<n;++i)t.b.data[i]=br[i]&MASK;
    t.c=math.fix->mul(t.a_add,t.b,ELL);
  });
  return t;
}
FixArray mixed_mul219(IOPack&io,int party,const BoolArray&sel,const FixArray&x,
                      const MixedTriple219&t){
  const int n=x.size;
  if(sel.size!=n||t.a_bool.size!=n)throw std::runtime_error("mixed size");
  std::vector<uint64_t> e_share(n),e_peer(n),e(n);
  std::vector<uint8_t> d_share(n);
  for(int i=0;i<n;++i){
    d_share[i]=(sel.data[i]^t.a_bool.data[i])&1;
    e_share[i]=(x.data[i]-t.b.data[i])&MASK;
  }
  auto pd=pack_bits219(d_share);
  const size_t EBYTES=size_t(n)*sizeof(uint64_t),DBYTES=pd.size();
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
  FixArray y(party,n,true,ELL,0);
  for(int i=0;i<n;++i){
    e[i]=(e_share[i]+e_peer[i])&MASK;
    const uint8_t d=uint8_t(d_share[i]^packed_bit219(pd_peer,i));
    const uint64_t ae=(t.a_add.data[i]*e[i])&MASK;
    if(!d)y.data[i]=(t.c.data[i]+ae)&MASK;
    else y.data[i]=(t.b.data[i]+((party==ALICE)?e[i]:0ULL)-t.c.data[i]-ae)&MASK;
  }
  return y;
}

uint8_t masked_leaf_gc(FPMath&math,OTPack&ot,const BoolArray&probe_sign,uint8_t leaf_mask){
  if(probe_sign.size!=INTERNAL)throw std::runtime_error("probe size");
  auto* pe=setup_semi_honest<NetIO>(math.iopack->io_GC,math.party,128);
  auto* iknp=ot.iknp_straight;
  if(math.party==ALICE)
    static_cast<SemiHonestGen<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->s);
  else
    static_cast<SemiHonestEva<NetIO>*>(pe)->setup_keys(iknp->k0,iknp->k1);

  std::vector<Bit>x; x.reserve(INTERNAL);
  for(int i=0;i<INTERNAL;++i){
    Bit a(math.party==ALICE?bool(probe_sign.data[i]&1):false,ALICE);
    Bit b(math.party==BOB?bool(probe_sign.data[i]&1):false,BOB);
    x.emplace_back(a^b);
  }
  auto mux=[](const Bit&sel,const Bit&one,const Bit&zero){
    return (sel & (one ^ zero)) ^ zero;
  };

  Bit b0=x[0];
  Bit b1=mux(b0,x[2],x[1]);
  Bit d20=mux(b1,x[4],x[3]);
  Bit d21=mux(b1,x[6],x[5]);
  Bit b2=mux(b0,d21,d20);

  Bit d30=mux(b2,x[8],x[7]);
  Bit d31=mux(b2,x[10],x[9]);
  Bit d32=mux(b2,x[12],x[11]);
  Bit d33=mux(b2,x[14],x[13]);
  Bit d310=mux(b1,d31,d30);
  Bit d311=mux(b1,d33,d32);
  Bit b3=mux(b0,d311,d310);

  std::array<Bit,4> leaf_bits={b3,b2,b1,b0}; // LSB -> MSB
  uint8_t out=0;
  for(int bit=0;bit<4;++bit){
    Bit r((leaf_mask>>bit)&1,ALICE);
    bool v=(leaf_bits[bit]^r).reveal<bool>(BOB);
    if(math.party==BOB && v)out|=uint8_t(1u<<bit);
  }
  math.iopack->io_GC->flush();
  delete circ_exec;
  delete prot_exec;
  return out;
}

FixArray native_relu(FPMath&math,const FixArray&x){
  auto sign=math.fix->GE(x,uint64_t(0));
  return math.fix->if_else(sign,x,uint64_t(0));
}
void print_phase(const char*name,int party,const Phase&p){
  std::cout<<"EXP219_PHASE party="<<party<<" name="<<name
           <<" bytes="<<p.bytes<<" rounds="<<p.rounds<<" ms="<<p.ms<<"\n";
}

// ---- Kangaroo-style blinded client-local comparison over additive shares ----
struct KComparePrep{
  int n=0;
  std::vector<uint64_t> alpha,beta,a,b,c;
  std::vector<uint8_t> flip;
  Phase phase;
  bool used=false;
};

std::vector<uint64_t> open_additive(IOPack&io,int party,const std::vector<uint64_t>&x){
  std::vector<uint64_t> peer(x.size()),opened(x.size());
  if(party==ALICE){
    io.io->send_data(x.data(),int(x.size()*8));io.io->flush();
    io.io->recv_data(peer.data(),int(peer.size()*8));
  }else{
    io.io->recv_data(peer.data(),int(peer.size()*8));
    io.io->send_data(x.data(),int(x.size()*8));io.io->flush();
  }
  for(size_t i=0;i<x.size();++i)opened[i]=(x[i]+peer[i])&MASK;
  return opened;
}

void share_alice_clear(IOPack&io,int party,PRG128&rng,int n,
                       const std::vector<uint64_t>&clear,
                       std::vector<uint64_t>&local){
  local.resize(n);std::vector<uint64_t>peer(n);
  if(party==ALICE){
    if(int(clear.size())!=n)throw std::runtime_error("clear share size");
    rng.random_data(local.data(),size_t(n)*8);
    for(int i=0;i<n;++i){local[i]&=MASK;peer[i]=(clear[i]-local[i])&MASK;}
    io.io->send_data(peer.data(),n*8);io.io->flush();
  }else io.io->recv_data(local.data(),n*8);
}

KComparePrep prepare_kcompare(FPMath&math,IOPack&io,int party,PRG128&rng,int n){
  KComparePrep p;p.n=n;p.flip.assign(n,0);
  auto b0=io.get_comm(),r0=io.get_rounds();auto t0=Clock::now();

  std::vector<uint64_t>ac(n),bc(n);
  if(party==ALICE){
    std::vector<uint64_t>raw(size_t(2)*n);rng.random_data(raw.data(),raw.size()*8);
    for(int i=0;i<n;++i){
      const int A0=2+int(raw[2*i]%511);          // 2..512
      const int B0=1+int(raw[2*i+1]%uint64_t(A0-1)); // 1..A-1
      const uint8_t f=uint8_t((raw[2*i]>>17)&1);p.flip[i]=f;
      const int sg=f?-1:1;
      ac[i]=enc_signed(int64_t(sg)*A0);
      bc[i]=enc_signed(int64_t(sg)*B0);
    }
  }
  share_alice_clear(io,party,rng,n,ac,p.alpha);
  share_alice_clear(io,party,rng,n,bc,p.beta);
  if(party==BOB)std::fill(p.flip.begin(),p.flip.end(),0);

  p.a.resize(n);p.b.resize(n);
  rng.random_data(p.a.data(),size_t(n)*8);rng.random_data(p.b.data(),size_t(n)*8);
  for(int i=0;i<n;++i){p.a[i]&=MASK;p.b[i]&=MASK;}
  FixArray aa(party,n,true,ELL,0),bb(party,n,true,ELL,0),cc;
  std::copy(p.a.begin(),p.a.end(),aa.data);std::copy(p.b.begin(),p.b.end(),bb.data);
  cc=math.fix->mul(aa,bb,ELL);flush_all(io);
  p.c.assign(cc.data,cc.data+n);

  p.phase={io.get_comm()-b0,io.get_rounds()-r0,
    std::chrono::duration<double,std::milli>(Clock::now()-t0).count()};
  return p;
}

BoolArray kangaroo_ge0(IOPack&io,int party,PRG128&rng,KComparePrep&p,
                       const std::vector<uint64_t>&dshare){
  if(p.used||int(dshare.size())!=p.n)throw std::runtime_error("kcompare invariant");
  p.used=true;const int n=p.n;
  std::vector<uint64_t>masked(size_t(2)*n);
  for(int i=0;i<n;++i){
    masked[i]=(p.alpha[i]-p.a[i])&MASK;
    masked[n+i]=(dshare[i]-p.b[i])&MASK;
  }
  auto opened=open_additive(io,party,masked);
  std::vector<uint64_t>tshare(n);
  for(int i=0;i<n;++i){
    __uint128_t v=p.c[i];
    v+=__uint128_t(opened[i])*p.b[i];
    v+=__uint128_t(opened[n+i])*p.a[i];
    if(party==ALICE)v+=__uint128_t(opened[i])*opened[n+i];
    tshare[i]=(uint64_t(v)+p.beta[i])&MASK;
  }

  BoolArray result(party,n);
  if(party==ALICE){
    io.io->send_data(tshare.data(),n*8);io.io->flush();
    std::vector<uint8_t>masked_bit(n);io.io->recv_data(masked_bit.data(),n);
    for(int i=0;i<n;++i)result.data[i]=uint8_t(masked_bit[i]^p.flip[i]);
  }else{
    std::vector<uint64_t>server(n);io.io->recv_data(server.data(),n*8);
    std::vector<uint8_t>masked_bit(n),client_share(n);
    std::vector<uint64_t>raw(n);rng.random_data(raw.data(),size_t(n)*8);
    for(int i=0;i<n;++i){
      const uint64_t t=(tshare[i]+server[i])&MASK;
      const uint8_t blinded=uint8_t(dec_signed(t)>=0);
      client_share[i]=uint8_t(raw[i]&1);
      masked_bit[i]=uint8_t(blinded^client_share[i]);
      result.data[i]=client_share[i];
    }
    io.io->send_data(masked_bit.data(),n);io.io->flush();
  }
  return result;
}

// ---- Additive 5-round secret-shuffle backend (Exp201) ----
uint32_t add24(uint32_t a,uint32_t b){return (a+b)&RMASK;}
uint32_t sub24(uint32_t a,uint32_t b){return (a-b)&RMASK;}
std::vector<uint32_t> random_perm(int n,PRG128&rng){
  std::vector<uint32_t> p(n);std::iota(p.begin(),p.end(),0);
  std::vector<uint64_t> r(n);rng.random_data(r.data(),n*8);
  for(int i=0;i<n;++i){int j=i+int(r[i]%uint64_t(n-i));std::swap(p[i],p[j]);}
  return p;
}
std::vector<uint32_t> inv_perm(const std::vector<uint32_t>&p){
  std::vector<uint32_t> q(p.size());for(size_t i=0;i<p.size();++i)q[p[i]]=uint32_t(i);return q;
}
void send_blob(NetIO*io,const std::string&s){uint64_t n=s.size();io->send_data(&n,8);io->send_data(s.data(),int(n));io->flush();}
std::string recv_blob(NetIO*io){uint64_t n=0;io->recv_data(&n,8);std::string s(n,'\0');io->recv_data(s.data(),int(n));return s;}
template<class T>std::string save_obj(const T&x){std::stringstream ss(std::ios::in|std::ios::out|std::ios::binary);x.save(ss);return ss.str();}
template<class T>T load_obj(const SEALContext&ctx,const std::string&s){T x;std::stringstream ss(s,std::ios::in|std::ios::binary);x.load(ctx,ss);return x;}

struct HEState{
  EncryptionParameters parms;SEALContext ctx;BatchEncoder encoder;KeyGenerator keygen;SecretKey sk;
  GaloisKeys gk_local,gk_peer;Evaluator eval;Encryptor enc;Decryptor dec;size_t slots,row;uint64_t plain_mod;
  HEState():parms(scheme_type::bfv),
    ctx([&]{parms.set_poly_modulus_degree(8192);parms.set_coeff_modulus(CoeffModulus::BFVDefault(8192));
      parms.set_plain_modulus(PlainModulus::Batching(8192,40));return SEALContext(parms);}()),
    encoder(ctx),keygen(ctx),sk(keygen.secret_key()),eval(ctx),enc(ctx,sk),dec(ctx,sk){
    keygen.create_galois_keys(gk_local);slots=encoder.slot_count();row=slots/2;plain_mod=parms.plain_modulus().value();
    if(row<4096||M>int(row))throw std::runtime_error("slot invariant");
  }
};
void exchange_galois(IOPack&io,int party,HEState&he){
  auto b=save_obj(he.gk_local);std::string p;
  if(party==ALICE){send_blob(io.io,b);p=recv_blob(io.io);}else{p=recv_blob(io.io);send_blob(io.io,b);}
  he.gk_peer=load_obj<GaloisKeys>(he.ctx,p);
}
Plaintext encode_cols(HEState&he,const std::vector<uint32_t>&v,int cols){
  std::vector<uint64_t> slots(he.slots,0);if(int(v.size())!=M*cols)throw std::runtime_error("encode size");
  for(int i=0;i<M;++i){slots[i]=v[size_t(i)*cols];if(cols==2)slots[he.row+i]=v[size_t(i)*cols+1];}
  Plaintext p;he.encoder.encode(slots,p);return p;
}
std::vector<uint32_t> decode_cols(HEState&he,const Plaintext&p,int cols){
  std::vector<uint64_t> slots;he.encoder.decode(p,slots);std::vector<uint32_t> v(size_t(M)*cols);
  const int64_t half=int64_t(he.plain_mod/2);
  for(int i=0;i<M;++i){
    auto cv=[&](uint64_t x){int64_t s=x>uint64_t(half)?int64_t(x)-int64_t(he.plain_mod):int64_t(x);return uint32_t(uint64_t(s)&RMASK);};
    v[size_t(i)*cols]=cv(slots[i]);if(cols==2)v[size_t(i)*cols+1]=cv(slots[he.row+i]);
  }return v;
}
Ciphertext he_permute(HEState&he,const Ciphertext&ct,const std::vector<uint32_t>&p,int cols){
  std::map<int,std::vector<int>> shifts;const int R=int(he.row);
  for(int i=0;i<M;++i){int s=(int(p[i])-i)%R;if(s<0)s+=R;shifts[s].push_back(i);}
  Ciphertext acc;bool first=true;
  for(auto&kv:shifts){
    Ciphertext tmp;if(kv.first==0)tmp=ct;else he.eval.rotate_rows(ct,kv.first,he.gk_peer,tmp);
    std::vector<uint64_t> mask(he.slots,0);
    for(int i:kv.second){mask[i]=1;if(cols==2)mask[he.row+i]=1;}
    Plaintext pm;he.encoder.encode(mask,pm);he.eval.multiply_plain_inplace(tmp,pm);
    if(first){acc=std::move(tmp);first=false;}else he.eval.add_inplace(acc,tmp);
  }return acc;
}
struct OwnerCorr{std::vector<uint32_t> delta;};
struct RecvCorr{std::vector<uint32_t>A,B;};
struct CorrPair{OwnerCorr owner;RecvCorr recv;};
struct PreparedPerm{std::vector<uint32_t>p;CorrPair fwd,inv;};
std::vector<uint32_t> rand_ring(PRG128&rng,int n){
  std::vector<uint32_t>v(n);std::vector<uint64_t>r(n);rng.random_data(r.data(),n*8);
  for(int i=0;i<n;++i)v[i]=uint32_t(r[i])&RMASK;return v;
}
void receiver_send_A(IOPack&io,HEState&he,PRG128&rng,int cols,RecvCorr&rc){
  rc.A=rand_ring(rng,M*cols);Plaintext pa=encode_cols(he,rc.A,cols);Ciphertext ct;he.enc.encrypt_symmetric(pa,ct);send_blob(io.io,save_obj(ct));
}
void owner_process_A(IOPack&io,HEState&he,PRG128&rng,const std::vector<uint32_t>&p,int cols,OwnerCorr&oc){
  auto ct=load_obj<Ciphertext>(he.ctx,recv_blob(io.io));auto pct=he_permute(he,ct,p,cols);
  oc.delta=rand_ring(rng,M*cols);Plaintext pd=encode_cols(he,oc.delta,cols);he.eval.sub_plain_inplace(pct,pd);send_blob(io.io,save_obj(pct));
}
void receiver_recv_B(IOPack&io,HEState&he,int cols,RecvCorr&rc){
  auto ct=load_obj<Ciphertext>(he.ctx,recv_blob(io.io));Plaintext pb;he.dec.decrypt(ct,pb);rc.B=decode_cols(he,pb,cols);
}
void generate_corr_set(IOPack&io,int party,HEState&he,PRG128&rng,int ownerParty,const std::vector<uint32_t>&p,CorrPair&fwd,CorrPair&inv){
  if(party==ownerParty){
    owner_process_A(io,he,rng,p,2,fwd.owner);owner_process_A(io,he,rng,p,1,inv.owner);
  }else{
    receiver_send_A(io,he,rng,2,fwd.recv);receiver_recv_B(io,he,2,fwd.recv);
    receiver_send_A(io,he,rng,1,inv.recv);receiver_recv_B(io,he,1,inv.recv);
  }
}
std::vector<uint32_t> apply_regular(IOPack&io,int party,int ownerParty,const std::vector<uint32_t>&p,const CorrPair&corr,const std::vector<uint32_t>&in,int cols){
  std::vector<uint32_t>out(size_t(M)*cols),msg(size_t(M)*cols);
  if(party!=ownerParty){
    for(size_t i=0;i<msg.size();++i)msg[i]=sub24(in[i],corr.recv.A[i]);
    io.io->send_data(msg.data(),int(msg.size()*4));io.io->flush();out=corr.recv.B;
  }else{
    io.io->recv_data(msg.data(),int(msg.size()*4));
    for(int i=0;i<M;++i)for(int c=0;c<cols;++c){
      size_t d=size_t(i)*cols+c,ss=size_t(p[i])*cols+c;
      out[d]=add24(add24(in[ss],msg[ss]),corr.owner.delta[d]);
    }
  }return out;
}
std::vector<uint32_t> apply_inverse(IOPack&io,int party,int ownerParty,const std::vector<uint32_t>&p,const CorrPair&corr,const std::vector<uint32_t>&in,int cols){
  std::vector<uint32_t>out(size_t(M)*cols),msg(size_t(M)*cols);
  if(party!=ownerParty){
    for(size_t i=0;i<msg.size();++i)msg[i]=sub24(in[i],corr.recv.B[i]);
    io.io->send_data(msg.data(),int(msg.size()*4));io.io->flush();out=corr.recv.A;
  }else{
    auto pinv=inv_perm(p);io.io->recv_data(msg.data(),int(msg.size()*4));
    for(int i=0;i<M;++i)for(int c=0;c<cols;++c){
      size_t d=size_t(i)*cols+c,ss=size_t(pinv[i])*cols+c;
      out[d]=sub24(add24(in[ss],msg[ss]),corr.owner.delta[ss]);
    }
  }return out;
}

// Secret need=(CAP-w) -> XOR-shared dummy prefix of exactly need ones.
BoolArray make_dummy_flags(FPMath&math,uint64_t need_share){
  const uint8_t one=uint8_t(math.party==ALICE);
  auto bitsv=decompose(math,{need_share&511ULL},{9});
  auto&bits=bitsv[0];
  std::vector<uint8_t> onehot(1,one);
  for(int bit=0;bit<9;++bit){
    const int old=int(onehot.size());
    BoolArray aa(math.party,old),bb(math.party,old);
    for(int i=0;i<old;++i){aa.data[i]=onehot[i];bb.data[i]=bits[bit];}
    auto high=math.bool_op->AND(aa,bb);
    std::vector<uint8_t> next(2*old);
    for(int i=0;i<old;++i){next[i]=onehot[i]^high.data[i];next[i+old]=high.data[i];}
    onehot=std::move(next);
  }
  BoolArray dummy(math.party,CAP);uint8_t suffix=0;
  for(int j=int(onehot.size())-2;j>=0;--j){
    suffix^=onehot[j+1];if(j<CAP)dummy.data[j]=suffix;
  }
  return dummy;
}
}

int main(int argc,char**argv){
  int party=0,port=32000;std::string address="127.0.0.1";
  ArgMapping amap;amap.arg("r",party,"role");amap.arg("p",port,"port");amap.arg("ip",address,"ip");amap.parse(argc,argv);
  if(party!=ALICE&&party!=BOB)return 2;
  IOPack io(party,port,address);OTPack ot(&io,party);FPMath math(party,&io,&ot);PRG128 rng;

  // One-time-pad the leaf index. BOB will learn only masked_leaf=true_leaf XOR leaf_mask.
  uint8_t leaf_mask=0;
  if(party==ALICE){rng.random_data(&leaf_mask,1);leaf_mask&=15;}
  std::vector<uint64_t>clear_bounds;std::vector<uint8_t>clear_signs;
  if(party==ALICE){
    clear_bounds.resize(size_t(LEAVES)*N);clear_signs.resize(size_t(LEAVES)*N);
    for(int masked=0;masked<LEAVES;++masked){
      const int real_leaf=masked^leaf_mask;
      for(int i=0;i<N;++i){
        clear_bounds[size_t(masked)*N+i]=BOUND;
        clear_signs[size_t(masked)*N+i]=pred_bit(real_leaf,i);
      }
    }
  }
  auto leaf_lookup=std::make_unique<exp198::PreparedSharedLeafLookup16>(math,rng,N,ELL,clear_bounds,clear_signs);

  // Fresh one-use preprocessing for all auxiliary order predicates introduced
  // by our screening protocol. Native fallback ReLU is deliberately excluded.
  auto k_probe=prepare_kcompare(math,io,party,rng,INTERNAL);
  auto k_cert=prepare_kcompare(math,io,party,rng,4*N);
  auto k_count=prepare_kcompare(math,io,party,rng,CAP+1);
  auto bool_triples=prepare_bool_triples_dual(math,io,ot,party,4*N);
  auto dummy_dabit=prepare_dabit(math,io,rng,party,CAP);
  auto merge_triple=prepare_mixed219(math,io,rng,party,N);

  // Secure input-independent additive permutation correlations.
  HEState he;
  Phase ph_shuffle_setup=measure(io,[&]{exchange_galois(io,party,he);});
  PreparedPerm p0,p1;
  if(party==ALICE)p0.p=random_perm(M,rng);else p0.p.resize(M);
  if(party==BOB)p1.p=random_perm(M,rng);else p1.p.resize(M);
  Phase ph_shuffle_pre=measure(io,[&]{
    generate_corr_set(io,party,he,rng,ALICE,p0.p,p0.fwd,p0.inv);
    generate_corr_set(io,party,he,rng,BOB,p1.p,p1.fwd,p1.inv);
  });

  // Secret-shared input z.
  std::vector<uint64_t>z_local(N),z_peer(N),z_clear(N);
  if(party==ALICE){
    for(int i=0;i<N;++i){
      bool pos=pred_bit(TARGET_LEAF,i)!=0;if(flip_for_unresolved(i))pos=!pos;
      int mag=1+((i*7919)%1000);z_clear[i]=enc_signed(pos?mag:-mag);
    }
    for(int d=0;d<DEPTH;++d){
      int node=path_internal_node(TARGET_LEAF,d);bool pos=target_branch(TARGET_LEAF,d)!=0;
      z_clear[node]=enc_signed(pos?(101+d):-(101+d));
    }
    rng.random_data(z_local.data(),N*8);
    for(int i=0;i<N;++i){z_local[i]&=MASK;z_peer[i]=(z_clear[i]-z_local[i])&MASK;}
    io.io->send_data(z_peer.data(),N*8);io.io->flush();
  }else io.io->recv_data(z_local.data(),N*8);
  FixArray z(party,N,true,ELL,0);std::copy(z_local.begin(),z_local.end(),z.data);

  // Single synchronization outside the measured online region.
  io.io->sync();
  const auto tb0=io.get_comm(),tr0=io.get_rounds();auto tt0=Clock::now();

  FixArray probe_z(party,INTERNAL,true,ELL,0);for(int j=0;j<INTERNAL;++j)probe_z.data[j]=z.data[j];
  std::vector<uint64_t>probe_d(INTERNAL);for(int j=0;j<INTERNAL;++j)probe_d[j]=probe_z.data[j];
  BoolArray probe_sign;auto ph_probe=measure(io,[&]{probe_sign=kangaroo_ge0(io,party,rng,k_probe,probe_d);});
  uint8_t masked_leaf=0;
  auto ph_route=measure(io,[&]{masked_leaf=masked_leaf_gc(math,ot,probe_sign,leaf_mask);});

  exp198::LeafLookupResult lr;FixArray bound(party,N,true,ELL,0);BoolArray pred_pos(party,N);
  auto ph_leaf=measure(io,[&]{
    const uint8_t lookup_choice=(party==BOB)?masked_leaf:0;
    lr=leaf_lookup->query(lookup_choice);
    std::copy(lr.bound_shares.begin(),lr.bound_shares.end(),bound.data);
    std::copy(lr.sign_shares.begin(),lr.sign_shares.end(),pred_pos.data);
  });

  // Eliminate the secret signed-alignment mux entirely.
  // Evaluate both exact sign-consistent intervals in parallel:
  // positive prediction:  1 <= z <= U-1
  // negative prediction: -U+1 <= z <= -1
  // Then select between the two Boolean certificates with cheap Boolean Beaver logic.
  Phase ph_align{};
  std::vector<uint64_t>cert_d(size_t(4)*N);
  for(int i=0;i<N;++i){
    const uint64_t one=(party==ALICE?1ULL:0ULL);
    cert_d[i]=(z.data[i]-one)&MASK;                         // z >= 1
    cert_d[N+i]=(bound.data[i]-z.data[i]-one)&MASK;       // z <= U-1
    cert_d[2*N+i]=((-z.data[i])&MASK)-one;                // z <= -1
    cert_d[3*N+i]=(bound.data[i]+z.data[i]-one)&MASK;     // z >= -U+1
    cert_d[2*N+i]&=MASK;cert_d[3*N+i]&=MASK;
  }
  BoolArray cert,safe_positive;
  auto ph_cert=measure(io,[&]{
    auto cmp=kangaroo_ge0(io,party,rng,k_cert,cert_d);
    BoolArray pair_l(party,2*N),pair_h(party,2*N);
    for(int i=0;i<N;++i){
      pair_l.data[i]=cmp.data[i];pair_h.data[i]=cmp.data[N+i];
      pair_l.data[N+i]=cmp.data[2*N+i];pair_h.data[N+i]=cmp.data[3*N+i];
    }
    auto pair_cert=beaver_bool_and(io,party,pair_l,pair_h,
      bool_triples.a.data(),bool_triples.b.data(),bool_triples.c.data());
    BoolArray pos_cert(party,N),neg_cert(party,N);
    for(int i=0;i<N;++i){pos_cert.data[i]=pair_cert.data[i];neg_cert.data[i]=pair_cert.data[N+i];}

    // Second layer computes the two mutually exclusive certified branches:
    // safe_pos = pred & pos_cert; safe_neg = (~pred) & neg_cert.
    BoolArray layer_x(party,2*N),layer_y(party,2*N);
    for(int i=0;i<N;++i){
      layer_x.data[i]=pred_pos.data[i];
      layer_y.data[i]=pos_cert.data[i];
      layer_x.data[N+i]=pred_pos.data[i]^uint8_t(party==ALICE);
      layer_y.data[N+i]=neg_cert.data[i];
    }
    BoolArray layer_out;FixArray layer_add;
    beaver_bool_and_dual(io,party,layer_x,layer_y,
      bool_triples.a.data()+2*N,bool_triples.b.data()+2*N,bool_triples.c.data()+2*N,
      bool_triples.a_add.data(),bool_triples.b_add.data(),bool_triples.c_add.data(),
      layer_out,layer_add);
    cert=BoolArray(party,N);safe_positive=BoolArray(party,N);
    FixArray cert_add(party,N,false,ELL,0);
    for(int i=0;i<N;++i){
      // The positive and negative safe branches are mutually exclusive.
      cert.data[i]=layer_out.data[i]^layer_out.data[N+i];
      safe_positive.data[i]=layer_out.data[i];
      cert_add.data[i]=(layer_add.data[i]+layer_add.data[N+i])&MASK;
    }

    // Reuse layer_add storage tail-free by placing cert additive shares into
    // the first N entries for the immediately following local count phase.
    for(int i=0;i<N;++i)layer_add.data[i]=cert_add.data[i];
    // Export through a local static handoff below.
    for(int i=0;i<N;++i)cert_d[i]=layer_add.data[i];
  });

  // cert_d[0..N) is now repurposed as additive certificate shares.
  FixArray marks_a(party,N,false,ELL,0);uint64_t w_share=0;
  auto ph_count=measure(io,[&]{
    for(int i=0;i<N;++i){
      const uint64_t cert_add_share=cert_d[i]&MASK;
      marks_a.data[i]=((party==ALICE?1ULL:0ULL)-cert_add_share)&MASK;
      w_share=(w_share+marks_a.data[i])&MASK;
    }
  });

  // One Kangaroo-style batch computes both overflow and every dummy-prefix bit:
  // accept := B-w >= 0; dummy_j := B-w-j-1 >= 0.
  std::vector<uint64_t>count_d(CAP+1);
  count_d[0]=((party==ALICE?uint64_t(CAP):0)-w_share)&MASK;
  for(int j=0;j<CAP;++j)
    count_d[j+1]=((party==ALICE?uint64_t(CAP-j-1):0)-w_share)&MASK;
  BoolArray dummy(party,CAP);bool accepted=false;
  auto ph_dummy=measure(io,[&]{
    auto bits=kangaroo_ge0(io,party,rng,k_count,count_d);
    uint8_t mine=bits.data[0],peer=0;
    for(int j=0;j<CAP;++j)dummy.data[j]=bits.data[j+1];
    if(party==ALICE){io.io->send_data(&mine,1);io.io->flush();io.io->recv_data(&peer,1);}
    else{io.io->recv_data(&peer,1);io.io->send_data(&mine,1);io.io->flush();}
    accepted=((mine^peer)&1)!=0;
  });

  FixArray final_out(party,N,true,ELL,0);
  Phase ph_flags{},ph_forward{},ph_tail{},ph_inverse{},ph_merge{},ph_overflow{};
  int opened_weight=0;

  if(accepted){
    FixArray dummy_a;
    ph_flags=measure(io,[&]{dummy_a=dabit_b2a(io,party,dummy,dummy_dabit);});

    std::vector<uint32_t> local(size_t(M)*2,0),shuffled;
    for(int i=0;i<N;++i){
      local[size_t(i)*2]=uint32_t(marks_a.data[i])&RMASK;
      local[size_t(i)*2+1]=uint32_t(z.data[i])&RMASK;
    }
    for(int j=0;j<CAP;++j)local[size_t(N+j)*2]=uint32_t(dummy_a.data[j])&RMASK;

    std::vector<int> active;
    ph_forward=measure(io,[&]{
      auto y0=apply_regular(io,party,ALICE,p0.p,p0.fwd,local,2);
      shuffled=apply_regular(io,party,BOB,p1.p,p1.fwd,y0,2);

      std::vector<uint32_t>mine(M),peer(M);
      for(int i=0;i<M;++i)mine[i]=shuffled[size_t(i)*2];
      if(party==ALICE){io.io->send_data(mine.data(),M*4);io.io->flush();io.io->recv_data(peer.data(),M*4);}
      else{io.io->recv_data(peer.data(),M*4);io.io->send_data(mine.data(),M*4);io.io->flush();}
      for(int i=0;i<M;++i)if(add24(mine[i],peer[i])){active.push_back(i);++opened_weight;}
      if(int(active.size())!=CAP)throw std::runtime_error("fixed weight");
    });

    std::vector<uint32_t>shuffled_out(M,0);
    ph_tail=measure(io,[&]{
      FixArray tx(party,CAP,true,ELL,0);
      for(int k=0;k<CAP;++k)tx.data[k]=shuffled[size_t(active[k])*2+1];
      auto y=native_relu(math,tx);
      for(int k=0;k<CAP;++k)shuffled_out[active[k]]=uint32_t(y.data[k])&RMASK;
    });

    std::vector<uint32_t>back;
    ph_inverse=measure(io,[&]{
      auto x1=apply_inverse(io,party,BOB,p1.p,p1.inv,shuffled_out,1);
      back=apply_inverse(io,party,ALICE,p0.p,p0.inv,x1,1);
    });

    ph_merge=measure(io,[&]{
      auto known=mixed_mul219(io,party,safe_positive,z,merge_triple);
      for(int i=0;i<N;++i)final_out.data[i]=(known.data[i]+back[i])&MASK;
    });
  }else{
    ph_overflow=measure(io,[&]{final_out=native_relu(math,z);});
  }

  flush_all(io);
  const uint64_t total_bytes=io.get_comm()-tb0,total_rounds=io.get_rounds()-tr0;
  const double total_ms=std::chrono::duration<double,std::milli>(Clock::now()-tt0).count();

  io.io->sync();
  FixArray baseline;auto ph_full=measure(io,[&]{baseline=native_relu(math,z);});
  auto pub_final=math.fix->output(PUBLIC,final_out);auto pub_full=math.fix->output(PUBLIC,baseline);
  auto pub_cert=math.bool_op->output(PUBLIC,cert);
  int mismatches=0,cert_count=0,expected_cert=0;
  for(int i=0;i<N;++i){
    cert_count+=pub_cert.data[i];mismatches+=((pub_final.data[i]&MASK)!=(pub_full.data[i]&MASK));
    if(party==ALICE){
      bool pp=pred_bit(TARGET_LEAF,i)!=0;int64_t zc=dec_signed(z_clear[i]);int64_t x=pp?zc:-zc;
      bool exp=(x>0&&x<BOUND);expected_cert+=exp;mismatches+=int(bool(pub_cert.data[i])!=exp);
    }
  }
  // Test-only route check after the measured online region.
  uint8_t opened_masked_leaf=0;
  if(party==BOB){io.io->send_data(&masked_leaf,1);io.io->flush();}
  else{
    io.io->recv_data(&opened_masked_leaf,1);
    mismatches+=int(((opened_masked_leaf^leaf_mask)&15)!=TARGET_LEAF);
  }
  if(accepted)mismatches+=(opened_weight!=CAP);

  print_phase("probe15",party,ph_probe);print_phase("masked_leaf_gc_route",party,ph_route);
  print_phase("leaf_param_lookup",party,ph_leaf);print_phase("certificate_align_removed",party,ph_align);
  print_phase("kangaroo_plus_bool_beaver_certificate",party,ph_cert);
  print_phase("dual_share_local_count",party,ph_count);print_phase("kangaroo_accept_and_dummy",party,ph_dummy);
  print_phase("dabit_dummy_convert",party,ph_flags);print_phase("shuffle_forward_plus_open",party,ph_forward);
  print_phase("native_tail_relu",party,ph_tail);print_phase("shuffle_inverse",party,ph_inverse);
  print_phase("mixed_masked_merge",party,ph_merge);print_phase("overflow_full_relu",party,ph_overflow);
  print_phase("full_relu_baseline",party,ph_full);
  print_phase("kcompare_probe_preprocess",party,k_probe.phase);
  print_phase("kcompare_certificate_preprocess",party,k_cert.phase);
  print_phase("kcompare_count_preprocess",party,k_count.phase);print_phase("bool_triple_preprocess",party,bool_triples.prep);print_phase("dummy_dabit_preprocess",party,dummy_dabit.prep);print_phase("mixed_merge_preprocess",party,merge_triple.prep);
  print_phase("shuffle_setup",party,ph_shuffle_setup);print_phase("shuffle_preprocess",party,ph_shuffle_pre);

  std::cout<<"EXP219_RESULT party="<<party<<" N="<<N<<" capacity="<<CAP
           <<" accepted="<<(accepted?1:0)<<" cert_count="<<cert_count<<" expected_cert="<<expected_cert
           <<" cert_fraction="<<(double(cert_count)/N)
           <<" movement_conceptual_rounds=5"
           <<" movement_iopack_rounds="<<(ph_forward.rounds+ph_inverse.rounds)
           <<" movement_bytes="<<(ph_forward.bytes+ph_inverse.bytes)
           <<" opened_weight="<<opened_weight
           <<" total_bytes="<<total_bytes<<" total_rounds="<<total_rounds<<" total_ms="<<total_ms
           <<" shuffle_preprocess_bytes="<<ph_shuffle_pre.bytes<<" shuffle_preprocess_ms="<<ph_shuffle_pre.ms
           <<" full_relu_bytes="<<ph_full.bytes<<" full_relu_rounds="<<ph_full.rounds<<" full_relu_ms="<<ph_full.ms
           <<" mismatches="<<mismatches<<"\n";
  return mismatches?3:0;
}