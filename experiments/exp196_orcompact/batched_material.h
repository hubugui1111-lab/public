// SPDX-License-Identifier: MIT
// Input-independent fresh materials; original nonlinear backend is untouched.
#pragma once
#include "private_gates.h"
#include "pack_boolean64.h"
#include <chrono>
#include <numeric>

namespace shared_residual {
inline void random_bytes(sci::PRG128& rng,std::vector<uint8_t>& bytes) {
  std::vector<sci::block128> blocks((bytes.size()+15)/16);
  rng.random_block(blocks.data(),int(blocks.size()));
  if(!bytes.empty()) std::memcpy(bytes.data(),blocks.data(),bytes.size());
}
inline std::vector<uint8_t> open_bits(FPMath& math,const std::vector<uint8_t>& local) {
  std::vector<uint8_t> send((local.size()+7)/8,0),peer(send.size());
  for(size_t i=0;i<local.size();++i) {gate_require(local[i]<=1);send[i/8]|=local[i]<<(i%8);}
  if(math.party==sci::ALICE) {
    math.iopack->io->send_data(send.data(),int(send.size()));math.iopack->io->flush();
    math.iopack->io->recv_data(peer.data(),int(peer.size()));
  } else {
    math.iopack->io->recv_data(peer.data(),int(peer.size()));
    math.iopack->io->send_data(send.data(),int(send.size()));math.iopack->io->flush();
  }
  std::vector<uint8_t> result(local.size());
  for(size_t i=0;i<local.size();++i) result[i]=local[i]^((peer[i/8]>>(i%8))&1);
  return result;
}

struct TripleProvider {
  virtual ~TripleProvider()=default;
  virtual void fill(std::vector<uint8_t>&,std::vector<uint8_t>&,std::vector<uint8_t>&)=0;
};
class BatchedAnd:public AndProvider {
  TripleProvider* provider_=nullptr;
  FPMath& math_;sci::PRG128& rng_;int flavor_;size_t minimum_;
  std::vector<uint8_t> a_,b_,c_,r0_,rho_,selected_,choice_;
  std::vector<uint64_t> packed_a_,packed_b_,packed_c_;
  size_t cursor_=0;
  void refill(size_t need) {
    const auto start=std::chrono::steady_clock::now();
    packed_a_.clear();packed_b_.clear();packed_c_.clear();
    const size_t n=((std::max(minimum_,need)+255)/256)*256;
    a_.resize(n);b_.resize(n);c_.resize(n);r0_.resize(n);rho_.resize(n);selected_.resize(n);choice_.resize(n);
    if(provider_) {
      provider_->fill(a_,b_,c_);random_ots+=2*n;
    } else if(flavor_>=3) {
      // FLUTE Fig. 12: use independent random-choice ROTs directly. SCI's
      // preprocess() already hashes the extension rows; no chosen-message
      // or chosen-correlation correction is needed for random triples.
      // Both contexts are auxiliary; fully consume and empty their pools so
      // subsequent B2A/other users cannot reuse any of these correlations.
      for(auto* ot:{math_.otpack->iknp_straight,math_.otpack->iknp_reversed}) {
        gate_require(ot->precomp_batch_size==0);
        for(size_t base=0;base<n;) {
        const size_t count=flavor_==4 ? std::min(n-base,size_t(ot->block_size)):n;
        const size_t block=std::min(size_t(ot->block_size),(count+255)/256*256);
        extended_random_ots+=(count+block-1)/block*block;
        ot->set_precomp_batch_size(int(count));ot->l=1;ot->preprocess();
        if(ot->party==sci::ALICE) {
          for(size_t i=0;i<count;++i) {
            r0_[base+i]=ot->h[0][i]&1;
            b_[base+i]=(ot->h[0][i]^ot->h[1][i])&1;
          }
        } else {
          for(size_t i=0;i<count;++i) {
            a_[base+i]=ot->r_off[i]&1;selected_[base+i]=ot->h[0][i]&1;
          }
        }
        ot->counter=int(count);ot->set_precomp_batch_size(0);gate_flush(math_);base+=count;
        }
      }
      for(size_t i=0;i<n;++i) c_[i]=(a_[i]&b_[i])^selected_[i]^r0_[i];
      random_ots+=2*n;
    } else {
    random_bytes(rng_,a_);random_bytes(rng_,b_);
    std::vector<uint64_t> corr(n),sent(n),received(n);std::unique_ptr<bool[]> choices(new bool[n]);
    for(size_t i=0;i<n;++i) {a_[i]&=1;b_[i]&=1;corr[i]=b_[i];choices[i]=a_[i]!=0;}
    if(math_.party==sci::ALICE) math_.otpack->iknp_straight->send_cot(sent.data(),corr.data(),int(n),1);
    else math_.otpack->iknp_straight->recv_cot(received.data(),choices.get(),int(n),1);
    gate_flush(math_);
    if(math_.party==sci::BOB) math_.otpack->iknp_reversed->send_cot(sent.data(),corr.data(),int(n),1);
    else math_.otpack->iknp_reversed->recv_cot(received.data(),choices.get(),int(n),1);
    gate_flush(math_);
    for(size_t i=0;i<n;++i) {
      c_[i]=uint8_t(sent[i]^received[i]^(a_[i]&b_[i]))&1;
      r0_[i]=sent[i]&1;rho_[i]=b_[i];selected_[i]=received[i]&1;choice_[i]=a_[i];
    }
    }
    cursor_=0;generated+=n;++refills;
    prepare_ms+=std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-start).count();
  }
public:
  uint64_t generated=0,consumed=0,refills=0,random_ots=0,extended_random_ots=0;double prepare_ms=0;
  BatchedAnd(FPMath& math,sci::PRG128& rng,int flavor,bool prefix,size_t minimum=4096):math_(math),rng_(rng),flavor_(flavor),minimum_(minimum) {
    gate_require(flavor>=1 && flavor<=4);low_depth=prefix;
  }
  void reserve(size_t operations) {if(cursor_+operations>a_.size()) refill(operations);}
  void set_provider(TripleProvider* provider) {gate_require(generated==0);provider_=provider;}
  void prepare_words() {
    gate_require(flavor_!=2 && cursor_==0 && !a_.empty());
    const auto start=std::chrono::steady_clock::now();
    packed_a_.assign((a_.size()+63)/64,0);packed_b_=packed_a_;packed_c_=packed_a_;
    gate_require(a_.size()%64==0);
    for(size_t i=0;i<a_.size();i+=64) {
      packed_a_[i/64]=pack_boolean64(a_.data()+i);
      packed_b_[i/64]=pack_boolean64(b_.data()+i);
      packed_c_[i/64]=pack_boolean64(c_.data()+i);
    }
    prepare_ms+=std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-start).count();
  }
  std::vector<uint64_t> multiply_words(const std::vector<uint64_t>& x,const std::vector<uint64_t>& y,size_t bits) {
    const size_t words=(bits+63)/64;
    gate_require(bits>0 && x.size()==words && y.size()==words && cursor_+bits<=a_.size() && !packed_a_.empty());
    const auto slice=[&](const std::vector<uint64_t>& tape,size_t word) {
      const size_t at=cursor_+64*word,index=at/64;const unsigned shift=unsigned(at%64);
      uint64_t result=tape[index]>>shift;
      if(shift && index+1<tape.size()) result|=tape[index+1]<<(64-shift);
      return result;
    };
    const uint64_t tail=bits%64 ? (uint64_t(1)<<(bits%64))-1:~uint64_t(0);
    std::vector<uint64_t> send(2*words),peer(send.size()),result(words);
    for(size_t i=0;i<words;++i) {
      const auto mask=i+1==words ? tail:~uint64_t(0);
      send[2*i]=(x[i]^slice(packed_a_,i))&mask;
      send[2*i+1]=(y[i]^slice(packed_b_,i))&mask;
    }
    auto* io=math_.iopack->io;
    if(math_.party==sci::ALICE) {io->send_data(send.data(),int(send.size()*8));io->flush();io->recv_data(peer.data(),int(peer.size()*8));}
    else {io->recv_data(peer.data(),int(peer.size()*8));io->send_data(send.data(),int(send.size()*8));io->flush();}
    for(size_t i=0;i<words;++i) {
      const auto d=send[2*i]^peer[2*i],e=send[2*i+1]^peer[2*i+1];
      result[i]=slice(packed_c_,i)^(d&slice(packed_b_,i))^(e&slice(packed_a_,i));
      if(math_.party==sci::ALICE) result[i]^=d&e;
    }
    result.back()&=tail;cursor_+=bits;consumed+=bits;return result;
  }
  BoolArray multiply(const BoolArray& x,const BoolArray& y) override {
    gate_require(x.party==math_.party && y.party==math_.party && x.size==y.size && x.size>0);
    const size_t n=x.size;if(cursor_+n>a_.size()) refill(n);
    std::vector<uint8_t> message(2*n);
    for(size_t i=0;i<n;++i) {
      const size_t j=cursor_+i;
      if(flavor_!=2) {message[2*i]=x.data[i]^a_[j];message[2*i+1]=y.data[i]^b_[j];}
      else {message[2*i]=x.data[i]^choice_[j];message[2*i+1]=rho_[j]^y.data[i];}
    }
    const auto opened=open_bits(math_,message);BoolArray result(math_.party,int(n));
    for(size_t i=0;i<n;++i) {
      const size_t j=cursor_+i;
      if(flavor_!=2) {
        const auto d=opened[2*i],e=opened[2*i+1];
        result.data[i]=c_[j]^(d&b_[j])^(e&a_[j])^((math_.party==sci::ALICE)&d&e);
      } else {
        // MOTION precomputed XOR-COT: both correction messages are independent.
        const auto peer_p=opened[2*i]^message[2*i];
        const auto peer_y=opened[2*i+1]^message[2*i+1];
        result.data[i]=(x.data[i]&y.data[i])^r0_[j]^(peer_p&rho_[j])^
                       selected_[j]^(x.data[i]&peer_y);
      }
    }
    cursor_+=n;consumed+=n;return result;
  }
};
class AndScope {
  AndProvider* old_;
public:
  explicit AndScope(AndProvider* provider):old_(active_and) {active_and=provider;}
  ~AndScope() {active_and=old_;}
};

// Precompute OT pads on independent random controls before the query arrives.
// Binding actual controls opens only d=s XOR a. Per-purpose pads remain disjoint.
class PreparedPadProducts:public ProductTape {
  FPMath& math_;int lanes_;std::vector<uint8_t> random_control_,difference_;
  std::unique_ptr<PadProducts> tape_;bool bound_=false;
public:
  PreparedPadProducts(FPMath& math,sci::PRG128& rng,size_t switches,int lanes):
      math_(math),lanes_(lanes),random_control_(switches) {
    random_bytes(rng,random_control_);
    for(auto& x:random_control_) x&=1;
    tape_=std::make_unique<PadProducts>(math,rng,random_control_,lanes);
  }
  void bind(const std::vector<uint8_t>& control) {
    gate_require(!bound_ && control.size()==random_control_.size());
    std::vector<uint8_t> masked(control.size());
    for(size_t i=0;i<control.size();++i) masked[i]=control[i]^random_control_[i];
    difference_=open_bits(math_,masked);bound_=true;
  }
  std::vector<uint64_t> apply(const std::vector<unsigned>& ids,const std::vector<uint64_t>& delta,int bits) override {
    gate_require(bound_);auto result=tape_->apply(ids,delta,bits);const auto mask=gate_mask(bits);
    for(size_t i=0;i<result.size();++i) {
      const uint64_t d=difference_[ids[i/lanes_]];
      result[i]=((uint64_t(1)-2*d)*result[i]+d*delta[i])&mask;
    }
    return result;
  }
  bool exhausted() const override {return bound_ && tape_->exhausted();}
};

// One random shared bit masks the SAME control for its vector gather/scatter.
// Independent vector masks in the arithmetic and Boolean domains, consumed once.
class MixedTripleProducts:public ProductTape {
  FPMath& math_;int lanes_;
  std::vector<uint8_t> bit_,d_,used_;
  std::vector<uint64_t> arith_,b_,c_,bb_,cb_;
public:
  MixedTripleProducts(FPMath& math,sci::PRG128& rng,const std::vector<uint8_t>& control,int lanes,bool direct=false):
      math_(math),lanes_(lanes),bit_(control.size()),used_(control.size(),0),
      b_(control.size()*lanes),bb_(b_.size()) {
    random_bytes(rng,bit_);BoolArray bits(math.party,int(bit_.size()));
    for(size_t i=0;i<bit_.size();++i) bits.data[i]=bit_[i]&=1;
    const auto a=math.fix->B2A(bits,false,21);arith_.assign(a.data,a.data+a.size);gate_flush(math);
    PadProducts generator(math,rng,bit_,lanes);
    if(direct) {
      auto arithmetic=generator.random_mask_products(21),binary=generator.random_mask_products(1);
      b_=std::move(arithmetic.first);c_=std::move(arithmetic.second);
      bb_=std::move(binary.first);cb_=std::move(binary.second);
    } else {
      std::vector<sci::block128> random((b_.size()+1)/2);rng.random_block(random.data(),int(random.size()));
      std::memcpy(b_.data(),random.data(),b_.size()*8);
      rng.random_block(random.data(),int(random.size()));std::memcpy(bb_.data(),random.data(),bb_.size()*8);
      for(size_t i=0;i<b_.size();++i) {b_[i]&=gate_mask(21);bb_[i]&=1;}
      std::vector<unsigned> ids(control.size());std::iota(ids.begin(),ids.end(),0);
      c_=generator.apply(ids,b_,21);cb_=generator.apply(ids,bb_,1);
    }
    gate_require(generator.exhausted());
    std::vector<uint8_t> local(control.size());
    for(size_t i=0;i<control.size();++i) local[i]=control[i]^bit_[i];
    d_=open_bits(math,local);
  }
  std::vector<uint64_t> apply(const std::vector<unsigned>& ids,const std::vector<uint64_t>& delta,int bits) override {
    gate_require(ids.size()*lanes_==delta.size() && (bits==1 || bits==21));
    const uint8_t use=bits==21 ? 1:2;const uint64_t mask=gate_mask(bits);
    const size_t bytes=bits==1 ? (delta.size()+7)/8:3*delta.size();
    std::vector<uint8_t> send(bytes,0),peer(bytes);std::vector<uint64_t> local(delta.size()),result(delta.size());
    for(size_t j=0;j<ids.size();++j) {
      const unsigned id=ids[j];gate_require(id<used_.size() && !(used_[id]&use));used_[id]|=use;
      for(int c=0;c<lanes_;++c) {
        const size_t p=j*lanes_+c,k=id*lanes_+c;
        local[p]=(delta[p]-(bits==21 ? b_[k]:bb_[k]))&mask;
        if(bits==1) send[p/8]|=uint8_t(local[p]<<(p%8));
        else for(int b=0;b<3;++b) send[3*p+b]=uint8_t(local[p]>>(8*b));
      }
    }
    if(math_.party==sci::ALICE) {
      math_.iopack->io->send_data(send.data(),int(bytes));math_.iopack->io->flush();math_.iopack->io->recv_data(peer.data(),int(bytes));
    } else {
      math_.iopack->io->recv_data(peer.data(),int(bytes));math_.iopack->io->send_data(send.data(),int(bytes));math_.iopack->io->flush();
    }
    for(size_t p=0;p<delta.size();++p) {
      uint64_t other=bits==1 ? ((peer[p/8]>>(p%8))&1):0;
      if(bits==21) for(int b=0;b<3;++b) other|=uint64_t(peer[3*p+b])<<(8*b);
      gate_require(other<=mask);const auto id=ids[p/lanes_];const size_t k=id*lanes_+p%lanes_;
      const uint64_t e=(local[p]+other)&mask;
      const uint64_t t=(bits==21 ? c_[k]+e*arith_[id]:cb_[k]+e*bit_[id]);
      result[p]=((uint64_t(1)-2*d_[id])*t+uint64_t(d_[id])*delta[p])&mask;
    }
    return result;
  }
  bool exhausted() const override {return std::all_of(used_.begin(),used_.end(),[](uint8_t x){return x==3;});}
};
} // namespace shared_residual
