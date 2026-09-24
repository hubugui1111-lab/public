// SPDX-License-Identifier: MIT
// Auxiliary gates only; no change to the frozen nonlinear backend.
#pragma once
#include "FloatingPoint/fp-math.h"
#include <algorithm>
#include <array>
#include <cstring>
#include <memory>
#include <stdexcept>
#include <utility>
#include <vector>

namespace shared_residual {
inline void gate_require(bool ok) {if(!ok) throw std::runtime_error("private gate invariant");}
inline uint64_t gate_mask(int bits) {return (uint64_t(1)<<bits)-1;}
inline void gate_flush(FPMath& math) {
  math.iopack->io->flush();math.iopack->io_rev->flush();math.iopack->io_GC->flush();
}

// (a0 XOR a1)*(b0 XOR b1) = a0*b0 XOR a1*b1 XOR a0*b1 XOR a1*b0.
// Two fresh bit COT batches share the cross terms, without a 16-way OT table.
struct AndProvider {
  bool low_depth=false;
  virtual BoolArray multiply(const BoolArray&,const BoolArray&)=0;
  virtual ~AndProvider()=default;
};
inline thread_local AndProvider* active_and=nullptr;

inline BoolArray bit_and(FPMath& math,const BoolArray& a,const BoolArray& b,bool fast) {
  if(fast && active_and) return active_and->multiply(a,b);
  if(!fast) return math.bool_op->AND(a,b);
  gate_require(a.party==math.party && b.party==math.party && a.size==b.size && a.size>0);
  const int n=a.size;
  std::vector<uint64_t> correlation(n),sent(n),received(n);
  std::unique_ptr<bool[]> choices(new bool[n]);
  for(int j=0;j<n;++j) {correlation[j]=b.data[j];choices[j]=a.data[j]!=0;}
  if(math.party==sci::ALICE) math.otpack->iknp_straight->send_cot(sent.data(),correlation.data(),n,1);
  else math.otpack->iknp_straight->recv_cot(received.data(),choices.get(),n,1);
  gate_flush(math);
  if(math.party==sci::BOB) math.otpack->iknp_reversed->send_cot(sent.data(),correlation.data(),n,1);
  else math.otpack->iknp_reversed->recv_cot(received.data(),choices.get(),n,1);
  gate_flush(math);
  BoolArray result(math.party,n);
  for(int j=0;j<n;++j) result.data[j]=uint8_t((sent[j]^received[j]^(a.data[j]&b.data[j]))&1);
  return result;
}

// One shared selection bit gates an entire XOR-shared word. Each direction
// sends fresh (R, R XOR local_word) messages; this is NOT arithmetic word COT.
inline BoolArray group_gate(FPMath& math,sci::PRG128& rng,const BoolArray& marks,
    const BoolArray& values,int lanes) {
  gate_require((lanes==1 || lanes==2 || lanes==4 || lanes==8) && values.size==marks.size*lanes);
  const int n=marks.size;gate_require(n>0);
  std::vector<sci::block128> random((n+15)/16);rng.random_block(random.data(),int(random.size()));
  const auto* bytes=reinterpret_cast<const uint8_t*>(random.data());
  std::vector<std::array<uint64_t,2>> messages(n);
  std::vector<uint64_t*> pointers(n);std::vector<uint64_t> selected(n),local(n,0);
  for(int j=0;j<n;++j) {
    for(int c=0;c<lanes;++c) local[j]|=uint64_t(values.data[j*lanes+c])<<c;
    messages[j][0]=uint64_t(bytes[j])&gate_mask(lanes);
    messages[j][1]=messages[j][0]^local[j];pointers[j]=messages[j].data();
  }
  if(math.party==sci::ALICE) math.otpack->iknp_straight->send(pointers.data(),n,lanes);
  else math.otpack->iknp_straight->recv(selected.data(),marks.data,n,lanes);
  gate_flush(math);
  if(math.party==sci::BOB) math.otpack->iknp_reversed->send(pointers.data(),n,lanes);
  else math.otpack->iknp_reversed->recv(selected.data(),marks.data,n,lanes);
  gate_flush(math);
  BoolArray result(math.party,values.size);
  for(int j=0;j<n;++j) {
    const uint64_t word=(local[j]&(0-uint64_t(marks.data[j])))^messages[j][0]^selected[j];
    for(int c=0;c<lanes;++c) result.data[j*lanes+c]=uint8_t((word>>c)&1);
  }
  return result;
}

// Decode two one-hot code shares against two SERVER-private 8-bit patterns.
// Pattern values never leave the sender except masked through fresh OT.
inline BoolArray decode_codes(FPMath& math,sci::PRG128& rng,
    const std::vector<uint16_t>& codes,const std::array<uint8_t,2>& patterns) {
  const int n=int(codes.size()),requests=2*n;gate_require(n>0);
  std::vector<uint64_t> selected(requests),local(n,0);
  std::vector<uint8_t> choices(requests);
  std::vector<std::array<uint64_t,2>> messages(requests);
  std::vector<uint64_t*> pointers(requests);
  std::vector<sci::block128> random((requests+15)/16);
  if(math.party==sci::ALICE) rng.random_block(random.data(),int(random.size()));
  const auto* bytes=reinterpret_cast<const uint8_t*>(random.data());
  for(int j=0;j<n;++j) for(int k=0;k<2;++k) {
    const int index=2*j+k;
    choices[index]=uint8_t((codes[j]>>k)&1);
    if(math.party==sci::ALICE) {
      messages[index][0]=bytes[index];messages[index][1]=bytes[index]^patterns[k];
      pointers[index]=messages[index].data();
      local[j]^=messages[index][0]^(uint64_t(patterns[k])&(0-uint64_t(choices[index])));
    }
  }
  if(math.party==sci::ALICE) math.otpack->iknp_straight->send(pointers.data(),requests,8);
  else math.otpack->iknp_straight->recv(selected.data(),choices.data(),requests,8);
  gate_flush(math);
  BoolArray result(math.party,8*n);
  for(int j=0;j<n;++j) {
    const uint64_t word=math.party==sci::ALICE ? local[j]:selected[2*j]^selected[2*j+1];
    for(int c=0;c<8;++c) result.data[8*j+c]=uint8_t((word>>c)&1);
  }
  return result;
}

// Shared ring words -> all XOR-shared bits using one batched private-owned
// generate step and a batched GMW ripple carry. Widths/shapes are PUBLIC.
inline uint64_t prefix_decompose_ands(const std::vector<int>& widths) {
  uint64_t result=0;
  for(int width:widths) {
    gate_require(width>=1 && width<=14);result+=width;
    for(int step=1;step<width-1;step*=2) result+=2*uint64_t(width-1-step);
  }
  return result;
}

inline std::vector<std::vector<uint8_t>> decompose(FPMath& math,
    const std::vector<uint64_t>& words,const std::vector<int>& widths) {
  gate_require(words.size()==widths.size());
  size_t total=0;int maximum=0;
  std::vector<size_t> offsets(words.size());
  for(size_t j=0;j<words.size();++j) {
    gate_require(widths[j]>=1 && widths[j]<=14);
    offsets[j]=total;total+=widths[j];maximum=std::max(maximum,widths[j]);
  }
  if(!total) return {};
  if(active_and && active_and->low_depth) {
    // Parallel prefix carry over PUBLIC widths. Never open a carry/operand.
    BoolArray left(math.party,int(total)),right(math.party,int(total));
    std::vector<uint8_t> original(total),prop(total);
    for(size_t j=0;j<words.size();++j) for(int bit=0;bit<widths[j];++bit) {
      const size_t pos=offsets[j]+bit;
      original[pos]=prop[pos]=uint8_t((words[j]>>bit)&1);
      left.data[pos]=math.party==sci::ALICE ? prop[pos]:0;
      right.data[pos]=math.party==sci::BOB ? prop[pos]:0;
    }
    auto gen=bit_and(math,left,right,true);
    for(int step=1;step<maximum-1;step*=2) {
      std::vector<size_t> ids;
      for(size_t j=0;j<words.size();++j)
        for(int bit=step;bit<widths[j]-1;++bit) ids.push_back(offsets[j]+bit);
      if(ids.empty()) continue;
      BoolArray a(math.party,int(2*ids.size())),b(math.party,int(2*ids.size()));
      for(size_t j=0;j<ids.size();++j) {
        const auto i=ids[j];a.data[2*j]=a.data[2*j+1]=prop[i];
        b.data[2*j]=gen.data[i-step];b.data[2*j+1]=prop[i-step];
      }
      const auto terms=bit_and(math,a,b,true);
      for(size_t j=0;j<ids.size();++j) {
        gen.data[ids[j]]^=terms.data[2*j];prop[ids[j]]=terms.data[2*j+1];
      }
    }
    std::vector<std::vector<uint8_t>> result(words.size());
    for(size_t j=0;j<words.size();++j) {
      result[j].resize(widths[j]);
      for(int bit=0;bit<widths[j];++bit)
        result[j][bit]=original[offsets[j]+bit]^(bit ? gen.data[offsets[j]+bit-1]:0);
    }
    return result;
  }
  std::vector<uint64_t> generate(total),correlation(total);
  std::vector<uint8_t> propagate(total),carry(words.size(),0);
  std::unique_ptr<bool[]> choices(new bool[total]);
  for(size_t j=0;j<words.size();++j) for(int bit=0;bit<widths[j];++bit) {
    const size_t pos=offsets[j]+bit;
    const uint8_t local=uint8_t((words[j]>>bit)&1);
    propagate[pos]=local;correlation[pos]=local;choices[pos]=local!=0;
  }
  if(math.party==sci::ALICE) math.otpack->iknp_straight->send_cot(generate.data(),correlation.data(),int(total),1);
  else math.otpack->iknp_straight->recv_cot(generate.data(),choices.get(),int(total),1);
  gate_flush(math);
  std::vector<std::vector<uint8_t>> result(words.size());
  for(size_t j=0;j<words.size();++j) result[j].resize(widths[j]);
  for(int bit=0;bit<maximum;++bit) {
    std::vector<size_t> next;
    for(size_t j=0;j<words.size();++j) if(bit<widths[j]) {
      result[j][bit]=propagate[offsets[j]+bit]^carry[j];
      if(bit+1<widths[j]) next.push_back(j);
    }
    if(next.empty()) continue;
    if(bit==0) {
      for(size_t j:next) carry[j]=uint8_t(generate[offsets[j]]&1);
      continue;
    }
    BoolArray p(math.party,int(next.size())),c(math.party,int(next.size()));
    for(size_t j=0;j<next.size();++j) {
      p.data[j]=propagate[offsets[next[j]]+bit];c.data[j]=carry[next[j]];
    }
    const auto term=bit_and(math,p,c,true);
    for(size_t j=0;j<next.size();++j) carry[next[j]]=uint8_t(generate[offsets[next[j]]+bit]&1)^term.data[j];
  }
  return result;
}

// A gate uses the SAME private control share in gather(21 bits) and scatter
// (1 bit). Each lane needs two independent pads totaling 22 bits. Up to four
// lanes fit directly in 128 bits; eight lanes use a fresh 128-bit PRG seed.
// Neither a pad bit nor its PRG position is reused across lanes/operations.
class ProductTape {
public:
  virtual std::vector<uint64_t> apply(const std::vector<unsigned>&,const std::vector<uint64_t>&,int)=0;
  virtual bool exhausted() const=0;
  virtual ~ProductTape()=default;
};

class PadProducts:public ProductTape {
  FPMath& math_;
  int lanes_;
  std::vector<uint8_t> choice_,used_;
  std::vector<uint64_t> pad0_,pad1_,selected_;
public:
  PadProducts(FPMath& math,sci::PRG128& rng,const std::vector<uint8_t>& control,int lanes=1):
      math_(math),lanes_(lanes),choice_(control),used_(control.size(),0),
      pad0_(control.size()*lanes),pad1_(control.size()*lanes),selected_(control.size()*lanes) {
    const int n=int(control.size());gate_require(n>0);
    gate_require(lanes==1 || lanes==2 || lanes==4 || lanes==8);
    for(auto value:choice_) gate_require(value<=1);
    if(lanes<=2) {
      std::vector<std::array<uint64_t,2>> pads(n);
      std::vector<uint64_t> selected(n);
      std::vector<sci::block128> random(n);rng.random_block(random.data(),n);
      std::vector<uint64_t*> messages(n);
      for(int j=0;j<n;++j) {
        std::memcpy(pads[j].data(),&random[j],16);
        pads[j][0]&=gate_mask(22*lanes);pads[j][1]&=gate_mask(22*lanes);messages[j]=pads[j].data();
      }
      if(math_.party==sci::ALICE) math_.otpack->iknp_straight->send(messages.data(),n,22*lanes);
      else math_.otpack->iknp_straight->recv(selected.data(),choice_.data(),n,22*lanes);
      gate_flush(math_);
      if(math_.party==sci::BOB) math_.otpack->iknp_reversed->send(messages.data(),n,22*lanes);
      else math_.otpack->iknp_reversed->recv(selected.data(),choice_.data(),n,22*lanes);
      gate_flush(math_);
      for(int j=0;j<n;++j) for(int c=0;c<lanes;++c) {
        pad0_[j*lanes+c]=(pads[j][0]>>(22*c))&gate_mask(22);
        pad1_[j*lanes+c]=(pads[j][1]>>(22*c))&gate_mask(22);
        selected_[j*lanes+c]=(selected[j]>>(22*c))&gate_mask(22);
      }
    } else {
      std::vector<sci::block128> first(n),second(n),selected(n);
      rng.random_block(first.data(),n);rng.random_block(second.data(),n);
      std::unique_ptr<bool[]> choices(new bool[n]);
      for(int j=0;j<n;++j) choices[j]=choice_[j]!=0;
      if(math_.party==sci::ALICE) math_.otpack->iknp_straight->send(first.data(),second.data(),n);
      else math_.otpack->iknp_straight->recv(selected.data(),choices.get(),n);
      gate_flush(math_);
      if(math_.party==sci::BOB) math_.otpack->iknp_reversed->send(first.data(),second.data(),n);
      else math_.otpack->iknp_reversed->recv(selected.data(),choices.get(),n);
      gate_flush(math_);
      const auto expand=[&](const sci::block128& source,uint64_t* destination) {
        std::array<sci::block128,2> blocks;
        if(lanes==4) blocks[0]=source;
        else {sci::PRG128 generator(&source);generator.random_block(blocks.data(),2);}
        std::array<uint32_t,8> words{};std::memcpy(words.data(),blocks.data(),4*lanes);
        for(int c=0;c<lanes;++c) destination[c]=uint64_t(words[c])&gate_mask(22);
      };
      for(int j=0;j<n;++j) {
        expand(first[j],pad0_.data()+j*lanes);expand(second[j],pad1_.data()+j*lanes);
        expand(selected[j],selected_.data()+j*lanes);
      }
    }
  }
  PadProducts(const PadProducts&)=delete;
  PadProducts& operator=(const PadProducts&)=delete;
  // Derive random mask/product shares instead of correcting to chosen data.
  // For Beaver preprocessing the caller MUST use fresh uniform choice shares.
  // b_i=(p1_i-p0_i)*(1-2*a_i), c_i=a_i*b_i+selected_i-p0_i.
  // Their sums satisfy c=(a_0 XOR a_1)*b. No correction message is needed.
  std::pair<std::vector<uint64_t>,std::vector<uint64_t>> random_mask_products(int bits) {
    gate_require(bits==21 || bits==1);
    const int shift=bits==21 ? 0:21;
    const uint8_t use=bits==21 ? 1:2;const uint64_t mask=gate_mask(bits);
    std::vector<uint64_t> b(pad0_.size()),c(b.size());
    for(size_t id=0;id<choice_.size();++id) {
      gate_require(!(used_[id]&use));used_[id]|=use;
      const uint64_t a=choice_[id];
      for(int lane=0;lane<lanes_;++lane) {
        const size_t k=id*lanes_+lane;
        const uint64_t p0=(pad0_[k]>>shift)&mask,p1=(pad1_[k]>>shift)&mask;
        b[k]=((p1-p0)*(uint64_t(1)-2*a))&mask;
        c[k]=(a*b[k]+((selected_[k]>>shift)&mask)-p0)&mask;
      }
    }
    return {std::move(b),std::move(c)};
  }
  std::vector<uint64_t> apply(const std::vector<unsigned>& ids,const std::vector<uint64_t>& delta,int bits) {
    gate_require(ids.size()*lanes_==delta.size() && (bits==21 || bits==1));
    const int shift=bits==21 ? 0:21;
    const uint8_t use=bits==21 ? 1:2;
    const uint64_t mask=gate_mask(bits);
    const size_t bytes=bits==1 ? (delta.size()+7)/8:3*delta.size();
    std::vector<uint8_t> send(bytes,0),received(bytes);
    std::vector<uint64_t> result(delta.size());
    for(size_t j=0;j<ids.size();++j) {
      const auto id=ids[j];gate_require(id<choice_.size() && !(used_[id]&use));used_[id]|=use;
      for(int c=0;c<lanes_;++c) {
        const size_t pos=j*lanes_+c,stored=id*lanes_+c;
        const uint64_t p0=(pad0_[stored]>>shift)&mask,p1=(pad1_[stored]>>shift)&mask;
        const uint64_t corr=(delta[pos]*(uint64_t(1)-2*uint64_t(choice_[id]))+p0-p1)&mask;
        if(bits==1) send[pos/8]|=uint8_t(corr<<(pos%8));
        else for(int b=0;b<3;++b) send[3*pos+b]=uint8_t(corr>>(8*b));
        result[pos]=(uint64_t(choice_[id])*delta[pos]+((selected_[stored]>>shift)&mask)-p0)&mask;
      }
    }
    auto* channel=math_.iopack->io;
    if(math_.party==sci::ALICE) {
      channel->send_data(send.data(),int(bytes));channel->flush();channel->recv_data(received.data(),int(bytes));
    } else {
      channel->recv_data(received.data(),int(bytes));channel->send_data(send.data(),int(bytes));channel->flush();
    }
    for(size_t j=0;j<delta.size();++j) {
      uint64_t value=bits==1 ? ((received[j/8]>>(j%8))&1):0;
      if(bits!=1) for(int b=0;b<3;++b) value|=uint64_t(received[3*j+b])<<(8*b);
      gate_require(value<=mask);
      result[j]=(result[j]+uint64_t(choice_[ids[j/lanes_]])*value)&mask;
    }
    return result;
  }
  bool exhausted() const {return std::all_of(used_.begin(),used_.end(),[](uint8_t x){return x==3;});}
};
} // namespace shared_residual
