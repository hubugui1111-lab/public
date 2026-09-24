// Experimental width adapter for the existing prepared PadProducts algebra.
// Two independent 24-bit mask slices per switch, one for gather, one for scatter.
#pragma once
#include "batched_material.h"
namespace shared_residual {
class PreparedMovement24 : public ProductTape {
  FPMath& math_;std::vector<uint8_t> r_,difference_,used_;bool bound_=false;
  std::vector<sci::block128> p0_,p1_,selected_;
  static constexpr uint64_t mask=(uint64_t(1)<<24)-1;
  static uint64_t slice(const sci::block128& b,int use){
    std::array<uint8_t,16> bytes;std::memcpy(bytes.data(),&b,16);uint64_t v=0;
    for(int j=0;j<3;++j)v|=uint64_t(bytes[use*3+j])<<(8*j);return v;
  }
public:
  PreparedMovement24(FPMath& math,sci::PRG128& rng,size_t n):math_(math),r_(n),used_(n,0),p0_(n),p1_(n),selected_(n){
    gate_require(n>0 && n<=size_t(INT32_MAX));random_bytes(rng,r_);std::unique_ptr<bool[]> choices(new bool[n]);
    for(size_t i=0;i<n;++i){r_[i]&=1;choices[i]=r_[i];}
    rng.random_block(p0_.data(),int(n));rng.random_block(p1_.data(),int(n));
    if(math.party==sci::ALICE)math.otpack->iknp_straight->send(p0_.data(),p1_.data(),int(n));
    else math.otpack->iknp_straight->recv(selected_.data(),choices.get(),int(n));gate_flush(math);
    if(math.party==sci::BOB)math.otpack->iknp_reversed->send(p0_.data(),p1_.data(),int(n));
    else math.otpack->iknp_reversed->recv(selected_.data(),choices.get(),int(n));gate_flush(math);
  }
  void bind(const std::vector<uint8_t>& control){
    gate_require(!bound_ && control.size()==r_.size());std::vector<uint8_t> x(control.size());
    for(size_t i=0;i<x.size();++i){gate_require(control[i]<=1);x[i]=control[i]^r_[i];}
    difference_=open_bits(math_,x);bound_=true;
  }
  std::vector<uint64_t> apply(const std::vector<unsigned>& ids,const std::vector<uint64_t>& delta,int bits) override{
    gate_require(bound_ && bits==24 && ids.size()==delta.size());std::vector<uint8_t> send(ids.size()*3),recv(send.size());std::vector<uint64_t> result(ids.size());
    for(size_t j=0;j<ids.size();++j){unsigned id=ids[j];gate_require(id<r_.size()&&used_[id]<2);int use=used_[id]++;
      uint64_t a=slice(p0_[id],use),b=slice(p1_[id],use),s=slice(selected_[id],use);
      uint64_t correction=(delta[j]*(uint64_t(1)-2*r_[id])+a-b)&mask;
      for(int k=0;k<3;++k)send[j*3+k]=uint8_t(correction>>(8*k));result[j]=(r_[id]*delta[j]+s-a)&mask;
    }
    if(math_.party==sci::ALICE){math_.iopack->io->send_data(send.data(),send.size());math_.iopack->io->flush();math_.iopack->io->recv_data(recv.data(),recv.size());}
    else{math_.iopack->io->recv_data(recv.data(),recv.size());math_.iopack->io->send_data(send.data(),send.size());math_.iopack->io->flush();}
    for(size_t j=0;j<ids.size();++j){uint64_t value=0;for(int k=0;k<3;++k)value|=uint64_t(recv[j*3+k])<<(8*k);unsigned id=ids[j];
      uint64_t product=(result[j]+r_[id]*value)&mask,d=difference_[id];result[j]=((uint64_t(1)-2*d)*product+d*delta[j])&mask;}
    return result;
  }
  bool exhausted()const override{return bound_&&std::all_of(used_.begin(),used_.end(),[](uint8_t u){return u==2;});}
};
}
