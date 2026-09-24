#pragma once
#include "FloatingPoint/fp-math.h"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <stdexcept>
#include <vector>

namespace exp252 {

inline void require(bool x){ if(!x) throw std::runtime_error("exp198 leaf lookup invariant"); }
inline void flush_all(FPMath& math){
  math.iopack->io->flush(); math.iopack->io_rev->flush(); math.iopack->io_GC->flush();
}

struct LeafLookupResult {
  std::vector<uint64_t> bound_shares; // additive mod 2^ell
  std::vector<uint8_t> sign_shares;   // XOR shares
  uint64_t online_bytes=0,online_rounds=0;
  double online_ms=0;
};

// One prepared shared-index 1-out-of-16 lookup.
// ALICE holds the fixed leaf table and an XOR share a of the leaf index.
// BOB holds XOR share b. True leaf = a XOR b.
// Online BOB sends e=b XOR rho. ALICE maps transmitted semantic slot s
// to model row (s XOR a), while using prepared OT seed (s XOR e).
// BOB opens only slot b with seed rho, obtaining row a XOR b.
// The real leaf is never opened to either party.
//
// Bound words are returned as additive 24-bit shares directly:
// ALICE keeps random R_i, BOB receives bound_i-R_i.
// Sign bits are returned as XOR shares:
// ALICE keeps random r_i, BOB receives sign_i XOR r_i.
class PreparedSharedLeafLookup16Wide {
  FPMath& math_;
  sci::PRG128& rng_;
  int n_,ell_;
  uint64_t mask_;
  size_t bound_bytes_,sign_bytes_,payload_bytes_;
  std::vector<sci::block128> sender_seeds_;
  sci::block128 receiver_seed_{};
  uint8_t rho_=0;
  std::vector<uint64_t> bound_mask_;
  std::vector<uint8_t> sign_mask_;
  std::vector<uint8_t> masked_rows_;
  bool used_=false;
 public:
  double prepare_ms=0;
  uint64_t prepare_bytes=0,prepare_rounds=0;

  PreparedSharedLeafLookup16Wide(FPMath& math,sci::PRG128& rng,int n,int ell,
      const std::vector<uint64_t>& clear_bounds,
      const std::vector<uint8_t>& clear_signs)
      :math_(math),rng_(rng),n_(n),ell_(ell),
       mask_((uint64_t(1)<<ell)-1),bound_bytes_((size_t(ell)+7)/8),
       sign_bytes_((size_t(n)+7)/8),payload_bytes_(bound_bytes_*size_t(n)+sign_bytes_) {
    require(n_>0 && ell_>0 && ell_<=56);
    if(math_.party==sci::ALICE){
      require(clear_bounds.size()==size_t(16*n_));
      require(clear_signs.size()==size_t(16*n_));
    }else{
      require(clear_bounds.empty() && clear_signs.empty());
    }

    auto b0=math_.iopack->get_comm(),r0=math_.iopack->get_rounds();
    auto t0=std::chrono::steady_clock::now();

    // Model-dependent masked rows are local preprocessing.
    if(math_.party==sci::ALICE){
      bound_mask_.resize(n_);
      std::vector<sci::block128> tmp((size_t(n_)*8+15)/16);
      rng_.random_block(tmp.data(),int(tmp.size()));
      std::memcpy(bound_mask_.data(),tmp.data(),size_t(n_)*8);
      for(auto& x:bound_mask_) x&=mask_;
      sign_mask_.resize(n_);
      tmp.resize((size_t(n_)+15)/16);
      rng_.random_block(tmp.data(),int(tmp.size()));
      std::memcpy(sign_mask_.data(),tmp.data(),size_t(n_));
      for(auto& x:sign_mask_) x&=1;

      masked_rows_.assign(size_t(16)*payload_bytes_,0);
      for(int row=0;row<16;++row){
        auto* dst=masked_rows_.data()+size_t(row)*payload_bytes_;
        for(int i=0;i<n_;++i){
          uint64_t v=(clear_bounds[size_t(row)*n_+i]-bound_mask_[i])&mask_;
          for(size_t bb=0;bb<bound_bytes_;++bb) dst[bound_bytes_*size_t(i)+bb]=uint8_t(v>>(8*bb));
        }
        auto* sb=dst+bound_bytes_*size_t(n_);
        for(int i=0;i<n_;++i){
          const uint8_t bit=(clear_signs[size_t(row)*n_+i]^sign_mask_[i])&1;
          sb[size_t(i)/8]|=uint8_t(bit<<(i%8));
        }
      }
    }

    // One random prepared 1-out-of-16 OT seed.
    auto* ot=math_.otpack->kkot[3];
    require(ot->N==16 && ot->precomp_batch_size==0);
    if(math_.party==sci::ALICE){
      ot->send_pre(1);
      flush_all(math_);
      std::vector<sci::block256> keys(16);
      sender_seeds_.resize(16);
      for(int k=0;k<16;++k) keys[k]=sci::xorBlocks(ot->qT[0],ot->c_AND_s[k]);
      sci::CCRF(sender_seeds_.data(),keys.data(),16);
      delete[] ot->qT; ot->qT=nullptr;
    }else{
      std::array<uint8_t,16> rb{};
      sci::block128 block; rng_.random_block(&block,1);
      std::memcpy(rb.data(),&block,16);
      rho_=rb[0]&15;
      uint8_t choice=rho_;
      ot->recv_pre(&choice,1);
      flush_all(math_);
      sci::CCRF(&receiver_seed_,ot->tT,1);
      delete[] ot->tT; ot->tT=nullptr;
    }

    prepare_bytes=math_.iopack->get_comm()-b0;
    prepare_rounds=math_.iopack->get_rounds()-r0;
    prepare_ms=std::chrono::duration<double,std::milli>(
      std::chrono::steady_clock::now()-t0).count();
  }

  LeafLookupResult query(uint8_t index_share){
    require(!used_ && index_share<16); used_=true;
    auto b0=math_.iopack->get_comm(),r0=math_.iopack->get_rounds();
    auto t0=std::chrono::steady_clock::now();

    uint8_t correction=0;
    if(math_.party==sci::BOB){
      correction=uint8_t(index_share^rho_);
      math_.iopack->io->send_data(&correction,1); math_.iopack->io->flush();
    }else{
      math_.iopack->io->recv_data(&correction,1);
    }

    const size_t blocks=(payload_bytes_+15)/16;
    std::vector<uint8_t> ciphertext(size_t(16)*payload_bytes_);
    LeafLookupResult out;
    if(math_.party==sci::ALICE){
      std::vector<sci::block128> stream(blocks);
      for(int semantic=0;semantic<16;++semantic){
        const int source=semantic^int(index_share);
        const int prepared=semantic^int(correction);
        sci::PRG128 gen(&sender_seeds_[prepared]);
        gen.random_block(stream.data(),int(blocks));
        const auto* pad=reinterpret_cast<const uint8_t*>(stream.data());
        const auto* src=masked_rows_.data()+size_t(source)*payload_bytes_;
        auto* dst=ciphertext.data()+size_t(semantic)*payload_bytes_;
        for(size_t b=0;b<payload_bytes_;++b) dst[b]=src[b]^pad[b];
      }
      math_.iopack->io->send_data(ciphertext.data(),int(ciphertext.size()));
      math_.iopack->io->flush();
      out.bound_shares=bound_mask_;
      out.sign_shares=sign_mask_;
    }else{
      math_.iopack->io->recv_data(ciphertext.data(),int(ciphertext.size()));
      std::vector<sci::block128> stream(blocks);
      sci::PRG128 gen(&receiver_seed_); gen.random_block(stream.data(),int(blocks));
      const auto* pad=reinterpret_cast<const uint8_t*>(stream.data());
      const auto* src=ciphertext.data()+size_t(index_share)*payload_bytes_;
      std::vector<uint8_t> clear(payload_bytes_);
      for(size_t b=0;b<payload_bytes_;++b) clear[b]=src[b]^pad[b];
      out.bound_shares.resize(n_);
      for(int i=0;i<n_;++i){
        uint64_t v=0; for(size_t bb=0;bb<bound_bytes_;++bb) v|=(uint64_t(clear[bound_bytes_*size_t(i)+bb])<<(8*bb)); out.bound_shares[i]=v&mask_;
      }
      out.sign_shares.resize(n_);
      const auto* sb=clear.data()+bound_bytes_*size_t(n_);
      for(int i=0;i<n_;++i) out.sign_shares[i]=uint8_t((sb[size_t(i)/8]>>(i%8))&1);
    }

    flush_all(math_);
    out.online_bytes=math_.iopack->get_comm()-b0;
    out.online_rounds=math_.iopack->get_rounds()-r0;
    out.online_ms=std::chrono::duration<double,std::milli>(
      std::chrono::steady_clock::now()-t0).count();
    return out;
  }
};

inline uint8_t leaf_index_share_from_onehot(const BoolArray& onehot){
  require(onehot.size==16);
  uint8_t idx=0;
  for(int bit=0;bit<4;++bit){
    uint8_t b=0;
    for(int l=0;l<16;++l) if((l>>bit)&1) b^=onehot.data[l];
    idx|=uint8_t((b&1)<<bit);
  }
  return idx;
}

} // namespace exp252
