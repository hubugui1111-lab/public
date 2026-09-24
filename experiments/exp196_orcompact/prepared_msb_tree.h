// Sign-only balanced carry reduction over additive shares; no native ReLU edit.
#pragma once
#include "batched_material.h"
namespace shared_residual {
inline uint64_t msb_ripple_ands(size_t n,int width) {
  gate_require(width>=2 && width<=48);return n*(width-1);
}
// Same ripple circuit and fresh triple cursor, evaluated in packed words.
inline BoolArray prepared_nonnegative_ripple_words(FPMath& math,BatchedAnd& engine,
    const std::vector<uint64_t>& shares,int width) {
  const size_t n=shares.size(),words=(n+63)/64;
  gate_require(n>0 && width>=2 && width<=48);
  std::vector<uint64_t> carry(words,0),p(words),ac(words);
  for(int bit=0;bit<width-1;++bit) {
    std::fill(p.begin(),p.end(),0);
    for(size_t j=0;j<n;++j)p[j/64]|=((shares[j]>>bit)&1)<<(j%64);
    for(size_t j=0;j<words;++j)ac[j]=carry[j]^(math.party==sci::ALICE?p[j]:0);
    carry=engine.multiply_words(p,ac,n);
    if(math.party==sci::ALICE)for(size_t j=0;j<words;++j)carry[j]^=p[j];
  }
  BoolArray result(math.party,int(n));
  for(size_t j=0;j<n;++j)result.data[j]=uint8_t((carry[j/64]>>(j%64))&1)^uint8_t((shares[j]>>(width-1))&1)^uint8_t(math.party==sci::ALICE);
  return result;
}
inline BoolArray prepared_nonnegative_ripple(FPMath& math,BatchedAnd& engine,
    const std::vector<uint64_t>& shares,int width) {
  const int n=int(shares.size());gate_require(n>0 && width>=2 && width<=48);
  BoolArray carry(math.party,n);std::fill(carry.data,carry.data+n,0);
  for(int bit=0;bit<width-1;++bit) {
    BoolArray p(math.party,n),ac(math.party,n);
    for(int j=0;j<n;++j) {
      uint8_t v=(shares[j]>>bit)&1,a=math.party==sci::ALICE?v:0;
      p.data[j]=v;ac.data[j]=a^carry.data[j];
    }
    carry=engine.multiply(p,ac);
    if(math.party==sci::ALICE)for(int j=0;j<n;++j)carry.data[j]^=uint8_t((shares[j]>>bit)&1);
  }
  for(int j=0;j<n;++j)carry.data[j]^=uint8_t((shares[j]>>(width-1))&1)^uint8_t(math.party==sci::ALICE);
  return carry;
}
inline uint64_t msb_tree_ands(size_t n,int width) {
  gate_require(width>=2 && width<=48);return n*(3*(width-1)-2);
}
inline BoolArray prepared_nonnegative(FPMath& math,BatchedAnd& engine,
    const std::vector<uint64_t>& shares,int width) {
  const int n=int(shares.size());gate_require(n>0 && width>=2 && width<=48);
  int segments=width-1;BoolArray left(math.party,n*segments),right(math.party,n*segments),prop(math.party,n*segments);
  for(int bit=0;bit<segments;++bit)for(int j=0;j<n;++j) {
    const uint8_t v=(shares[j]>>bit)&1;const int at=bit*n+j;
    left.data[at]=math.party==sci::ALICE?v:0;right.data[at]=math.party==sci::BOB?v:0;prop.data[at]=v;
  }
  auto gen=engine.multiply(left,right);
  while(segments>1) {
    const int pairs=segments/2,next=(segments+1)/2;
    BoolArray a(math.party,2*pairs*n),b(math.party,2*pairs*n);
    for(int pair=0;pair<pairs;++pair)for(int j=0;j<n;++j) {
      const int low=2*pair*n+j,high=low+n,at=2*(pair*n+j);
      a.data[at]=a.data[at+1]=prop.data[high];b.data[at]=gen.data[low];b.data[at+1]=prop.data[low];
    }
    auto products=engine.multiply(a,b);BoolArray ng(math.party,next*n),np(math.party,next*n);
    for(int pair=0;pair<pairs;++pair)for(int j=0;j<n;++j) {
      const int at=2*(pair*n+j);ng.data[pair*n+j]=gen.data[(2*pair+1)*n+j]^products.data[at];np.data[pair*n+j]=products.data[at+1];
    }
    if(segments%2)for(int j=0;j<n;++j){ng.data[(next-1)*n+j]=gen.data[(segments-1)*n+j];np.data[(next-1)*n+j]=prop.data[(segments-1)*n+j];}
    gen=std::move(ng);prop=std::move(np);segments=next;
  }
  BoolArray result(math.party,n);
  for(int j=0;j<n;++j)result.data[j]=uint8_t((shares[j]>>(width-1))&1)^gen.data[j]^uint8_t(math.party==sci::ALICE);
  return result;
}
}
