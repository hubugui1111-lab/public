// SPDX-License-Identifier: MIT
// Shared-mark translation of the corrected ORCompact control formulas.
// No marks, ranks, offsets, switch bits, or partial counts are opened.
#pragma once
#include "FloatingPoint/fp-math.h"
#include "orcompact_scatter.h"
#include "private_gates.h"
#include <algorithm>
#include <functional>
#include <stdexcept>
#include <vector>

namespace shared_residual {
inline void require(bool ok) {if(!ok) throw std::runtime_error("shared control invariant");}
inline uint64_t bitmask(int bits) {return (uint64_t(1)<<bits)-1;}
inline int log2ceil(unsigned n) {int b=0;while((1U<<b)<n) ++b;return b;}

struct Prefix {
  int bits;
  std::vector<uint64_t> sums;
};

inline Prefix prefix(FPMath& math,const BoolArray& marks) {
  Prefix result{log2ceil(unsigned(marks.size)+1)+1,std::vector<uint64_t>(marks.size+1,0)};
  auto counts=math.fix->B2A(marks,false,result.bits);
  for(int i=0;i<marks.size;++i) result.sums[i+1]=(result.sums[i]+counts.data[i])&bitmask(result.bits);
  return result;
}

inline bool accepted(FPMath& math,const Prefix& counts,int capacity,bool buffered=false) {
  FixArray diff(math.party,1,true,counts.bits,0);
  diff.data[0]=((math.party==sci::ALICE ? uint64_t(capacity):0)-counts.sums.back())&bitmask(counts.bits);
  if(buffered) {
    // Native comparison/open routines exchange in both directions before
    // joining; they assume unbuffered streams. Keep the original backend intact
    // and use our explicitly flushed auxiliary adder/open instead.
    const auto bits=decompose(math,{diff.data[0]},{counts.bits});
    const uint8_t mine=bits[0].back()^uint8_t(math.party==sci::ALICE);
    uint8_t peer=0;
    auto* channel=math.iopack->io;
    if(math.party==sci::ALICE) {
      channel->send_data(&mine,1);channel->flush();channel->recv_data(&peer,1);
    } else {
      channel->recv_data(&peer,1);channel->send_data(&mine,1);channel->flush();
    }
    require(peer<=1);
    return (mine^peer)!=0;
  }
  const auto inside=math.bool_op->NOT(math.fix->MSB(diff));
  // This is the only production opening in the entire query.
  return math.bool_op->output(sci::PUBLIC,inside).data[0]!=0;
}

inline std::vector<uint8_t> compile(FPMath& math,const h0_orcompact::Plan& plan,
                                    const BoolArray& marks,const Prefix& counts,bool fused_wrap=false,int gates=0,bool prune=false,
                                    uint64_t* planned_ands=nullptr) {
  require(marks.size==int(plan.features()) && counts.sums.size()==size_t(marks.size+1));
  const uint8_t one=uint8_t(math.party==sci::ALICE);
  struct Node {
    unsigned span,outputs,base,parent_width;
    uint64_t value,offset,marked;
    uint8_t wrap=0;
    std::vector<uint8_t> bits,thermometer;
  };
  struct Leaf {unsigned start,id;uint8_t offset;};
  std::vector<Node> nodes;
  std::vector<Leaf> leaves;
  unsigned next=0;
  const auto count=[&](unsigned start,unsigned size) {return counts.sums[start+size]-counts.sums[start];};
  std::function<void(unsigned,unsigned,uint64_t)> offset;
  offset=[&](unsigned start,unsigned size,uint64_t o) {
    if(size<=1) return;
    o&=size-1;
    if(size==2) {leaves.push_back({start,next++,uint8_t(o)});return;}
    const unsigned half=size/2;
    const uint64_t m=count(start,half);
    offset(start,half,o);
    offset(start+half,half,o+m);
    Node node{half,half,next,unsigned(log2ceil(size)),(o+m)&(fused_wrap ? size-1:half-1),o,m&(size-1)};
    nodes.push_back(std::move(node));next+=half;
  };
  std::function<void(unsigned,unsigned)> compact;
  compact=[&](unsigned start,unsigned size) {
    if(!size) return;
    unsigned power=1;while(power<=size/2) power*=2;
    const unsigned rest=size-power;
    const uint64_t m=count(start,rest);
    compact(start,rest);
    offset(start+rest,power,m+(math.party==sci::ALICE ? power-rest:0));
    if(rest) {
      const unsigned span=1U<<log2ceil(rest+1);
      Node node{span,rest,next,0,m&(span-1),0,0};
      nodes.push_back(std::move(node));next+=rest;
    }
  };
  compact(0,plan.features());
  require(next==plan.full_switch_count());
  std::vector<uint8_t> controls(next,0);
  if(prune) {
    // These nodes depend directly on local linear combinations of prefix shares,
    // not on other control outputs. Prune only PUBLIC unused output ranges.
    std::vector<unsigned> kept(next+1,0);
    for(unsigned id:plan.kept_control_ids()) kept[id+1]=1;
    for(size_t i=1;i<kept.size();++i) kept[i]+=kept[i-1];
    nodes.erase(std::remove_if(nodes.begin(),nodes.end(),[&](const Node& n){
      return kept[n.base+n.outputs]==kept[n.base];}),nodes.end());
    leaves.erase(std::remove_if(leaves.begin(),leaves.end(),[&](const Leaf& n){
      return kept[n.id+1]==kept[n.id];}),leaves.end());
  }

  // Wrap extraction in the PARENT ring. Never lift child-ring shares naively.
  for(int width=2;!fused_wrap && width<=log2ceil(plan.features());++width) {
    std::vector<size_t> ids;
    for(size_t j=0;j<nodes.size();++j) if(nodes[j].parent_width==unsigned(width)) ids.push_back(j);
    if(ids.empty()) continue;
    FixArray values(math.party,int(ids.size()),true,width,0);
    for(size_t j=0;j<ids.size();++j) values.data[j]=nodes[ids[j]].offset;
    const auto high=math.fix->MSB(values);
    for(size_t j=0;j<ids.size();++j) {
      auto& node=nodes[ids[j]];
      values.data[j]=(node.offset-uint64_t(node.span)*high.data[j]+node.marked)&bitmask(width);
    }
    const auto carry=math.fix->MSB(values);
    for(size_t j=0;j<ids.size();++j) nodes[ids[j]].wrap=high.data[j]^carry.data[j];
  }

  // Bit-decompose only the small shared boundaries, grouping public widths.
  for(auto& node:nodes) {
    node.bits.resize(log2ceil(node.span)+int(fused_wrap && node.parent_width));
    node.thermometer={one};
  }
  if(planned_ands) {
    require(fused_wrap && gates>=2 && prune);
    std::vector<int> widths;uint64_t count=leaves.size();
    const auto pair_tree_ands=[](int w) {
      if(w<=1) return uint64_t(0);
      std::vector<uint64_t> sizes(size_t(w/2),4);
      if(w&1) sizes.push_back(2);
      uint64_t total=uint64_t(w/2);
      while(sizes.size()>1) {
        std::vector<uint64_t> next;
        for(size_t i=0;i<sizes.size();i+=2) {
          if(i+1<sizes.size()) {total+=sizes[i]*sizes[i+1];next.push_back(sizes[i]*sizes[i+1]);}
          else next.push_back(sizes[i]);
        }
        sizes=std::move(next);
      }
      return total;
    };
    for(const auto& node:nodes) {
      widths.push_back(int(node.bits.size()));
      count+=gates>=3 ? pair_tree_ands(log2ceil(node.span)) : uint64_t(node.span-2);
    }
    *planned_ands=count+prefix_decompose_ands(widths);
    return {};
  }
  if(gates>=2 && !nodes.empty()) {
    require(fused_wrap);
    std::vector<uint64_t> values;std::vector<int> widths;
    for(const auto& node:nodes) {values.push_back(node.value);widths.push_back(int(node.bits.size()));}
    auto decomposed=decompose(math,values,widths);
    for(size_t j=0;j<nodes.size();++j) nodes[j].bits=std::move(decomposed[j]);
  }
  for(int bit=0;gates<2 && bit<log2ceil(plan.features());++bit) {
    std::vector<size_t> ids;
    for(size_t j=0;j<nodes.size();++j) if(int(nodes[j].bits.size())>bit) ids.push_back(j);
    if(ids.empty()) continue;
    if(bit==0) {
      for(size_t j:ids) nodes[j].bits[0]=uint8_t(nodes[j].value&1);
    } else {
      FixArray projected(math.party,int(ids.size()),true,bit+1,0);
      for(size_t j=0;j<ids.size();++j) projected.data[j]=nodes[ids[j]].value&bitmask(bit+1);
      const auto bits=math.fix->MSB(projected);
      for(size_t j=0;j<ids.size();++j) nodes[ids[j]].bits[bit]=bits.data[j];
    }
  }

  // In Z_(2h), adding h*MSB(o) flips exactly the high bit. Hence the
  // original wrap equals MSB((o+m) mod 2h); lower bits are the boundary.
  if(fused_wrap) for(auto& node:nodes) if(node.parent_width) node.wrap=node.bits.back();


  // Optional lower-depth thermometer compiler (gates>=3).
  //
  // The original recurrence consumes one secret boundary bit per interactive
  // level.  Here we first decode every 2-bit chunk into a 4-way one-hot with
  // one AND, then combine adjacent chunk one-hots with a balanced Cartesian-
  // product tree.  All products at one tree level are batched in one bit_and.
  // The final one-hot is converted to the identical thermometer [i >= value]
  // by local prefix XOR.  This changes only Boolean circuit scheduling, never
  // the represented boundary/control bits.
  if(gates>=3 && !nodes.empty()) {
    struct Group { std::vector<uint8_t> v; };
    std::vector<std::vector<Group>> groups(nodes.size());

    size_t pair_products=0;
    for(const auto& node:nodes) pair_products+=log2ceil(node.span)/2;
    if(pair_products) {
      BoolArray a(math.party,int(pair_products)),b(math.party,int(pair_products));
      size_t pos=0;
      for(const auto& node:nodes) {
        const int w=log2ceil(node.span);
        for(int bit=0;bit+1<w;bit+=2) {
          a.data[pos]=node.bits[bit];
          b.data[pos]=node.bits[bit+1];
          ++pos;
        }
      }
      const auto products=bit_and(math,a,b,true);
      pos=0;
      for(size_t j=0;j<nodes.size();++j) {
        const int w=log2ceil(nodes[j].span);
        for(int bit=0;bit+1<w;bit+=2) {
          const uint8_t x=nodes[j].bits[bit],y=nodes[j].bits[bit+1],t=products.data[pos++];
          Group g;g.v.resize(4);
          // Index is x + 2*y (little-endian within the 2-bit chunk).
          g.v[0]=one^x^y^t;
          g.v[1]=x^t;
          g.v[2]=y^t;
          g.v[3]=t;
          groups[j].push_back(std::move(g));
        }
        if(w&1) {
          const uint8_t x=nodes[j].bits[w-1];
          Group g;g.v={uint8_t(one^x),x};
          groups[j].push_back(std::move(g));
        }
        require(!groups[j].empty());
      }
    } else {
      for(size_t j=0;j<nodes.size();++j) {
        const int w=log2ceil(nodes[j].span);
        require(w==1);
        const uint8_t x=nodes[j].bits[0];
        Group g;g.v={uint8_t(one^x),x};
        groups[j].push_back(std::move(g));
      }
    }

    while(true) {
      bool any=false;size_t total=0;
      for(const auto& gs:groups) {
        if(gs.size()>1) any=true;
        for(size_t k=0;k+1<gs.size();k+=2) total+=gs[k].v.size()*gs[k+1].v.size();
      }
      if(!any) break;
      require(total>0);
      BoolArray a(math.party,int(total)),b(math.party,int(total));
      size_t pos=0;
      for(const auto& gs:groups) for(size_t k=0;k+1<gs.size();k+=2) {
        const auto& low=gs[k].v;const auto& high=gs[k+1].v;
        for(size_t hi=0;hi<high.size();++hi) for(size_t lo=0;lo<low.size();++lo) {
          a.data[pos]=low[lo];b.data[pos]=high[hi];++pos;
        }
      }
      const auto products=bit_and(math,a,b,true);
      pos=0;
      std::vector<std::vector<Group>> next(nodes.size());
      for(size_t j=0;j<groups.size();++j) {
        auto& gs=groups[j];
        for(size_t k=0;k+1<gs.size();k+=2) {
          const size_t nl=gs[k].v.size(),nh=gs[k+1].v.size();
          Group g;g.v.resize(nl*nh);
          for(size_t hi=0;hi<nh;++hi) for(size_t lo=0;lo<nl;++lo)
            g.v[lo+nl*hi]=products.data[pos++];
          next[j].push_back(std::move(g));
        }
        if(gs.size()&1) next[j].push_back(std::move(gs.back()));
      }
      require(pos==total);
      groups=std::move(next);
    }

    for(size_t j=0;j<nodes.size();++j) {
      require(groups[j].size()==1 && groups[j][0].v.size()==nodes[j].span);
      nodes[j].thermometer.resize(nodes[j].span);
      uint8_t acc=0;
      for(size_t i=0;i<groups[j][0].v.size();++i) {
        acc^=groups[j][0].v[i];
        nodes[j].thermometer[i]=acc;
      }
    }
  }

  if(!leaves.empty()) {
    BoolArray a(math.party,int(leaves.size())),b(math.party,int(leaves.size()));
    for(size_t j=0;j<leaves.size();++j) {
      a.data[j]=marks.data[leaves[j].start]^one;
      b.data[j]=marks.data[leaves[j].start+1];
    }
    const auto product=bit_and(math,a,b,gates>=1);
    for(size_t j=0;j<leaves.size();++j) controls[leaves[j].id]=product.data[j]^leaves[j].offset;
  }
  for(int bit=0;gates<3 && bit<log2ceil(plan.features());++bit) {
    const unsigned half=1U<<bit;
    std::vector<size_t> ids;
    for(size_t j=0;j<nodes.size();++j) if(log2ceil(nodes[j].span)>bit) ids.push_back(j);
    if(ids.empty()) continue;
    if(bit==0) {
      for(size_t j:ids) nodes[j].thermometer={uint8_t(one^nodes[j].bits[0]),one};
      continue;
    }
    BoolArray select(math.party,int(ids.size()*half)),previous(math.party,int(ids.size()*half));
    for(size_t j=0;j<ids.size();++j) {
      const auto& node=nodes[ids[j]];
      require(node.thermometer.size()==half);
      for(unsigned i=0;i<half;++i) {
        select.data[j*half+i]=node.bits[bit];previous.data[j*half+i]=node.thermometer[i];
      }
    }
    const auto products=bit_and(math,select,previous,gates>=1);
    for(size_t j=0;j<ids.size();++j) {
      auto& node=nodes[ids[j]];node.thermometer.resize(2*half);
      for(unsigned i=0;i<half;++i) {
        const uint8_t t=products.data[j*half+i];
        node.thermometer[i]^=t;
        node.thermometer[half+i]=one^node.bits[bit]^t;
      }
    }
  }
  for(const auto& node:nodes) for(unsigned i=0;i<node.outputs;++i)
    controls[node.base+i]=node.thermometer[i]^node.wrap;
  std::vector<uint8_t> retained;retained.reserve(plan.switch_count());
  for(unsigned id:plan.kept_control_ids()) retained.push_back(controls[id]);
  return retained;
}

// A fixed public network layer performs shared selection. Ring-2 arithmetic
// agrees with XOR; the boolean inverse uses only native ANDs.
inline std::vector<uint64_t> permute(FPMath& math,const h0_orcompact::Plan& plan,
    const std::vector<uint8_t>& control,const std::vector<uint64_t>& input,int bits,bool gather,
    bool fast_boolean=false,ProductTape* tape=nullptr,int lanes=1) {
  require(control.size()==plan.switch_count());
  require(lanes==1 || lanes==2 || lanes==4 || lanes==8);
  require(input.size()==lanes*(gather ? plan.features():plan.prefix_capacity()));
  const uint64_t mask=bitmask(bits);
  std::vector<uint64_t> wires(lanes*plan.wire_count(),0);
  if(gather) for(unsigned i=0;i<plan.features();++i) for(int c=0;c<lanes;++c)
    wires[lanes*plan.output_wires()[i]+c]=input[lanes*i+c];
  else std::copy(input.begin(),input.end(),wires.begin());
  const auto layer=[&](const std::vector<h0_orcompact::Gate>& gates) {
    if(gates.empty()) return;
    BoolArray select(math.party,int(lanes*gates.size()));
    std::vector<uint64_t> products(lanes*gates.size());
    if(tape) {
      std::vector<unsigned> ids(gates.size());std::vector<uint64_t> delta(lanes*gates.size());
      for(size_t j=0;j<gates.size();++j) {
        const auto& g=gates[j];ids[j]=plan.control_index(g.control_id);
        for(int c=0;c<lanes;++c)
          delta[lanes*j+c]=(wires[lanes*(gather ? g.output1:g.input1)+c]-wires[lanes*(gather ? g.output0:g.input0)+c])&mask;
      }
      products=tape->apply(ids,delta,bits);
    } else if(bits==1) {
      BoolArray difference(math.party,int(lanes*gates.size()));
      for(size_t j=0;j<gates.size();++j) {
        const auto& g=gates[j];
        for(int c=0;c<lanes;++c) {
          select.data[lanes*j+c]=control[plan.control_index(g.control_id)];
          difference.data[lanes*j+c]=uint8_t(wires[lanes*(gather ? g.output0:g.input0)+c]^wires[lanes*(gather ? g.output1:g.input1)+c]);
        }
      }
      const auto product=bit_and(math,select,difference,fast_boolean);
      for(size_t j=0;j<products.size();++j) products[j]=product.data[j];
    } else {
      FixArray difference(math.party,int(lanes*gates.size()),true,bits,0);
      for(size_t j=0;j<gates.size();++j) {
        const auto& g=gates[j];
        for(int c=0;c<lanes;++c) {
          select.data[lanes*j+c]=control[plan.control_index(g.control_id)];
          difference.data[lanes*j+c]=(wires[lanes*(gather ? g.output1:g.input1)+c]-wires[lanes*(gather ? g.output0:g.input0)+c])&mask;
        }
      }
      const auto product=math.fix->if_else(select,difference,uint64_t(0));
      std::copy(product.data,product.data+product.size,products.begin());
    }
    for(size_t j=0;j<gates.size();++j) {
      const auto& g=gates[j];
      const auto a=gather ? g.output0:g.input0,b=gather ? g.output1:g.input1;
      const auto x=gather ? g.input0:g.output0,y=gather ? g.input1:g.output1;
      for(int c=0;c<lanes;++c) {
        wires[lanes*x+c]=(wires[lanes*a+c]+products[lanes*j+c])&mask;
        wires[lanes*y+c]=(wires[lanes*b+c]-products[lanes*j+c])&mask;
      }
    }
  };
  if(gather) for(auto it=plan.layers().rbegin();it!=plan.layers().rend();++it) layer(*it);
  else for(const auto& gates:plan.layers()) layer(gates);
  if(gather) return {wires.begin(),wires.begin()+lanes*plan.prefix_capacity()};
  std::vector<uint64_t> out(lanes*plan.features());
  for(unsigned i=0;i<plan.features();++i) for(int c=0;c<lanes;++c)
    out[lanes*i+c]=wires[lanes*plan.output_wires()[i]+c];
  return out;
}

inline BoolArray group_marks(FPMath& math,const BoolArray& unknown,int lanes) {
  require(unknown.size%lanes==0 && (lanes==1 || lanes==2 || lanes==4 || lanes==8));
  BoolArray known(math.party,unknown.size);
  const uint8_t one=uint8_t(math.party==sci::ALICE);
  for(int i=0;i<unknown.size;++i) known.data[i]=unknown.data[i]^one;
  for(int remaining=lanes;remaining>1;remaining/=2) {
    BoolArray a(math.party,known.size/2),b(math.party,known.size/2);
    for(int i=0;i<a.size;++i) {a.data[i]=known.data[2*i];b.data[i]=known.data[2*i+1];}
    known=bit_and(math,a,b,true);
  }
  for(int i=0;i<known.size;++i) known.data[i]^=one;
  return known;
}
} // namespace shared_residual
