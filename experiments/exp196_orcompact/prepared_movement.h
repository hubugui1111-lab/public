// SPDX-License-Identifier: MIT
// Kangaroo-inspired static layout, using the unchanged secret switching network.
#pragma once
#include "shared_controls.h"
namespace shared_residual {
class PreparedMovement {
  struct Layer {
    std::vector<unsigned> ids,a,b,x,y;
  };
  const h0_orcompact::Plan& plan_;int lanes_;
  std::vector<Layer> forward_,reverse_;
  Layer make(const std::vector<h0_orcompact::Gate>& gates,bool gather) {
    Layer out;
    for(const auto& g:gates) {
      out.ids.push_back(plan_.control_index(g.control_id));
      for(int c=0;c<lanes_;++c) {
        out.a.push_back(lanes_*(gather ? g.output0:g.input0)+c);
        out.b.push_back(lanes_*(gather ? g.output1:g.input1)+c);
        out.x.push_back(lanes_*(gather ? g.input0:g.output0)+c);
        out.y.push_back(lanes_*(gather ? g.input1:g.output1)+c);
      }
    }
    return out;
  }
public:
  PreparedMovement(const h0_orcompact::Plan& plan,int lanes):plan_(plan),lanes_(lanes) {
    for(auto it=plan.layers().rbegin();it!=plan.layers().rend();++it) forward_.push_back(make(*it,true));
    for(const auto& layer:plan.layers()) reverse_.push_back(make(layer,false));
  }
  std::vector<uint64_t> run(ProductTape& tape,const std::vector<uint64_t>& input,int bits,bool gather) const {
    require(input.size()==lanes_*(gather ? plan_.features():plan_.prefix_capacity()));
    const auto mask=bitmask(bits);std::vector<uint64_t> wires(lanes_*plan_.wire_count(),0);
    if(gather) for(unsigned i=0;i<plan_.features();++i) for(int c=0;c<lanes_;++c)
      wires[lanes_*plan_.output_wires()[i]+c]=input[lanes_*i+c];
    else std::copy(input.begin(),input.end(),wires.begin());
    for(const auto& layer:gather ? forward_:reverse_) {
      if(layer.ids.empty()) continue;
      std::vector<uint64_t> delta(layer.a.size());
      for(size_t i=0;i<delta.size();++i) delta[i]=(wires[layer.b[i]]-wires[layer.a[i]])&mask;
      const auto products=tape.apply(layer.ids,delta,bits);
      for(size_t i=0;i<delta.size();++i) {
        wires[layer.x[i]]=(wires[layer.a[i]]+products[i])&mask;
        wires[layer.y[i]]=(wires[layer.b[i]]-products[i])&mask;
      }
    }
    if(gather) return {wires.begin(),wires.begin()+lanes_*plan_.prefix_capacity()};
    std::vector<uint64_t> result(lanes_*plan_.features());
    for(unsigned i=0;i<plan_.features();++i) for(int c=0;c<lanes_;++c)
      result[lanes_*i+c]=wires[lanes_*plan_.output_wires()[i]+c];
    return result;
  }
};
}
