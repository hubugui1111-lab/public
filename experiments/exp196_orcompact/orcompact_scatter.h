// SPDX-License-Identifier: MIT
// Independent implementation of the corrected ORCompact algorithm described
// by Sasy, Johnson and Goldberg, CCS 2022 extended author version, Figures 1/2.
// https://www.ohmygodel.com/publications/oblivshuffle-ccs2022.pdf
#pragma once

#include <cstddef>
#include <cstdint>
#include <vector>

struct GroupElement;
class Peer;

namespace h0_orcompact {

struct Gate {
  uint32_t control_id;
  uint32_t input0, input1, output0, output1;
};

class Plan {
 public:
  // Full inverse topology, for the pure public-data reference. The compiler
  // accepts any marked subset; its reference input is a complete F-word array.
  explicit Plan(uint32_t features);
  // Candidate: exactly B possibly nonzero prefix inputs, including dummy slots.
  // Remove only switches whose two inputs are publicly known zero. Never use
  // the compiled controls, target set, validity or actual delta to prune gates.
  Plan(uint32_t features, uint32_t prefix_capacity);
  // Full topology with a shorter output prefix.  Unlike Plan(F,B), this
  // retains switches touching every input coordinate, so secret nonzero
  // positions may occur anywhere in the F-word input.  It is the correct
  // choice when the unresolved set is private and not known to be a public
  // prefix; the output is still bounded to the first B compacted slots.
  static Plan full_prefix(uint32_t features, uint32_t prefix_capacity);
  uint32_t features() const { return features_; }
  uint32_t prefix_capacity() const { return prefix_capacity_; }
  bool pruned() const { return pruned_; }
  uint32_t wire_count() const { return wire_count_; }
  std::size_t switch_count() const { return kept_control_ids_.size(); }
  std::size_t full_switch_count() const { return full_switch_count_; }
  const std::vector<uint32_t>& kept_control_ids() const { return kept_control_ids_; }
  uint32_t control_index(uint32_t original_id) const;
  const std::vector<std::vector<Gate>>& layers() const { return layers_; }
  const std::vector<uint32_t>& output_wires() const { return output_wires_; }

  // Model-owner-local compilation. Targets are strictly increasing natural
  // coordinates; Plan(F,B) requires exactly B, Plan(F) permits any size <= F.
  // Return canonical clear bits in retained FORWARD traversal-ID order. These
  // bits must be secretly selected/shared before any two-party execution.
  // Expansion applies the same swaps in reversed dependency order. The input
  // prefix must follow this sorted target order, not the original slot order.
  std::vector<uint8_t> compile_sorted_targets(
      const std::vector<uint32_t>& targets) const;

 private:
  Plan(uint32_t features, uint32_t prefix_capacity, bool pruned);
  uint32_t features_, prefix_capacity_, wire_count_;
  bool pruned_;
  std::size_t full_switch_count_ = 0;
  std::vector<uint32_t> kept_control_ids_, compact_control_index_, output_wires_;
  std::vector<std::vector<Gate>> layers_;
};

// Online execution is restricted to Plan(F,B), exactly B ring-24 delta shares
// and canonical XOR control shares. Same public layers on both parties; each
// layer consumes fresh native COT material and joins before the next layer.
// No secret address, branch, target index or active-slot count is disclosed.
std::vector<GroupElement> scatter(
    int party_id, Peer* player, const Plan& plan,
    const std::vector<uint8_t>& secret_controls,
    const std::vector<GroupElement>& deltas);

}  // namespace h0_orcompact
