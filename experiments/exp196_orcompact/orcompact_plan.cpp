// SPDX-License-Identifier: MIT
// Written independently from the corrected author paper's Figures 1/2;
// no source from the separately distributed oblivshuffle package is included.
// Paper SHA256: f113594174f7b692c8d00325745499eddadbb86fa1416628839a5ef9df99bcaa
#include "orcompact_scatter.h"

#include <algorithm>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <utility>

namespace h0_orcompact {
namespace {
using Pair = std::pair<uint32_t, uint32_t>;
constexpr uint32_t kMissing = std::numeric_limits<uint32_t>::max();

uint32_t largest_power(uint32_t count) {
  uint32_t power = 1;
  while (power <= count / 2) power *= 2;
  return power;
}

// Public pair sequence in forward compaction order, without reading marks.
void offset_pairs(uint32_t start, uint32_t count, std::vector<Pair>& pairs) {
  if (count <= 1) return;
  if (count == 2) {
    pairs.emplace_back(start, start + 1);
    return;
  }
  const uint32_t half = count / 2;
  offset_pairs(start, half, pairs);
  offset_pairs(start + half, half, pairs);
  for (uint32_t i = 0; i < half; ++i) pairs.emplace_back(start + i, start + half + i);
}

void compact_pairs(uint32_t start, uint32_t count, std::vector<Pair>& pairs) {
  if (count == 0) return;
  const uint32_t power = largest_power(count), remainder = count - power;
  compact_pairs(start, remainder, pairs);
  // The power-of-two block is the suffix, not the prefix or a rounded half.
  offset_pairs(start + remainder, power, pairs);
  for (uint32_t i = 0; i < remainder; ++i) pairs.emplace_back(start + i, start + power + i);
}

// The prefix sums describe ORIGINAL marks. No mark or data array is mutated
// while compiling the controls; all count/offset work is owner-local.
void offset_controls(uint32_t start, uint32_t count, uint32_t offset,
                     const std::vector<uint32_t>& prefix, std::vector<uint8_t>& controls) {
  if (count <= 1) return;
  if (count == 2) {
    const uint32_t mark0 = prefix[start + 1] - prefix[start];
    const uint32_t mark1 = prefix[start + 2] - prefix[start + 1];
    controls.push_back(static_cast<uint8_t>(((1 - mark0) * mark1) ^ offset));
    return;
  }
  const uint32_t half = count / 2;
  const uint32_t marked_left = prefix[start + half] - prefix[start];
  offset_controls(start, half, offset % half, prefix, controls);
  offset_controls(start + half, half, (offset + marked_left) % half, prefix, controls);
  const bool wrap = ((offset % half) + marked_left >= half) ^ (offset >= half);
  const uint32_t boundary = (offset + marked_left) % half;
  for (uint32_t i = 0; i < half; ++i)
    controls.push_back(static_cast<uint8_t>(wrap ^ (i >= boundary)));
}

void compact_controls(uint32_t start, uint32_t count, const std::vector<uint32_t>& prefix,
                      std::vector<uint8_t>& controls) {
  if (count == 0) return;  // Before log/power and before taking a modulo.
  const uint32_t power = largest_power(count), remainder = count - power;
  const uint32_t marked_left = prefix[start + remainder] - prefix[start];
  compact_controls(start, remainder, prefix, controls);
  // Corrected Figure 2, line 4; line 6 uses >=, not >.
  offset_controls(start + remainder, power,
                  (power - remainder + marked_left) % power, prefix, controls);
  for (uint32_t i = 0; i < remainder; ++i)
    controls.push_back(static_cast<uint8_t>(i >= marked_left));
}
}  // namespace

Plan::Plan(uint32_t features) : Plan(features, features, false) {}
Plan::Plan(uint32_t features, uint32_t capacity) : Plan(features, capacity, true) {}
Plan Plan::full_prefix(uint32_t features, uint32_t capacity) {
  return Plan(features, capacity, false);
}

Plan::Plan(uint32_t features, uint32_t capacity, bool pruned)
    : features_(features), prefix_capacity_(capacity), wire_count_(features), pruned_(pruned) {
  // The private CNN adapter has 6272 scalar coordinates. Keep a public finite
  // resource bound; this changes no topology/control rule for earlier callers.
  if (features == 0 || features > 8192 || capacity > features)
    throw std::invalid_argument("invalid public ORCompact dimensions");
  std::vector<Pair> forward_pairs;
  compact_pairs(0, features, forward_pairs);
  full_switch_count_ = forward_pairs.size();
  compact_control_index_.assign(full_switch_count_, kMissing);
  std::vector<uint8_t> keep(full_switch_count_, 0), zero(features, 0);
  if (pruned)
    for (uint32_t i = capacity; i < features; ++i) zero[i] = 1;
  std::vector<uint32_t> current(features), depth(features, 0);
  std::iota(current.begin(), current.end(), 0);
  // Reverse the swaps, not merely their bits. Unique scratch wires make layer
  // dependencies explicit; deleted outputs remain canonical public zero.
  for (std::size_t next = forward_pairs.size(); next > 0; --next) {
    const auto id = static_cast<uint32_t>(next - 1);
    const auto [position0, position1] = forward_pairs[id];
    const uint32_t input0 = current[position0], input1 = current[position1];
    const uint32_t output0 = wire_count_++, output1 = wire_count_++;
    const bool public_zero = pruned && zero[input0] && zero[input1];
    const uint32_t level = public_zero ? 0 : 1 + std::max(depth[input0], depth[input1]);
    zero.push_back(static_cast<uint8_t>(public_zero));
    zero.push_back(static_cast<uint8_t>(public_zero));
    depth.push_back(level);
    depth.push_back(level);
    current[position0] = output0;
    current[position1] = output1;
    if (!public_zero) {
      if (layers_.size() < level) layers_.resize(level);
      layers_[level - 1].push_back({id, input0, input1, output0, output1});
      keep[id] = 1;
    }
  }
  output_wires_ = std::move(current);
  for (uint32_t id = 0; id < full_switch_count_; ++id) {
    if (!keep[id]) continue;
    compact_control_index_[id] = static_cast<uint32_t>(kept_control_ids_.size());
    kept_control_ids_.push_back(id);
  }
}

uint32_t Plan::control_index(uint32_t original_id) const {
  if (original_id >= compact_control_index_.size() || compact_control_index_[original_id] == kMissing)
    throw std::invalid_argument("invalid retained ORCompact control ID");
  return compact_control_index_[original_id];
}

std::vector<uint8_t> Plan::compile_sorted_targets(const std::vector<uint32_t>& targets) const {
  if (targets.size() > features_ || (pruned_ && targets.size() != prefix_capacity_))
    throw std::invalid_argument("ORCompact target count mismatch");
  std::vector<uint32_t> prefix(features_ + 1, 0);
  for (std::size_t i = 0; i < targets.size(); ++i) {
    if (targets[i] >= features_ || (i > 0 && targets[i - 1] >= targets[i]))
      throw std::invalid_argument("ORCompact targets must be strictly increasing and bounded");
    prefix[targets[i] + 1] = 1;
  }
  for (uint32_t i = 0; i < features_; ++i) prefix[i + 1] += prefix[i];
  std::vector<uint8_t> full_controls;
  full_controls.reserve(full_switch_count_);
  compact_controls(0, features_, prefix, full_controls);
  if (full_controls.size() != full_switch_count_)
    throw std::runtime_error("ORCompact compiler topology mismatch");
  std::vector<uint8_t> result;
  result.reserve(kept_control_ids_.size());
  for (uint32_t id : kept_control_ids_) result.push_back(full_controls[id]);
  return result;
}
}  // namespace h0_orcompact
