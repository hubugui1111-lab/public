#pragma once
#include <cstdint>
#ifdef __SSE2__
#include <emmintrin.h>
#endif
namespace shared_residual {
// Input: exactly 64 bytes, each 0 or 1. Preserve triple index bit-for-bit.
inline uint64_t pack_boolean64(const uint8_t* input) {
  uint64_t result=0;
#ifdef __SSE2__
  for(unsigned block=0;block<4;++block) {
    auto bytes=_mm_loadu_si128(reinterpret_cast<const __m128i*>(input+16*block));
    result|=uint64_t(uint16_t(_mm_movemask_epi8(_mm_slli_epi16(bytes,7))))<<(16*block);
  }
#else
  for(unsigned bit=0;bit<64;++bit)result|=uint64_t(input[bit])<<bit;
#endif
  return result;
}
}
