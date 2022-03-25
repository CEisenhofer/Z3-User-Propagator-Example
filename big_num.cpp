#include "big_num.h"

#include <algorithm>
#include <cassert>
#include <sstream>
#include <string.h>

BigNum::BigNum() : arr(), bitWidth(0) { }

BigNum::BigNum(size_t bitWidth) : arr(), bitWidth(bitWidth) {
    assert(bitWidth > 0);
    set((uint64_t)0);
}

BigNum::BigNum(uint64_t u64, size_t bitWidth) : arr(), bitWidth(bitWidth) {
  assert(bitWidth > 0);
  set(u64);
}

BigNum::BigNum(const char *const arr, size_t bitWidth) {
  this->bitWidth = bitWidth;
  set(arr);
}

BigNum::BigNum(std::vector<uint64_t> &&arr, size_t bitWidth) : arr(arr), bitWidth(bitWidth) {
  assert(bitWidth > 0);
  arr.resize((bitWidth + 63) / 64, 0ull);
}

BigNum::BigNum(const BigNum &other) = default;

BigNum::~BigNum() = default;

void BigNum::set(uint64_t u64) {
  arr.resize((bitWidth + 63) / 64, 0ull);
  if (bitWidth < 64)
    arr[0] = u64 & ((1ull << bitWidth) - 1);
  else
    arr[0] = u64;
}

void BigNum::set(const char* arr) {
  this->arr.resize((bitWidth + 63) / 64, 0);
  size_t i = 0;
  const char *current = arr + (strlen(arr) - 1);
  for (; i < bitWidth && current + 1 != arr; i++, current--) {
    this->arr[i / 64] |= ((uint64_t)(*current == '1')) << (i % 64);
  }
}

BigNum BigNum::operator+(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  assert(arr.size() == other.arr.size());
  std::vector<uint64_t> res;
  res.resize(arr.size(), 0ull);

  uint64_t overflow = 0ull;

  for (size_t i = 0; i < arr.size(); i++) {
    uint64_t v = arr[i] + other.arr[i] + overflow;
    res[i] = v;
    overflow = (uint64_t)(v < arr[i] || v < other.arr[i] || v < overflow);
  }
  if (bitWidth % 64 != 0) {
    res.back() &= ((1ull << (bitWidth % 64)) - 1);
  }
  return {std::move(res), bitWidth};
}

BigNum BigNum::operator-(const BigNum &other) const {
    assert(bitWidth == other.bitWidth);
    assert(arr.size() == other.arr.size());
    std::vector<uint64_t> res;
    res.resize(arr.size(), 0ull);

    uint64_t overflow = 1ull;

    for (size_t i = 0; i < arr.size(); i++) {
        uint64_t o = ~(other.arr[i]);
        uint64_t v = arr[i] + o + overflow;
        res[i] = v;
        overflow = (uint64_t)(v < arr[i] || v < o || v < overflow);
    }
    if (bitWidth % 64 != 0) {
        res.back() &= ((1ull << (bitWidth % 64)) - 1);
    }
    return {std::move(res), bitWidth};
}

bool BigNum::operator==(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  assert(arr.size() == other.arr.size());
  for (size_t i = 0; i < arr.size(); i++) {
    if (arr[i] != other.arr[i]) {
      return false;
    }
  }
  return true;
}

bool BigNum::operator<(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  assert(arr.size() == other.arr.size());
  for (size_t i = arr.size(); i > 0; i--) {
    if (arr[i - 1] < other.arr[i - 1])
      return true;
    else if (arr[i - 1] > other.arr[i - 1])
      return false;
  }
  return false;
}

bool BigNum::operator<=(const BigNum &other) const {
  assert(bitWidth == other.bitWidth);
  assert(arr.size() == other.arr.size());
  for (size_t i = arr.size(); i > 0; i--) {
    if (arr[i - 1] < other.arr[i - 1])
      return true;
    else if (arr[i - 1] > other.arr[i - 1])
      return false;
  }
  return true;
}

bool BigNum::extract(size_t pos) const {
  size_t posArr = pos / 64;
  size_t posBit = pos % 64;
  return (bool)((arr[posArr] >> posBit) & 1);
}

BigNum::operator bool() const {
  for (uint64_t v: arr) {
    if (v != 0)
      return true;
  }
  return false;
}

std::string BigNum::toString() const {
  std::stringstream ss;
  for (size_t i = bitWidth; i > 0; i--) {
    size_t posArr = (i - 1) / 64;
    size_t posBit = (i - 1) % 64;
    ss << (char)('0' + ((arr[posArr] >> posBit) & 1));
  }
  return ss.str();
}