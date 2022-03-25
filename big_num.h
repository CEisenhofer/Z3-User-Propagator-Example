#pragma once
#include <cstdint>
#include <string>
#include <vector>
#include <set>

class BigNum {

  /**
   * Representation of the number
   */
  std::vector<uint64_t> arr;
  /**
   * The number of bits
   */
  size_t bitWidth;

public:

  BigNum();

  explicit BigNum(size_t bitWidth);

  BigNum(uint64_t u64, size_t bitWidth);

  BigNum(const char *arr, size_t bitWidth);

  BigNum(std::vector<uint64_t> &&arr, size_t bitWidth);

  BigNum(const BigNum &other);

  virtual ~BigNum();

  size_t bits() const {
    return bitWidth;
  }

  void set(uint64_t u64);

  void set(const char* arr);

  BigNum operator+(const BigNum &other) const;

  BigNum operator-(const BigNum &other) const;

  bool operator==(const BigNum &other) const;

  bool operator!=(const BigNum &other) const { return !(*this == other); }

  bool operator<(const BigNum &other) const;

  bool operator<=(const BigNum &other) const;

  bool operator>(const BigNum &other) const { return other < *this; }

  bool operator>=(const BigNum &other) const { return other <= *this; }

  bool extract(size_t pos) const;

  operator bool() const;

  std::string toString() const;

  std::string toString2() {
    return toString() + " (" + std::to_string(bitWidth) + "bits)";
  }

};
