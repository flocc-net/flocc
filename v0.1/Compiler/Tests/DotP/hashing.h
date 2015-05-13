#include <iostream>
#include <boost/functional/hash/hash.hpp>

namespace flocc {

typedef std::size_t hash_t;

template <typename T>
struct hasher {
  inline static hash_t hash(T v) {
    boost::hash<T> h;
    return h(v);
  }
};

template <class T> // taken from boost
inline void hash_combine(std::size_t& seed, T const& v) {
    seed ^= flocc::hasher<T>::hash(v) + 0x9e3779b9 + (seed<<6) + (seed>>2);
}

}

/*int main(int argc, char** argv) {

  std::cout << flocc::hasher<int>::hash(-1);
  return 0;

}*/
