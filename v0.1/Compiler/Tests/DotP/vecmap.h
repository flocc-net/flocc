#define DEBUG 1
#include <cstdio>
#include <cstring>
#include <vector>
#include <algorithm>

#include "pointer.h"

#define VEC_START(V) &((V).front())
#define VEC_LAST(V) &((V).back())
#define VEC_END(V) (&(V)[((V).size())])

using namespace std;

namespace flocc {

// comparison function using standard less-than but
// only comparing the keys of a key-value struct
template <typename KV>
inline bool compare_keys (KV i, KV j) { return (i.v0 < j.v0); }

// a sorted vector
template <typename K, typename V, typename KV>
struct vecmap {
private:
  bool sorted, owned;
  SPTR(vector<KV>) vec;

  void sort() {
    sort(VEC_START(*vec), VEC_END(*vec));
    unique(VEC_START(*vec), VEC_END(*vec));
    sorted = true;
  }

  inline void ensureSorted() {
    if (!sorted) sort();
  }

public:
  // create a new vector internally
  vecmap(): sorted(false), owned(true), vec(new vector<KV>) {
  }

  // uses vector passed to it
  vecmap(SPTR(vector<KV>) vec, bool sorted): sorted(sorted), owned(false), vec(vec) {
  }

  ~vecmap() {
    if (owned) delete vec;
  }

  void appendBlock (KV *data, int count) {
    // invalidate current element order
    sorted = false;

    // resize to fit data
    int sz = vec->size();
    vec->resize(sz+count);
    KV* end = &(*vec)[sz];

    // memcopy data
    memcpy(end, data, count*sizeof(KV));
  }

  typedef typename vector<KV>::iterator iterator;
  typedef typename vector<KV>::const_iterator const_iterator;
  
  // access using it->v0 and it->v1
  inline iterator begin() {
    ensureSorted();
    return vec->begin();
  }

  inline iterator end() {
    ensureSorted();
    return vec->end();
  }

  inline const_iterator cbegin() {
    ensureSorted();
    return vec->cbegin();
  }

  inline const_iterator cend() {
    ensureSorted();
    return vec->cend();
  }

  iterator find(K key) {
    // ensure sorted
    ensureSorted();

    // make search term
    KV keyVal;
    keyVal.v0 = key;

    // binary search
    return lower_bound(VEC_START(*vec), VEC_END(*vec), keyVal, compare_keys<KV>);
  }

};

}

/*int main(int argc, char** argv) {

  return 0;

}*/
