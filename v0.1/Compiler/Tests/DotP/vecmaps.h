#include <vector>
#include <algorithm>
#include <iostream>

#include "global.h"
#include "pointer.h"
#include "assert.h"

#define VEC_START(V) &((V).front())
#define VEC_LAST(V) &((V).back())
#define VEC_END(V) (&(V)[((V).size())])

#define VEC_IBEGIN(V) ((V).begin())
#define VEC_IEND(V) ((V).end())

//#define VEC_CONST 0

using namespace std;

// TODO reimplement using Boost multiindex containers?

namespace flocc {

// comparison function using standard less-than but
// only comparing the keys emitted by proj functions
template <typename ET, typename KT, typename ProjK>
struct less_than_keys {
  static inline bool less_than (ET i, ET j) { 
    KT Ki = ProjK::run(i);
    KT Kj = ProjK::run(j);
    return (Ki < Kj); 
  }
};

// comparison function using standard less-than but
// only comparing the keys of a key-value struct
template <typename ET>
struct less_than_fsts {
  static inline bool less_than (ET i, ET j) { 
    return (i.v0 < j.v0); 
  }
};

// comparison function using standard less-than but
// only comparing the keys of a key-value struct
template <typename ET, typename KT, typename ProjK>
struct equal_keys {
  static inline bool equals (ET i, ET j) { 
    KT Ki = ProjK::proj(i);
    KT Kj = ProjK::proj(j);
    return (Ki == Kj); 
  }
};

// comparison function using standard equals but
// only comparing the keys of a key-value struct
template <typename ET>
struct equal_fsts {
  static inline bool equals (ET i, ET j) { 
    return (i.v0 == j.v0); 
  }
};

// projection function for fst on any struct
template <typename ET, typename K>
struct proj_fst {
  static inline K proj(ET v) {
    return v.v0;
  }
  static inline K run(ET v) {
    return v.v0;
  }
};

// binary search to lower bound in sorted range
template <class ForwardIterator, class KeyT, class ProjKey>
  ForwardIterator lower_bound (ForwardIterator first, ForwardIterator last, const KeyT& val)
{
  ForwardIterator it;
  typename iterator_traits<ForwardIterator>::difference_type count, step;
  count = distance(first,last);
  while (count>0)
  {
    it = first; step=count/2; advance (it,step);
    if ( ProjKey::run(*it) < val ) {                 // or: if (comp(*it,val)), for version (2)
      first=++it;
      count-=step+1;
    }
    else count=step;
  }
  return first;
}

// binary search to upper bound in sorted range
template <class ForwardIterator, class KeyT, class ProjKey>
  ForwardIterator upper_bound (ForwardIterator first, ForwardIterator last, const KeyT& val)
{
  ForwardIterator it;
  typename iterator_traits<ForwardIterator>::difference_type count, step;
  count = std::distance(first,last);
  while (count>0)
  {
    it = first; step=count/2; std::advance (it,step);
    if (!(val < ProjKey::run(*it)))                 // or: if (!comp(val,*it)), for version (2)
      { first=++it; count-=step+1;  }
    else count=step;
  }
  return first;
}

// binary search to lower and upper bound in sorted range
template <class ForwardIterator, class KeyT, class ProjKey>
  pair<ForwardIterator,ForwardIterator>
    equal_range (ForwardIterator first, ForwardIterator last, const KeyT& val)
{
  ForwardIterator it = flocc::lower_bound<ForwardIterator, KeyT, ProjKey>(first,last,val);
  return std::make_pair ( it, flocc::upper_bound<ForwardIterator, KeyT, ProjKey>(it,last,val) );
}

template <class ForwardIterator>
  bool is_sorted (ForwardIterator first, ForwardIterator last)
{
  if (first==last) return true;
  ForwardIterator next = first;
  while (++next!=last) {
    if (*next<*first)     // or, if (comp(*next,*first)) for version (2)
      return false;
    ++first;
  }
  return true;
}

// a sorted vector
// ET: element type, 
// PK: Primary key type (uniqueness)
// SK: Secondary key type (for searching), ProjSK: emits SK from ET
template <typename ET, typename PK, typename SK, typename ProjSK>
class vecmap {
private:
  bool distinct;
  int sorted; // 0: not sorted, 1: by primary key, 2: by secondary key 
  SPTR(vector<ET>) vec;

  // remove duplicate elements
  void makeDistinct() {
    ensureSorted1();

    #ifdef DEBUG
    int R = MPI::COMM_WORLD.Get_rank();
    // (is_sorted checking if sorted by element, rather than just prim key)...
    std::cerr << R << ") vecmap: before makeDistinct() is_sorted? " << is_sorted(VEC_START(*vec), VEC_END(*vec)) << "\n";
    std::cerr << R << ") vecmap: before makeDistinct() size:" << vec->size() << "\n";
    #endif

    ET *newEnd = unique(VEC_START(*vec), VEC_END(*vec));//, equal_fsts<ET>::equals);
    //std::cout << "unique called on vecmap.\n";
    vec->resize(std::distance(VEC_START(*vec), newEnd));
    distinct = true;

    #ifdef DEBUG
    std::cerr << R << ") vecmap: after makeDistinct() size:" << vec->size() << "\n";
    #endif
  }

  inline bool ensureDistinct() {
    if (!distinct) makeDistinct();
  }

  // sort by primary key
  void sort1() {
    std::sort(VEC_START(*vec), VEC_END(*vec), less_than_fsts<ET>::less_than); // TODO CHANGE BACK
    //ET *st = &vec->front(); //st++;
    //ET *end = &(*vec)[vec->size()];
    //std::sort(st, &(*vec)[vec->size()-1]); // WEIRDLY WORKS!
    //std::sort(st, end);
    sorted = 1; 
  }

  inline void ensureSorted1() {
    if (sorted != 1) sort1();
  }

  // sort by secondary key
  void sort2() {
    std::sort(VEC_START(*vec), VEC_END(*vec), less_than_keys<ET, SK, ProjSK>::less_than);
    sorted = 2;
  }

  inline void ensureSorted2() {
    if (sorted != 2) sort2();
  }

  void init() {
    #ifdef DEBUG
    int R = MPI::COMM_WORLD.Get_rank();
    std::cerr << R << ") flocc::vecmap<" << TYID(ET) << ", " << TYID(PK) << ", " << TYID(SK) << ", " << TYID(ProjSK) << ">::init()\n";
    #endif
  }

public:
  // create a new vector internally
  vecmap(): distinct(false), sorted(0), vec(new vector<ET>) {
    init();
  }

  // uses vector passed to it
  vecmap(SPTR(vector<ET>) vec, int sorted, bool distinct): sorted(sorted), distinct(distinct), vec(vec) {
    mpiAssert(vec, "vecmap:constructor: vec is null pointer.");
    mpiAssert(sorted >= 0 && sorted <= 2, "vecmap:constructor: sorted out of range.");
    init();
  }

  inline ET* data() { return VEC_START(*vec); }

  void setDistinct() { distinct = true; }
  bool isDistinct() { return distinct;  }

  void setPrimarySorted() { sorted = 1; }
  bool isPrimarySorted() { return sorted == 1; }

  void qsetSecondarySorted() { sorted = 2; }
  bool isSecondarySorted() { return sorted == 2; }

  void push_back(ET el) {
    mpiAssert(vec, "vecmap:push_back: vec is null pointer.");
    sorted = 0; distinct = false; // TODO could insert at correct position, to keep sorted... 
    vec->push_back(el);
  }

  void appendBlock (ET *data, int count) {
    mpiAssert(count > 0, "vecmap:appendBlock: count is 0 or negative");
    mpiAssert(data != NULL, "vecmap:appendBlock: data is null pointer.");
    mpiAssert(vec, "vecmap:appendBlock: vec is null pointer.");

    // invalidate current element order
    sorted = 0; distinct = false;

    // resize to fit data
    int sz = vec->size();
    //vec->resize(sz+count);
    //ET* end = &(*vec)[sz];

    // memcopy data
    //memcpy(end, data, count*sizeof(ET));
    //vec->insert(vec->end(), data, &data[count]);
    ET def = {};
    for (int i = 0; i < count; i++) {
      // catch uninit data early 
      if (data[i] < def) { std::cout << ""; }
      else { std::cout << ""; }
      // add to vector
      vec->push_back(data[i]);
    }
  }

  template <typename NewSK, typename NewProjK>
  void assign(SPTR_CLASS<vecmap<ET, PK, NewSK, NewProjK> > newVec) {
    mpiAssert(newVec, "vecmap:assign: newVec is null pointer.");

    // insert new data
    vec->clear();
    appendBlock(newVec->data(), newVec->size());
    
    // if was sorted by primary key then inherit this sort
    if (newVec->isDistinct()) setDistinct();
    else distinct = false;
    if (newVec->isPrimarySorted()) setPrimarySorted();
    else sorted = 0;
  }

  int size() {
    ensureDistinct();
    return vec->size();
  }

  typedef typename vector<ET>::iterator iterator;
  
  iterator findPri(PK key) {
    // ensure sorted by primary key with no duplicates
    ensureDistinct();
    ensureSorted1();

    // make search term
    ET keyVal;
    keyVal.v0 = key;

    // binary search
    return std::lower_bound(VEC_IBEGIN(*vec), VEC_IEND(*vec), keyVal, less_than_fsts<ET>::less_than);
  }

  template<typename SearchK, typename SearchProj>
  iterator findSecBegin(SearchK key) {
    // ensure sorted by secondary key with no duplicates
    ensureDistinct();
    ensureSorted2();
    
    // binary search
    return flocc::lower_bound<iterator, SearchK, SearchProj>(VEC_IBEGIN(*vec), VEC_IEND(*vec), key);
  }

  template<typename SearchK, typename SearchProj>
  iterator findSecEnd(SearchK key) { return findSecEnd(VEC_IBEGIN(*vec), key); }

  template<typename SearchK, typename SearchProj>
  iterator findSecEnd(iterator begin, SearchK key) {
    // ensure sorted by secondary key with no duplicates
    ensureDistinct();
    ensureSorted2();
    
    // binary search
    return flocc::upper_bound<iterator, SearchK, SearchProj>(begin, VEC_IEND(*vec), key);
  }

  // iterators for different orderings
  // access key and value using it->v0 and it->v1
  // any order:
  inline iterator begin() {
    ensureDistinct();
    return vec->begin();
  }

  inline iterator end() {
    ensureDistinct();
    return vec->end();
  }

  // sorted by primary key:
  inline iterator pbegin() {
    ensureDistinct();
    ensureSorted1();
    return vec->begin();
  }

  inline iterator pend() {
    ensureDistinct();
    ensureSorted1();
    return vec->end();
  }

  // sorted by secondary key:
  inline iterator sbegin() {
    ensureDistinct();
    ensureSorted2();
    return vec->begin();
  }

  inline iterator send() {
    ensureDistinct();
    ensureSorted2();
    return vec->end();
  }

  #ifdef VEC_CONST
  typedef typename vector<ET>::const_iterator const_iterator;
  inline const_iterator cbegin() {
    ensureDistinct();
    return vec->cbegin();
  }

  inline const_iterator cend() {
    ensureDistinct();
    return vec->cend();
  }

  inline const_iterator cpbegin() {
    ensureDistinct();
    ensureSorted1();
    return vec->cbegin();
  }

  inline const_iterator cpend() {
    ensureDistinct();
    ensureSorted1();
    return vec->cend();
  }

  inline const_iterator csbegin() {
    ensureDistinct();
    ensureSorted2();
    return vec->cbegin();
  }

  inline const_iterator csend() {
    ensureDistinct();
    ensureSorted2();
    return vec->cend();
  }
  #else
  typedef iterator const_iterator;
  inline iterator cbegin() {
    ensureDistinct();
    return vec->begin();
  }

  inline iterator cend() {
    ensureDistinct();
    return vec->end();
  }

  inline iterator cpbegin() {
    ensureDistinct();
    ensureSorted1();
    return vec->begin();
  }

  inline iterator cpend() {
    ensureDistinct();
    ensureSorted1();
    return vec->end();
  }

  inline iterator csbegin() {
    ensureDistinct();
    ensureSorted2();
    return vec->begin();
  }

  inline iterator csend() {
    ensureDistinct();
    ensureSorted2();
    return vec->end();
  }
  #endif

};

// a sorted vector
// specialization where primary key == secondary key
// i.e. where sort proj function is fst
template <typename ET, typename K>
class vecmap <ET, K, K, proj_fst<ET, K> > {
private:
  bool sorted, distinct;
  SPTR(vector<ET>) vec;

  // remove duplicates of primary key
  void makeDistinct() {
    ensureSorted();
    ET *newEnd = unique(VEC_START(*vec), VEC_END(*vec), equal_fsts<ET>::equals);
    vec->resize(std::distance(VEC_START(*vec), newEnd));
    //vec->resize((newEnd - VEC_START(*vec)) / sizeof(ET));
    //std::cout << "unique called on fst vecmap.\n";
    distinct = true;
  }

  inline void ensureDistinct() {
    if (!distinct) makeDistinct();
  }

  // sort by primary key
  void sort() {
    std::sort(VEC_START(*vec), VEC_END(*vec), less_than_fsts<ET>::less_than);
    sorted = true; 
  }

  inline void ensureSorted() {
    if (!sorted) sort();
  }

public:
  typedef vecmap <ET, K, K, proj_fst<ET, K> > this_type;

  // create a new vector internally
  vecmap(): sorted(false), distinct(false), vec(new vector<ET>) {
    std::cout << "INIT VECMAP<FST>\n";
  }

  // uses vector passed to it
  vecmap(SPTR(vector<ET>) vec, bool sorted, bool distinct): sorted(sorted), distinct(true), vec(vec) {
    mpiAssert(vec, "vecmap<fst>:constructor: vec is null pointer.");
  }

  inline ET* data() { return VEC_START(*vec); }

  void setDistinct() { distinct = true; }
  bool isDistinct() { return distinct; }

  void setPrimarySorted() { sorted = true; }
  bool isPrimarySorted() { return sorted; }

  void setSecondarySorted() { sorted = true; }
  bool isSecondarySorted() { return sorted; }

  void push_back(ET el) {
    vec->push_back(el); // TODO change to insert at correct position
    sorted = false;
    distinct = false;
  }

  void appendBlock (ET *data, int count) {
    mpiAssert(count > 0, "vecmap:appendBlock: count is 0 or negative");
    mpiAssert(data != NULL, "vecmap:appendBlock: data is null pointer.");
    mpiAssert(vec, "vecmap:appendBlock: vec is null pointer.");

    // invalidate current element order
    sorted = false;
    distinct = false;

    // resize to fit data
    int sz = vec->size();
    //vec->resize(sz+count);
    //ET* end = &(*vec)[sz];

    // memcopy data
    //memcpy(end, data, count*sizeof(ET));
    vec->insert(vec->end(), data, &data[count]);
  }

  template <typename NewSK, typename NewProjK>
  void assign(SPTR_CLASS<vecmap<ET, K, NewSK, NewProjK> > newVec) {
    mpiAssert(newVec, "vecmap:assign<fst>: newVec is null pointer.");
    // insert new data
    vec->clear();
    appendBlock(newVec->data(), newVec->size());
    
    // if was sorted by primary key then inherit this sort
    if (newVec->isDistinct()) setDistinct();
    else distinct = false;
    if (newVec->isPrimarySorted()) setPrimarySorted();
    else sorted = false;
  }

  int size() {
    ensureDistinct();
    return vec->size();
  }

  typedef typename vector<ET>::iterator iterator;
  
  inline iterator findPri(K key) {
    return findSecBegin(key);
  }

  template<typename SearchK, typename SearchProj>
  iterator findSecBegin(SearchK key) {
    // ensure sorted by secondary key with no duplicates
    ensureDistinct();
    
    // binary search
    return flocc::lower_bound<iterator, SearchK, SearchProj>(VEC_IBEGIN(*vec), VEC_IEND(*vec), key);
  }

  template<typename SearchK, typename SearchProj>
  iterator findSecEnd(SearchK key) { return findSecEnd(VEC_IBEGIN(*vec), key); }

  template<typename SearchK, typename SearchProj>
  iterator findSecEnd(iterator begin, SearchK key) {
    // ensure sorted by secondary key with no duplicates
    ensureDistinct();
    
    // binary search
    return flocc::upper_bound<iterator, SearchK, SearchProj>(begin, VEC_IEND(*vec), key);
  }

  // iterators for different orderings
  // access key and value using it->v0 and it->v1
  // any order:
  inline iterator begin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator end() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }

    // sorted by primary key:
  inline iterator pbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator pend() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }

  // sorted by secondary key:
  inline iterator sbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator send() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }

  #ifdef VEC_CONST
  typedef typename vector<ET>::const_iterator const_iterator;
  inline const_iterator cbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->cbegin();
  }

  inline const_iterator cend() {
    ensureDistinct();
    ensureSorted();
    return vec->cend();
  }

  inline const_iterator cpbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->cbegin();
  }

  inline const_iterator cpend() {
    ensureDistinct();
    ensureSorted();
    return vec->cend();
  }

  inline const_iterator csbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->cbegin();
  }

  inline const_iterator csend() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }
  #else
  typedef iterator const_iterator;
  inline iterator cbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator cend() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }

  inline iterator cpbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator cpend() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }

  inline iterator csbegin() {
    ensureDistinct();
    ensureSorted();
    return vec->begin();
  }

  inline iterator csend() {
    ensureDistinct();
    ensureSorted();
    return vec->end();
  }
  #endif

  /*template<typename SK, typename ProjSK, typename InjectSK> bool operator==(vecmap<ET, K, SK, ProjSK, InjectSK> b) {
    // check sizes match
    if (size() != b.size()) return false;

    // check elements do (ensures both sorted by primary key)
    this_type::iterator it1 = pbegin();
    this_type::iterator it2 = b.pbegin();
    for (;it1 != pend() && it2 != b.pend(); it1++, it2++) {
      if ((*it1) != (*it2)) return false;
    }

    // must be same
    return true;
  }*/

  //bool operator !=(this_type b) {
  //  return !(this == b);
  //}

};


}

/*struct intPair {
  int v0, v1;
  bool operator<(const intPair& b) const {
    return (v0 < b.v0) || ((v0 == b.v0) && ((v1 < b.v1)));
  }
  void print() { std::cout << "(" << v0 << ", " << v1 << ")"; }
};

struct projFstInt {
    static inline int proj(intPair v) { return v.v0; }
    static inline int run(intPair v) { return v.v0; }
};

struct projSndInt {
    static inline int proj(intPair v) { return v.v1; }
    static inline int run(intPair v) { return v.v0; }
};*/


/*using namespace flocc;

int main(int argc, char** argv) {

  // declare vec maps
  typedef flocc::vecmap<intPair, int, int, proj_fst<intPair, int> > t1;
  typedef flocc::vecmap<intPair, int, int, projFstInt > t2;
  typedef flocc::vecmap<intPair, int, int, projSndInt > t3;
  t1 map1;
  t2 map2;
  t3 map3;

  // TODO should we just disallow adding duplicates in the first place?
  // currently it will throw away and pairs with the same fst value.

  // insert data
  for (int i = 0; i < 100; i++) {
    intPair v;
    v.v0 = rand() % 100;
    v.v1 = rand() % 5;
    map1.push_back(v);
    map2.push_back(v);
    map3.push_back(v);
  }

  std::cout << "100 elements added.\n";

  std::cout << "sizes: " << map1.size() << ", " << map2.size() << ", " << map3.size() << "\n";

  char c;
  std::cin >> c;

  //map1 == map1;
  //map1 == map2;
  //map1 == map3;

  // order by primary key
  t1::iterator it1 = map1.pbegin();
  t2::iterator it2 = map2.pbegin();
  t3::iterator it3 = map3.pbegin();
  for (;it1 != map1.pend() &&
       it2 != map2.pend() &&
       it3 != map3.pend();
       it1++, it2++, it3++) {
    it1->print(); 
    it2->print();
    it3->print(); 
    std::cout << "\n";
  }

  std::cin >> c;

  // order by secondary key
  t1::iterator it1s = map1.sbegin();
  t2::iterator it2s = map2.sbegin();
  t3::iterator it3s = map3.sbegin();
  for (;it1s != map1.send() &&
       it2s != map2.send() &&
       it3s != map3.send();
       it1s++, it2s++, it3s++) {
    it1s->print(); 
    it2s->print();
    it3s->print(); 
    std::cout << "\n";
  }

  // get an individual primary key
  std::cout << "search for primary = 3:\n";
  intPair e = *map1.findPri(3); e.print();
  e = *map2.findPri(3); e.print();
  e = *map3.findPri(3); e.print();

  // get a range of secondary keys
  t1::iterator it1b = map1.findSecBegin(3), it1e = map1.findSecEnd(3);
  t2::iterator it2b = map2.findSecBegin(3), it2e = map2.findSecEnd(3);
  t3::iterator it3b = map3.findSecBegin(3), it3e = map3.findSecEnd(3); 
  std::cout << "\nmap1.findSec(3):\n";
  for (;it1b != it1e; it1b++) { it1b->print(); }
  std::cout << "\nmap2.findSec(3):\n";
  for (;it2b != it2e; it2b++) { it2b->print(); }
  std::cout << "\nmap3.findSec(3):\n";
  for (;it3b != it3e; it3b++) { it3b->print(); }

  std::cout << "\n";
  return 0;

}*/
