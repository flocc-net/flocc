#include "header.h"

using namespace flocc;

struct intPair {
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
};

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

  // copy data between them
  SPTR_CLASS<t1> pmap1(&map1);
  SPTR_CLASS<t2> pmap2(&map2);
  map2.assign(pmap1);
  map1.assign(pmap2);

  // search sec key
  map3.findSecEnd<int, projSndInt>(map3.begin(), 5);

  std::cout << "\n";
  return 0;

}
