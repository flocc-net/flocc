#include <mpi.h>
#include <vector>
#include <cstdlib>
#include <memory>
#include <time.h> // to seed srand
#include <sparsehash/dense_hash_map> // hashmap
#include <cstring> // for strcmp
#include <cstdio> // sprintf
#include <climits> // for hashmap empty key values
#include <cmath> // for hashmap empty key values

// RAND NUMBERS
#define randFloat() ((double)rand()/RAND_MAX)

// BASE TYPES 

typedef struct nullStruct {
  bool operator<(const nullStruct& b) const {
    return false;
  }
  bool operator==(const nullStruct& b) const {
    return true;
  }
} nullStruct;

// PRINTING

void printVal(int v) { printf("%i", v); }
void printVal(double v) { printf("%f", v); }
void printVal(const char *v) { printf("%s", v); }
void printVal(nullStruct v) {
  printVal("null");
}

// HASHING

using google::dense_hash_map;

unsigned hashData ( const void *key, int len )
{
    unsigned char *p = (unsigned char*)key;
    unsigned h = 0;
    int i;
  
    for ( i = 0; i < len; i++ ) {
      h += p[i];
      h += ( h << 10 );
     h ^= ( h >> 6 );
   }
 
   h += ( h << 3 );
   h ^= ( h >> 11 );
   h += ( h << 15 );
 
   return h;
}

template <class T>
struct hash {
  public:
  inline size_t operator()(const T& x) const {
    std::cerr << "Called unimplemented hash<T> class!\n";
    throw -1;
  }
};

template <>
struct hash<int> {
  public:
  inline size_t operator()(const int& x) const {
    return x;
  }
};
const hash<int> intHasher;

template <>
struct hash<bool> {
  public:
  inline size_t operator()(const bool& x) const {
    return x;
  }
};
const hash<bool> boolHasher;

// empty keys for hashmaps
// TODO generate empty values for all structs...
const int intEmpty = INT_MIN;
const double doubleEmpty = NAN; 

// EQUALITY

struct eqcharStar
{
  bool operator()(const char* s1, const char* s2) const
  {
    return (s1 == s2) || (s1 && s2 && strcmp(s1, s2) == 0);
  }
};

struct eqint
{
  bool operator()(const int s1, const int s2) const
  {
    return (s1 == s2);
  }
};

struct eqdouble
{
  bool operator()(const double s1, const double s2) const
  {
    // TODO - change so equal to within an interval.
    return (s1 == s2);
  }
};

struct eqbool
{
  bool operator()(const bool s1, const bool s2) const
  {
    return (s1 == s2);
  }
};

// MPI STUFF

typedef struct NodeLayout {
  // all partition root nodes
  // in this node set
  MPI::Comm *partitionCom;
  int partitionCount, // number of partitions
      partitionRank;  // partition rank of this node

  // all nodes to mirror on in this partition
  MPI::Comm *mirrorCom;
  int mirrorCount, // number of nodes in mirror set
      mirrorRank,  // rank in mirror set of this node
      mirrorRootRank;    // rank of root in mirror set

  // if mirrorRank == mirrorRootRank, then this is a partition
  // head/root node

  // if partitionRank or mirrorRank is -1
  // then this node is not in this node layout

  bool operator==(const NodeLayout& b) const {
    // comparing layouts on a single machine, it should
    // be sufficient to compare communicators, as no other
    // layout should exist ON THIS MACHINE with the same
    // communicators.
    return (partitionCom == b.partitionCom) &&
           (mirrorCom == b.mirrorCom);
  }

  void Free() {
    // free communicators, 
    // ONLY SAFE AT VERY END, as other
    // layouts might use one of the same communicators.
    if (partitionCom != NULL && (*partitionCom) != MPI::COMM_WORLD) partitionCom->Free();
    if (mirrorCom != NULL) mirrorCom->Free();
  }

} NodeLayout;

NodeLayout allNodes;

#define NL_ON_FRINGE(nl) ((nl.mirrorRank == nl.mirrorRootRank) && (nl.mirrorRank >= 0))

// converts the rank of a process in one communicator to it's rank
// in another communicator.
void translateRank(MPI::Comm *srcComm, int srcRank, MPI::Comm *destComm, int *destRank) {
  MPI_Group orig_group, new_group; 
  orig_group = srcComm->Get_group();
  new_group = destComm->Get_group();
  MPI::Group::Translate_ranks(orig_group, 1, &srcRank, new_group, destRank);
} 

//typedef void MPI::Comm::Errhandler_fn(MPI::Comm &, int *, ... );
void throwErrHandler(MPI::Comm &comm, int *errCode, ...) {
  int len = 5000;
  char str[len];
  for (int i = 0; i < len; i++) str[i] = 0;
  MPI::Get_error_string(*errCode, str, len);
  std::cerr << "MPI Error: " << str << "\n";
  throw 1;
}

// allToAll communicate vectors
template <class T>
void exchangePartitions(
  std::vector<T> *inputs, 
  std::vector<T> *output, 
  NodeLayout *layout) {
  // if just one node, return
  const int pcount = layout->partitionCount;
  if (pcount <= 1) { 
    *output = inputs[0];
    return;
  } 

  std::cout << "MAX VECTOR SIZE: " << output->max_size() << "\n\n";

  // alltoall data 
  // inputs 228
  // outV 225 = output
  int sendCnts[pcount]; // 229
  int recvCnts[pcount]; // 230
  int sendDispls[pcount]; // 231
  int recvDispls[pcount]; // 232 

  // send/recv partition sizes
  for (int pid = 0; pid < pcount; pid++) {
    sendCnts[pid] = inputs[pid].size() * sizeof(T);  // sendCnts
    void* ptr = &inputs[pid].front();
    std::cout << "Pointer: " << ptr << "\n\n";
    sendDispls[pid] = MPI::Get_address(ptr); // sendDispls
  }
  //return;
  layout->partitionCom->Alltoall(sendCnts, 1, MPI_INT, recvCnts, 1, MPI_INT);

  // sum counts, and make displacements
  int count; // 233      
  for (int pid = 0; pid < pcount; pid++) {
    recvDispls[pid] = count; // recv displs
    count += recvCnts[pid]; // total bytes to recv
  }
  count /= sizeof(T); // total elements to recv
  output->resize(count); // reserve room for total elements

  // send/recv partitions
  layout->partitionCom->Alltoallv(MPI_BOTTOM, sendCnts, sendDispls, MPI_PACKED,
        &(output->front()), recvCnts, recvDispls, MPI_PACKED);
}

// TIME

#define MAX_TIME_HEADER 1024
int timeRank;
char timeHeader[MAX_TIME_HEADER];
double beginTime, middleTime;

void initTime() {
  // rank
  timeRank = MPI::COMM_WORLD.Get_rank();

  // start time
  beginTime = MPI_Wtime();
  middleTime = beginTime;
}

void logTime(const char* event, double *startTime) {
  if (timeRank == 0) {
    double End = MPI_Wtime();
    std::cerr << timeHeader << "\t" 
              << event << "\t" << (End - (*startTime)) << std::endl;
  }
  middleTime = MPI_Wtime();
}

//int main(int argc, char** argv) {}
