#ifndef HEADER_H
#define HEADER_H

#include <mpi.h>

#define DEBUG 1
#include "pointer.h"
#include "hashing.h"
#include "vecmaps.h"
#include "reparter.h"
#include "carttops.h"

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
void printVal(const char *v) { printf("%s", v); }
void printVal(nullStruct v) {
  printVal("null");
}
void printVal(int* v) {
  // only safe to print one, as don't know array length
  printVal(*v); 
} 

// MPI STUFF

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

#endif

// Global cartesian communicator
static const int ndims = 1;
static const int maxNodesPerDim = 4096;
static std::vector<int> dimSizes;
static MPI::Cartcomm cartComm;
static int coordRanks[maxNodesPerDim];
static int thisCoord[ndims];
static int thisRank, Nproc, rootRank;


 // user def reduction function
  void userFun98(const void* invec, void *inoutvec, int len, const MPI::Datatype& datatype) {
   const double* in = (const double*)invec;
   double* out = (double*)inoutvec;
   // TODO: WHEN SENDING PROPER DATATYPE, CHANGE (len / sizeof(double)) to len!
   for (int i = 0; i < (len / sizeof(double)); i++) {
     double val2 = out[i];
       out[i] = in[i] + val2;
  
  }
 }

MPI::Op v103;



void run() {
// Init global cartesian topology
thisRank = MPI::COMM_WORLD.Get_rank();
Nproc = MPI::COMM_WORLD.Get_size();
dimSizes = flocc::findBestDims(Nproc, ndims);

bool periods[ndims]; for (int i = 0; i < ndims; i++) periods[i] = false;
cartComm = MPI::COMM_WORLD.Create_cart(ndims, &dimSizes.front(), periods, true);

{
 int coord[ndims];
for (coord[0] = 0; coord[0] < dimSizes[0]; coord[0]++) {
coordRanks[coord[0]] = cartComm.Get_cart_rank(coord);
}

}
rootRank = coordRanks[0];
v103.Init(&userFun98, true);

  int v1;
  v1 = 1000000;
  int v8;
  v8 = 2000000;
  double v15;
  v15 = 0.0;
// BEGIN genFloatList
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN genFloatList\n";
#endif
#ifdef DEBUG
std::cerr << "WARNING: genFloatList ignores par dims and distributions over ALL nodes.\n";
#endif
int v2 = v1 / Nproc + (thisRank < (v1%Nproc) ? 1 : 0);
SPTR(vector<double>) v5(new vector<double>(v2));
for (int v3 = 0; v3 < v2; v3++) {
  double v4 = (double)rand()/RAND_MAX;
  v5->push_back(v4);
}
// END genFloatList
#ifdef DEBUG
std::cerr << thisRank << ") END genFloatList\n";
#endif
// BEGIN readList
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN readList\n";
#endif
      // BEGIN reduceList init
        double v16(v15);
          double v17;
        
      // END reduceList init
      
    std::vector<double >::iterator v13(v12->begin());
    
if (true) {
  std::vector<double >::iterator v6(v5->begin());
    std::vector<double >::iterator v7(v5->end());
  
for (; v6 != v7; v6++) {
    // BEGIN zip consume:
  if (v13 < v12->end()) {    // BEGIN mapList consume:
      double v14;
        v14 = (*v6) * (*v13);
      
      // BEGIN reduceList consume
        v17 = v16 + v14;
          v16 = v17; //(Lf:(Float )) = (Lf:(Float ))
        
      // END reduceList consume
      
    // END mapList consume
    
  }
  // END zip consume
  
}
}
      // BEGIN reduceList fin
      if (true) {
        cartComm.Allreduce(&v17, &<st1>, sizeof(double), MPI_PACKED, v103);
      }
      if (cartComm != cartComm) {
        cartComm.Bcast(&<st1>, sizeof(double), MPI_PACKED, rootRank);
      }
      // END reduceList fin
      
// END readList
#ifdef DEBUG
std::cerr << thisRank << ") END readList\n";
#endif
// BEGIN genFloatList
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN genFloatList\n";
#endif
#ifdef DEBUG
std::cerr << "WARNING: genFloatList ignores par dims and distributions over ALL nodes.\n";
#endif
int v9 = v8 / Nproc + (thisRank < (v8%Nproc) ? 1 : 0);
SPTR(vector<double>) v12(new vector<double>(v9));
for (int v10 = 0; v10 < v9; v10++) {
  double v11 = (double)rand()/RAND_MAX;
  v12->push_back(v11);
}
// END genFloatList
#ifdef DEBUG
std::cerr << thisRank << ") END genFloatList\n";
#endif
// BEGIN printFloat
#ifdef DEBUG
std::cerr << thisRank << ") BEGIN printFloat\n";
#endif
if (thisRank == rootRank) std::cout << v16;
// END printFloat
#ifdef DEBUG
std::cerr << thisRank << ") END printFloat\n";
#endif
// No stream called 'final' found in output streams.
}


int main(int argc, char** argv) {
  MPI::Init(argc, argv);
  int rank = MPI::COMM_WORLD.Get_rank();
  double startTime = MPI::Wtime();

  run();

  double duration = MPI::Wtime() - startTime;
  std::cerr << "\n";
  std::cerr << rank << ") Duration " << duration << "s\n"; 

  MPI::Finalize();
  return 0;
}
//



