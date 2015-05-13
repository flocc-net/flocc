#ifndef HEADER_H
#define HEADER_H

#include <cmath>
#include <mpi.h>
#include <vector>
#include <sparsehash/dense_hash_map> // hashmap

#define DEBUG 1
#include "pointer.h"
#include "hashing.h"
#include "vecs.h"
#include "vecmaps.h"
#include "reparter.h"
#include "carttops.h"

// MATH

int ipow(int base, int exp) {
    int result = 1;
    while (exp)
    {
        if (exp & 1)
            result *= base;
        exp >>= 1;
        base *= base;
    }

    return result;
}

int mandelbrot_xy(double x0, double y0) {
  double x2 = 0.0, y2 = 0.0, x = 0.0, y = 0.0;
  int d = 0;
  while (d < 1000 && (x2+y2) <= 4.0) {
    x2 = x*x; y2 = y*y;
    y = 2.0 * x * y * y0;
    x = x2 - y2 + x0;
    d++;
  }
  if (d >= 1000) return 0;
  else return d;
}

// BASE TYPES 

typedef struct nullStruct {
  bool operator<(const nullStruct& b) const {
    return false;
  }
  bool operator==(const nullStruct& b) const {
    return true;
  }
} nullStruct;

typedef struct intPair {
  int v0, v1;
} intPair;
void printVal(intPair v) {
  printf("(%i, %i)", v.v0, v.v1);
}

// PRINTING

void printVal(int v) { printf("%i", v); }
void printVal(double v) { printf("%f", v); }
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

// TODO FIX SO WORKS WITH NON 1 RANGES!
// partitions a dense integer range from begin (inc) to end (not inc) in steps of step
intPair partitionIntRange(int begin, int end, int step, int pcount, int prank) {
  int rangeSz = (end-begin)/step;
  int rangeDiv = rangeSz / pcount;
  int rangeMod = rangeSz % pcount;

  int pbegin, pend;
  if (prank < rangeMod) { 
    pend = step;
    pbegin = prank*step;
  } else {
    pend = 0;
    pbegin = rangeMod*step;
  }

  pbegin += (prank * rangeDiv * step) + begin;
  pend += pbegin + rangeDiv;

  intPair res = {pbegin, pend};
  return res;
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
