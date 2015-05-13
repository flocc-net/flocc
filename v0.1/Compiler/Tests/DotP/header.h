#ifndef HEADER_H
#define HEADER_H

#include <cmath>
#include <mpi.h>

//#define DEBUG 1
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
