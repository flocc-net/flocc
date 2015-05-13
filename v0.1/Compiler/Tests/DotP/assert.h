#ifndef ASSERT_H
#define ASSERT_H

#include <iostream>
#include <mpi.h>

inline void mpiAssert(bool test, const char* str) {
  #ifdef DEBUG
  if (!test) {
    std::cerr << MPI::COMM_WORLD.Get_rank() << ") assertion failed: " << str << "\n";
    throw 1;
  }
  #endif
}

#endif
