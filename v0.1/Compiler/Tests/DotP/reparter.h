#include <vector>
#include <mpi.h>
#include <iostream>

#include "pointer.h"
#include "assert.h"

namespace flocc {

template <typename T, typename OutT>
class reparter {
private:
  const static uint bufSize = 1*1024*1024; // 8MB data  
  const static uint maxBufCount = bufSize / sizeof(T);
  uint N, rank;
  int recvBufSize;
  vector<T> *bufs;
  T *recvBuf;
  MPI::Comm *comm;
  SPTR(OutT) consumer;
  int recvNum;

  #ifdef DEBUG
  unsigned long totalSent, totalRecv;
  #endif

  void send() {
    // send sizes
    int sendCounts[N], recvCounts[N]; // originally num elements
    for (uint n = 0; n < N; n++) sendCounts[n] = bufs[n].size();
    comm->Alltoall(sendCounts, 1, MPI::INT, recvCounts, 1, MPI::INT);

    // prepare to send data
    int sendDispls[N], recvDispls[N], recvCount = 0;
    for (uint n = 0; n < N; n++) {
      void *ptr = &bufs[n].front();
      sendDispls[n] = ptr == NULL ? 0 : MPI::Get_address(ptr);
      recvCounts[n] *= sizeof(T); // now number of bytes
      sendCounts[n] *= sizeof(T); // ..
      recvDispls[n] = recvCount;
      recvCount += recvCounts[n];
    }

    // if recv buffer too small reallocate
    if ((recvBufSize*sizeof(T)) < recvCount) {
      recvBufSize = recvCount/sizeof(T);
      delete [] recvBuf;
      recvBuf = new T[recvBufSize];
    }
    mpiAssert((recvBufSize*sizeof(T)) >= recvCount, "reparter:send: recv buf size is smaller than recv count.");

    // do send
    comm->Alltoallv(MPI::BOTTOM, sendCounts, sendDispls, MPI::PACKED,
      recvBuf, recvCounts, recvDispls, MPI::PACKED);

    // remember how many received
    #ifdef DEBUG
    totalRecv += recvCount/sizeof(T);
    #endif

    // pass to consumer
    mpiAssert((recvCount % sizeof(T)) == 0, "reparter:send: recvCount doesn't divide by sizeof(T)!");
    recvNum = recvCount/sizeof(T);
    if (recvNum > 0)
      consumer->appendBlock(recvBuf, recvNum);

    // make counts 0
    for (uint n = 0; n < N; n++) bufs[n].clear();
  }

  void init() {
    // mpiAssert
    mpiAssert(consumer, "reparter:init: consumer is null pointer.");
    mpiAssert(comm != NULL, "reparter:init: comm is null pointer.");

    // get number nodes
    N = comm->Get_size();
    rank = comm->Get_rank();

    // allocate buffers
    bufs = new vector<T>[N];
  }
 
public:
  reparter(MPI::Comm *comm, SPTR(OutT) consumer): comm(comm), consumer(consumer), 
    #ifdef DEBUG
    totalSent(0), totalRecv(0),
    #endif
    recvBufSize(sizeof(T) * 1024), recvBuf(new T[1024]), recvNum(1) {
    init();
  }

  reparter(SPTR(OutT) consumer): comm(&MPI::COMM_WORLD), consumer(consumer), 
    #ifdef DEBUG
    totalSent(0), totalRecv(0),
    #endif
    recvBufSize(sizeof(T) * 1024), recvBuf(new T[1024]), recvNum(1) {
    init();
  }

  ~reparter() {
    delete [] bufs;
    delete [] recvBuf;
  }

  SPTR(OutT) getConsumer() {
    return consumer;
  }

  inline void push_back(int destNode, T val) {
    mpiAssert(destNode >= 0 && destNode < N, "reparter:push_back: destNode out of range.");

    // remember number sent
    #ifdef DEBUG
    totalSent++;
    #endif

    // if a buffer is full, do a send (check til all are full?)
    if (bufs[destNode].size() >= maxBufCount) 
      send();

    // add to buffer
    bufs[destNode].push_back(val);
  }

  void finish() {
      do send(); while (recvNum > 0);
      
      // show total sent
      #ifdef DEBUG
      std::cerr << MPI::COMM_WORLD.Get_rank() << ") reparter total sent: " << totalSent << "\n"
                << MPI::COMM_WORLD.Get_rank() << ") reparter total recv: " << totalRecv << "\n";
      #endif
  }
};

}
