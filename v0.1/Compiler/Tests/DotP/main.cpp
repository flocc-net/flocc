
int main(int argc, char** argv) {
  MPI::Init(argc, argv);
  int rank = MPI::COMM_WORLD.Get_rank();
  int nproc = MPI::COMM_WORLD.Get_size();
  double startTime = MPI::Wtime();

  run();

  double duration = MPI::Wtime() - startTime;
  if (rank == 0) {
    std::cerr << "prog\t" << nproc << "\t" << duration << "\n"; 
  }

  MPI::Finalize();
  return 0;
}
