
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
