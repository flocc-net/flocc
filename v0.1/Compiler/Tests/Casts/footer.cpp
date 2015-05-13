
int main(int argc, char** argv) {
  MPI::Init(argc, argv);


  double t0 = MPI::Wtime();
  run();
  MPI::COMM_WORLD.Barrier(); // wait for all procs to finish, to get total time
  //usleep(5000000);
  double t1 = MPI::Wtime();
  std::cerr << thisRank << ") finished run\n";
  std::cout.flush();

  MPI::COMM_WORLD.Barrier();
  usleep(500000);
  if (thisRank == 0) std::cout << "\n" << (t1 - t0);

  MPI::Finalize();
  return 0;
}
