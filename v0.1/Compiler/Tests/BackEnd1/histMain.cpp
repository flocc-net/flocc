
int main(int argc, char **argv) {
  MPI::Init(argc, argv);
  MPI::Errhandler errHandler = MPI::COMM_WORLD.Create_errhandler(&throwErrHandler);
  MPI::COMM_WORLD.Set_errhandler(errHandler);  

  // seed random numbers
  srand (time(NULL));

  // init consts
  int Nh = 100;
  long N = 1073741824; // remember size is 8 times this = 10.5GB
  int Nproc = MPI::COMM_WORLD.Get_size();

  // the current date/time
  time_t timer = time(NULL);
  struct tm* dateTime = localtime(&timer);
  char *strTime = asctime(dateTime);
  char* strPtr = strTime;
  while (*strPtr != '\0') { if (*strPtr == '\n') *strPtr = '\0'; strPtr++; }
  
  // make log header
  snprintf(timeHeader, MAX_TIME_HEADER, "%s\t%li\t%i\t%i", strTime, N, Nh, Nproc);

  // time the computation
  initTime();
  run();
  logTime("total", &beginTime);

  // cleanup
  MPI::Finalize(); return 0;
}
