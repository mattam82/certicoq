#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include <time.h>


extern void body(struct thread_info *);

extern void print_Coq_Init_Datatypes_list(unsigned long long, void (*)(unsigned long long));

extern void print_Coq_Init_Datatypes_nat(unsigned long long);

extern value args[];

/* #define is_ptr(s)  ((_Bool) ((x) & 1) == 0) */

_Bool is_ptr(value s) {
  return (_Bool) Is_block(s);
}

int main(int argc, char *argv[]) {
  value val;
  struct thread_info* tinfo;
  clock_t start, end;
  double msec, sec;
  // Specify number of runs to be executed
  int n = 1;
  if (argc > 0) n = atoi(argv[1]);

  start = clock();
  // Run Coq program
  for (int i = 0; i < n; i ++) {
    tinfo = make_tinfo();
    body(tinfo);
  }
  end = clock();

  val = tinfo -> args[1];
  /* print_Coq_Init_Datatypes_list(val, print_Coq_Init_Datatypes_nat); */
  /* printf("\n"); */

  sec = (double)(end - start)/CLOCKS_PER_SEC;
  msec = 1000*sec;
  printf("Time taken %f seconds %f milliseconds\n", sec, msec);

  return 0;
}
