#include <assert.h>

#include "_system.h"

int x = 0;

TASK t2() {
  assert(x==20);
  x = 10;
  TerminateTask(); //end t2
  x = 2; //will be ignored
}

TASK t1(){
  ActivateTask(_t2); //directly call for testing purpose
  assert(x==0); //checked 10!
  x = 20;
  TerminateTask(); //end t1
  x = 3; //will be ignored
}
