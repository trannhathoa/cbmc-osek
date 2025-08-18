#include <assert.h>
#include "_system.h"

int x = 0;
TASK t1(){
  assert(x==0);
  x = 1;
  ActivateTask(_t2);
  assert(x==2);
  x = 3;
}

TASK t2(){
  assert(x==1);
  x = 2;
}