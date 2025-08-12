//
// Created by Tran Nhat Hoa on 8/10/25.
//
#include <assert.h>
#include "_system.h" //added

int x = 0;

TASK t1(){ //keep //3
  assert(x==0);
  x = 1;
  ChainTask(_t2); //modified
  x = 4;
}

TASK t2(){ //keep //2
  assert(x==1);
  ChainTask(_t3); //modified
  x = 2;
}

TASK t3(){ //keep
  assert(x==2);
  x = 3;
}