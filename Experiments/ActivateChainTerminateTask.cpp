//
// Created by Tran Nhat Hoa on 8/12/25.
//
//
// Created by Tran Nhat Hoa on 8/10/25.
//
#include <assert.h>
#include "_system.h" //added

int x = 0;

TASK t1(){ //keep //3
  assert(x==0);
  x = 1;
  ActivateTask(_t2); //modified
  assert(x==2);
  x = 3;
}

TASK t2(){ //keep //2
  assert(x==1);
  x = 2;
  ChainTask(_t3); //modified
  x = 4;
}

TASK t3(){ //keep
  assert(x==3);
  x = 5;
}