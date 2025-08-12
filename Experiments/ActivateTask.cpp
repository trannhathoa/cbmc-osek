//
// Created by Tran Nhat Hoa on 8/12/25.
//
#include <assert.h>
#include "_system.h"
//application
int x = 0;

TASK task1(){
  //  TerminateTask();
  assert(x==0);
  x = 1;
  ActivateTask(_task2);
  x = 2;
}

TASK task2(){
  assert(x==1);
  x = 1;
}