#include "_system.h"

int nondet_int();
int speed, maxspeed;

TASK contask(){
  maxspeed = 120;
  while(true){
    speed = nondet_int();;
    if (speed < maxspeed)
      ActivateTask(_inctask);
    else
      ActivateTask(_dectask);
  }
  TerminateTask();
}

TASK inctask(){
  speed++;
  TerminateTask();
}

TASK dectask(){
  speed--;
  TerminateTask();
}