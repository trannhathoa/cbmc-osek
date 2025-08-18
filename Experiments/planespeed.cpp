#include "_system.h"

int nondet_int();
int speed, maxspeed;

TASK contask(){
  maxspeed = 900;
  speed = nondet_int();;
  while(true){
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