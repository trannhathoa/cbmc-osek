#define  TASK void
//task id
#define _t1 1
#define _t2 2
#define _t3 3

TASK TerminateTask();
TASK ActivateTask(int task);
TASK ChainTask(int task);
TASK Schedule();
