#include <assert.h>
#include "_system.h"
#include "TerminateTask.cpp"

#define  TASK void

//task
TASK t1();
TASK t2();

//wrapper
TASK __t1(){
	Schedule();
	t1();
}
TASK __t2(){
	Schedule();
	t2();
}

//API function implementation
TASK Schedule() {}
TASK TerminateTask() {}
TASK ActivateTask(int task) {
	switch(task)
	{
	case _t1:
		__t1();
		break;
	case _t2:
		__t2();
		break;
	}
}
TASK ChainTask(int task) {
	switch(task)
	{
	case _t1:
		__t1();
		break;
	case _t2:
		__t2();
		break;
	}
}
int main() {
	ActivateTask(_t1);
	return 0;
}
