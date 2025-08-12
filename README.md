# cbmc-osek
This is a CBMC extension for checking the OSEK applications

We aim to verify applications run on top of OSEK OS. Our approach traverses the control-flow graphs (CFG) of the tasks in the system. This is done using the API function calls and the attributes of the tasks (e.g., priority). The corresponding path realized from the traversal is used to build a formula. Then the formula will be solved by a SAT solver.

The input of the tool is now the source code and the configuration of the OSEK application (*.cpp and *.oil files). The output of the verification is the checking results.

We used CBMC as the base verification tool and modified the way to explore the path realized using the --show-goto-symex-steps parameter. This helps to indicate the API function calls. When traversing the CFG of each task, we check whether the function called is an API of OSEK (TerminateTask, ActivateTask, ChainTask, etc.) and re-order the steps of the execution of the tasks following their attributes (e.g., priority). This is done using a special data structure called "open-stack". We can perform the operations _push_ and _pop_ as a normal stack; however, we added a new operation to push and order a new element in this stack using its attributes. That helps to realize the execution path of the OSEK application. The necessary steps of the verification are indicated below:

1. The source code and the configuration of the OSEK application (*.cpp and *.oil file) need some information added to conform to C++ source code. We do that by reading the configuration file (*.oil) and creating verification files named _system.cpp, _system.h, and _system.oil. The module **create_system_from_oil** will do this task.


2. We check the OSEK application by running the following command: CBMC --show-goto-symex-steps _system.cpp.

The corresponding modified source code from the CBMC version 6.5.0 (cbmc-6.5.0-4-gfab67109ec-dirty) is put in this repository (in the src directory). The experiments directory contains some simple applications to check.
