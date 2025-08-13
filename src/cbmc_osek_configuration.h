//
// Created by Tran Nhat Hoa on 7/27/25.
//

#ifndef CBMC_CBMC_OSEK_CONFIGURATION_H
#define CBMC_CBMC_OSEK_CONFIGURATION_H
#include "irep.h"
#include <map>

const int No_Function = -1;
const int Normal_Function = 0;
const int TerminateTask = 1;
const int ActivateTask = 2;
const int Schedule = 3;
const int Schedule_after_ActivateTask = 4;
const int ChainTask = 5;
const int Schedule_after_ChainTask = 6;

struct Task {
  std::string name;
  bool schedule_type = true; //SCHEDULE_FULL
  int priority = 0;
  bool autostart = false;
};

class cbmc_osek_configuration
{
private:

  static void define_main_task_priority();

  ///task priority for frame stack
  static std::map<irep_idt, int> task_priority;
  ///task name
  static std::map<int, irep_idt> task_id;
  static void read_configuration_from_oil_file();

//  static void define_task_priority();
  //    static void define_task_id();

public:
  static std::string source_file;
  static std::string oil_file;
  static std::string source_path;
  static int get_function_code(const irep_idt function_name);
  static irep_idt get_task_name(int function_id);
  static int get_task_priority(irep_idt task_name);
  static void get_task_attribute_from_oil();

//  static std::map<irep_idt, bool> task_schedule_type;
  static std::map<irep_idt, Task> tasks;
  static bool is_schedule_full(irep_idt task_name);
};

#endif //CBMC_CBMC_OSEK_CONFIGURATION_H
