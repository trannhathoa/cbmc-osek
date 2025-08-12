//
// Created by Tran Nhat Hoa on 7/27/25.
//

#include "cbmc_osek_configuration.h"

#include <fstream>
#include <iostream>
#include <regex>

std::string cbmc_osek_configuration::source_file;
std::string cbmc_osek_configuration::oil_file;
std::string cbmc_osek_configuration::source_path;

///task priority for frame stack
std::map<irep_idt, int> cbmc_osek_configuration::task_priority;
///task name
std::map<int, irep_idt> cbmc_osek_configuration::task_id;

void cbmc_osek_configuration::get_task_attribute()
{
  //from filename and path
  std::cout << "Current working directory: " << source_path << std::endl;
  std::cout << "Current working file: " << source_file << std::endl;

  std::string from_c = ".cpp";
  std::string to_oil = ".oil";

  oil_file = source_file;
  size_t start_pos = oil_file.find(from_c);
  if (start_pos != std::string::npos) {
    oil_file.replace(start_pos, from_c.length(), to_oil);
  }

  std::cout << "Current oil file: " << oil_file << std::endl;

  define_main_task_priority();
  read_configuration_from_oil_file();
}

int cbmc_osek_configuration::get_task_priority(irep_idt task_name){
  return task_priority[id2string(task_name)];
}

//get from configuration file
void cbmc_osek_configuration::define_main_task_priority(){
  task_priority["__CPROVER__start"] = 0;
  task_priority["__CPROVER_initialize"] = 0;
  task_priority["main"] = -1;

  task_priority["ActivateTask"] = 0;
  task_priority["TerminateTask"] = 0;
  task_priority["Schedule"] = 0;
  task_priority["ChainTask"] = 0;

//  //before T1 executes, TASK1 is run first to make a stack frame.
//  //We can use this frame to order the execution of T1 (TASK1 is a wrapper frame of T1)
//  task_priority["_T1"] = 1;
//  task_priority["TASK1"] = 1; //wrapper
//  task_priority["_T2"] = 2;
//  task_priority["TASK2"] = 2;
//  task_priority["_T3"] = 3;
//  task_priority["TASK3"] = 3;
}

//void cbmc_osek_configuration::define_task_id(){
//  task_id[1] = "Task1";
//  task_id[2] = "Task2";
//  task_id[3] = "Task3";
//}
//std::string to_uppercase(std::string input) {
//  std::transform(input.begin(), input.end(), input.begin(), ::toupper);
//  return input;
//}
int cbmc_osek_configuration::get_function_code(irep_idt const function_name){
  if (as_string(function_name).find("TerminateTask") != std::string::npos)
    return TerminateTask;
  if (as_string(function_name).find("ActivateTask") != std::string::npos)
    return ActivateTask;
  if (as_string(function_name).find("ChainTask") != std::string::npos)
    return ChainTask;
  if (as_string(function_name).find("Schedule") != std::string::npos)
    return Schedule;

//  if (function_name.compare("ActivateTask") == 0)
//    return ActivateTask;
//  if (function_name.compare("ChainTask") == 0)
//    return ChainTask;
//  if (function_name.compare("Schedule") == 0)
//    return Schedule;

  return Normal_Function;
}
void cbmc_osek_configuration::read_configuration_from_oil_file(){
  std::ifstream file(source_path+"/"+oil_file);

  if (!file.is_open()) {
    std::cerr << "Cannot open file.\n";
    return;
  }

  std::string line;
  std::string current_task;
  std::string task;
  std::string _task_id;
  std::string __task_wrapper;

  std::regex task_regex(R"(TASK\s+(\w+))");
  std::regex priority_regex(R"(PRIORITY\s*=\s*(\d+);)");

  int id = 0;
  while (std::getline(file, line)) {
    std::smatch match;

    // Check for TASK line
    if (std::regex_search(line, match, task_regex)) {
      current_task = match[1];
    }
    // Check for PRIORITY inside current TASK
    else if (std::regex_search(line, match, priority_regex) && !current_task.empty()) {
      int priority = std::stoi(match[1]);

      task_id[++id] = current_task;
      task = current_task + "()";
      _task_id = "_" + task;
      __task_wrapper = "_" + _task_id ;

      task_priority[task] = priority;
      task_priority[_task_id] = priority;
      task_priority[__task_wrapper] = priority;

      current_task.clear();  // reset after getting task info
      task.clear();
      _task_id.clear();
      __task_wrapper.clear();
    }
  }

  file.close();
  // Output result
  for (const auto& [task, priority] : task_priority) {
    std::cout << "Task: " << task << " | Priority: " << priority << '\n';
  }
}
irep_idt cbmc_osek_configuration::get_task_name(int function_id){
  return task_id[function_id];
}

//----------------------------------