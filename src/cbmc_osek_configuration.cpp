//
// Created by Tran Nhat Hoa on 7/27/25.
//

#include "cbmc_osek_configuration.h"

#include <fstream>
#include <iostream>
#include <regex>

const bool SCHEDULE_FULL = true; //full preemption
const bool SCHEDULE_NON = false; //Non-preemptive task

std::string cbmc_osek_configuration::source_file;
std::string cbmc_osek_configuration::oil_file;
std::string cbmc_osek_configuration::source_path;


//list of tasks in the system
std::map<irep_idt, Task> cbmc_osek_configuration::tasks;
///task id
std::map<int, irep_idt> cbmc_osek_configuration::task_id;

///task priority for frame stack
std::map<irep_idt, int> cbmc_osek_configuration::task_priority;
///task schedule type
//std::map<irep_idt, bool> cbmc_osek_configuration::task_schedule_type;

void cbmc_osek_configuration::get_task_attribute_from_oil()
{
  //from filename and path
//  std::cout << "Reading soure files" << std::endl;
//  std::cout << "Current working directory: " << source_path << std::endl;
//  std::cout << "Current working file: " << source_file << std::endl;

  std::string from_cpp = ".cpp";
  std::string to_oil = ".oil";

  oil_file = source_file;
  size_t start_pos = oil_file.find(from_cpp);
  if (start_pos != std::string::npos) {
    oil_file.replace(start_pos, from_cpp.length(), to_oil);
  }

//  std::cout << "Current oil file: " << oil_file << std::endl;

  define_main_task_priority();
  read_configuration_from_oil_file();
}

int cbmc_osek_configuration::get_task_priority(irep_idt task_name){
  return task_priority[id2string(task_name)];
//  return tasks[id2string(task_name)].priority;
}

bool cbmc_osek_configuration::is_schedule_full(irep_idt task_name){
  return tasks[task_name].schedule_type; //SCHEDULE_FULL return true
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
}


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
  std::string task_function;
  std::string _task_id;
  std::string __task_wrapper;
  std::string task_name;

  std::regex taskStartRegex(R"(TASK\s+(\w+)\s*\{)");
  std::regex propertyRegex(R"((\w+)\s*=\s*([^;]+);)");
  std::smatch match;

  Task currentTask;
  bool inTask = false;

  int id = 0;

  while (std::getline(file, line)) {
    // Remove leading/trailing spaces
    line.erase(line.begin(), std::find_if(line.begin(), line.end(), [](unsigned char ch) {
                                            return !std::isspace(ch);
                                          }));
    line.erase(std::find_if(line.rbegin(), line.rend(), [](unsigned char ch) {
                              return !std::isspace(ch);
                            }).base(), line.end());

    if (!inTask) {
      // Start of a TASK
      if (std::regex_search(line, match, taskStartRegex)) {
        currentTask = Task();
        task_name = match[1];
        currentTask.name = task_name;
        task_id[++id] = task_name;
        inTask = true;
      }
    } else {
      // End of TASK
      if (line.find("};") != std::string::npos) {
        tasks[currentTask.name] = currentTask;
        inTask = false;
      }
      // Property inside TASK
      else if (std::regex_search(line, match, propertyRegex)) {
        std::string key = match[1];
        std::string value = match[2];

        // Remove extra spaces from value
        value.erase(value.begin(), std::find_if(value.begin(), value.end(), [](unsigned char ch) {
                                                  return !std::isspace(ch);
                                                }));
        value.erase(std::find_if(value.rbegin(), value.rend(), [](unsigned char ch) {
                                   return !std::isspace(ch);
                                 }).base(), value.end());

        if (key == "SCHEDULE") {
//          currentTask.schedule_type = std::equal(value.begin(), value.end(), "FULL");
          if (std::equal(value.begin(), value.end(), "FULL")) {
            currentTask.schedule_type = SCHEDULE_FULL;
          }
          if (std::equal(value.begin(), value.end(), "NON")) {
            currentTask.schedule_type = SCHEDULE_NON;
          }
        } else if (key == "PRIORITY") {
          currentTask.priority = std::stoi(value);
          task_function = task_name + "()";
          _task_id = "_" + task_name;
          __task_wrapper = "_" + _task_id ;

          task_priority[task_name] = currentTask.priority;
          task_priority[task_function] = currentTask.priority;
          task_priority[_task_id] = currentTask.priority;
          task_priority[__task_wrapper] = currentTask.priority;
        } else if (key == "AUTOSTART") {
          std::string valUpper = value;
          std::transform(valUpper.begin(), valUpper.end(), valUpper.begin(), ::toupper);
          currentTask.autostart = (valUpper == "TRUE");
        }
      }
    }
  }

  // Print parsed tasks
//  for (const auto &[tid, name] : task_id)
//  {
//      std::cout << "id: " << tid << "- TASK: " << tasks[name].name << "\n";
//      std::cout << "  SCHEDULE = " << (tasks[name].schedule_type ? "FULL" : "NON")<< "\n";
//      std::cout << "  PRIORITY = " << tasks[name].priority << "\n";
//      std::cout << "  AUTOSTART = " << (tasks[name].autostart ? "TRUE" : "FALSE") << "\n";
//  }

  file.close();
}

irep_idt cbmc_osek_configuration::get_task_name(int function_id){
  return task_id[function_id];
}

