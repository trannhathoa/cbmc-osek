//
// Created by Tran Nhat Hoa on 8/4/25.
//

#ifndef CBMC_CREATE_SYSTEM_FROM_OIL_H
#define CBMC_CREATE_SYSTEM_FROM_OIL_H

#include <list>
#define irep_idt std::string

class create_system_from_oil
{
//private:
  ///task name
//  static std::list<std::string>  task_name;

public:
  static std::string oil_file;
  static std::string oil_path;
  static std::string system_file;
  ///task priority for frame stack
//  static std::map<irep_idt, int> task_priority;
  ///task name
//  static std::map<int, irep_idt> task_id;

  static void read_configuration_from_oil_file();
};

#endif //CBMC_CREATE_SYSTEM_FROM_OIL_H
