//
// Created by Tran Nhat Hoa on 8/4/25.
//
#include "create_system_from_oil.h"

#include <filesystem>
#include <fstream>
#include <iostream>
#include <regex>
#include <unistd.h>
#include <list>



std::string create_system_from_oil::oil_file;
std::string create_system_from_oil::oil_path;

///task name
std::list<std::string> task_name;
std::string start_task;

///task priority for frame stack
//std::map<irep_idt, int> create_system_from_oil::task_priority;
///task name
//std::map<int, irep_idt> create_system_from_oil::task_id;

//std::string to_uppercase(std::string input) {
//  std::transform(input.begin(), input.end(), input.begin(), ::toupper);
//  return input;
//}

void create_system_from_oil::read_configuration_from_oil_file(){
  std::ifstream file(oil_path+"/"+oil_file);

  if (!file.is_open()) {
    std::cerr << "Cannot open file.\n";
    return;
  }

  std::string line;
  std::string current_task;

//  std::string __task_wrapper;

  std::regex task_regex(R"(TASK\s+(\w+))");
//  std::regex priority_regex(R"(PRIORITY\s*=\s*(\d+);)");
  std::regex autostart_regex(R"(AUTOSTART\s*=\s*TRUE;)");


  while (std::getline(file, line)) {
    std::smatch match;

    // Check for TASK line
    if (std::regex_search(line, match, task_regex)) {
      current_task = match[1];
      if (!current_task.empty()){
        task_name.push_back(current_task);
      }
    } // Check for AUTOSTART inside current TASK
    else if (std::regex_search(line, match, autostart_regex) && !current_task.empty()) {
      start_task = current_task;
    }
  }

  file.close();

  // Output result
  for (const auto& task : task_name) {
    std::cout << "Task: " << task << '\n';
  }
  std::cout << "Starting Task: " << start_task << '\n';
}

void write_header_file(){
  std::ofstream headerFile("_system.h");  // Open header file for writing
  if (headerFile.is_open()) {
    headerFile << "#define  TASK void\n";

    headerFile << "//task id\n";
    int i = 1;
    for (const auto& task : task_name) {
      headerFile << "#define " << "_" << task << " " << i++ << '\n';
    }

    headerFile << "\n";
    headerFile << "TASK TerminateTask();\n";
    headerFile << "TASK ActivateTask(int task);\n";
    headerFile << "TASK ChainTask(int task);\n";
    headerFile << "TASK Schedule();\n";

    headerFile.close();                  // Always close the file
    std::cout << "Write header file (_system.h) successful.\n";
  } else {
    std::cerr << "Failed to open header file (_system.h) for writing.\n";
  }
}

void copy_oil_file(){
//  std::ifstream file(oil_path+"/"+oil_file);
  std::ifstream src(create_system_from_oil::oil_path+"/"
                    +create_system_from_oil::oil_file, std::ios::binary);
  std::ofstream dst("_system.oil", std::ios::binary);

  if (!src || !dst) {
    std::cerr << "Error opening files!" << std::endl;
    return ;
  }

  dst << src.rdbuf(); // Copy contents

  std::cout << "Oil file copied successfully!" << std::endl;
  return ;
}

void write_system_file() {
  std::ofstream systemFile("_system.cpp");  // Open header file for writing
  if (systemFile.is_open()) {
    std::string from_oil = ".oil";
    std::string to_cpp = ".cpp";
    auto oil_file = create_system_from_oil::oil_file;
    auto cpp_file = oil_file;

    size_t start_pos = oil_file.find(from_oil);
    if (start_pos != std::string::npos) {
      cpp_file.replace(start_pos, from_oil.length(), to_cpp);
    }

    systemFile << "#include <assert.h>\n";
    systemFile << "#include \"_system.h\"\n";
    systemFile << "#include \"" << cpp_file << "\""<< "\n";

    systemFile << "\n";
    systemFile << "#define  TASK void\n";

//    systemFile << "\n";
//    systemFile << "//taskid\n";
//    int i = 1;
//    for (const auto& task : task_name) {
//      systemFile << "#define " << "_" << task << " " << i++ << '\n';
//    }

    systemFile << "\n";
    systemFile << "//task\n";
    for (const auto& task : task_name) {
      systemFile << "TASK " << task << "();" << '\n';
    }

    systemFile << "\n";
    systemFile << "//wrapper\n";
    for (const auto& task : task_name) {
      systemFile << "TASK " << "__" << task << "(){" << '\n';
      systemFile << "\t" << "Schedule();" << '\n';
      systemFile << "\t"<< task << "();" << '\n';
      systemFile << "}" << '\n';
    };

    systemFile << "\n";
    systemFile << "//API function implementation\n";
    systemFile << "TASK Schedule() {}\n";
    systemFile << "TASK TerminateTask() {}\n";

    systemFile << "TASK ActivateTask(int task) {\n";
    systemFile << "\t" << "switch(task)" << "\n";
    systemFile << "\t" << "{" << "\n";
    for (const auto& task : task_name) {
      systemFile << "\t" << "case " << "_" << task << ":" << '\n';
      systemFile << "\t\t" << "__" << task << "();" << '\n';
      systemFile << "\t\t"<< "break;" << '\n';
    };
    systemFile << "\t}" << '\n';
    systemFile << "}" << '\n';


    systemFile << "TASK ChainTask(int task) {\n";
    systemFile << "\t" << "switch(task)" << "\n";
    systemFile << "\t" << "{" << "\n";
    for (const auto& task : task_name) {
      systemFile << "\t" << "case " << "_" << task << ":" << '\n';
      systemFile << "\t\t" << "__" << task << "();" << '\n';
      systemFile << "\t\t"<< "break;" << '\n';
    };
    systemFile << "\t}" << '\n';
    systemFile << "}" << '\n';


    systemFile << "int main() {\n";
    if (!start_task.empty())
//      systemFile << "\tActivateTask(" << "_" << start_task << ");\n"; //wrong?
        systemFile << "\t" << "ActivateTask(_" << start_task << ");\n";
    systemFile << "\treturn 0;" << "\n";
    systemFile << "}" << '\n';

    systemFile.close();                  // Always close the file
    std::cout << "Write system file (_system.cpp) successful.\n";
  } else {
    std::cerr << "Failed to open system file (_system.cpp) for writing.\n";
  }
}

int main(int argc, char* args[]) {
  if (argc != 2){
    std::cout << "please specify oil file!" << std::endl;
    return 1;
  }

  create_system_from_oil::oil_file = args[1];

//  char cwd[PATH_MAX];
//  if (getcwd(cwd, sizeof(cwd)) != NULL) {
//    std::cout << "Current working directory: " << cwd << std::endl;
//  } else {
//    perror("getcwd() error");
//    return  0;
//  }
//
//  std::cout << "Command-line arguments:" << std::endl;
//  for(int i = 1; i < argc; ++i)
//  { // Start from index 1 to skip the program name
//    std::cout << "Argument " << i << ": " << args[i] << std::endl;
//  }
//  create_system_from_oil::oil_path = cwd;

  create_system_from_oil::oil_path =  std::filesystem::current_path();
  create_system_from_oil::read_configuration_from_oil_file();

  write_header_file();
  write_system_file();
  copy_oil_file();

//  std::string path =  std::filesystem::current_path();
//  std::ifstream file(path+"/"+filename);
//  std::string h_file = std::string(cwd) + "/" + "system.h";
//  const char* header = h_file.c_str();
//
//  FILE *header_file = fopen(header, "w");
//  if (header_file == NULL) {
//    printf("Error: Could not open file %s for writing.\n", args[1]);
//    return 1;
//  }



  return 0; // Indicate successful execution
}


