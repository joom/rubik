#include "rubik.h"

#include <cstdio>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <string>
#include <string_view>

int main(int argc, char **argv) {
  bool smoke = false;
  std::string screenshot;
  if (argc == 3 && std::string_view(argv[1]) == "--smoke") {
    smoke = true;
    screenshot = argv[2];
  } else if (argc != 1) {
    std::cerr << "Usage: rubik [--smoke screenshot.png]\n";
    return 2;
  }
  int code = 0;
  try {
    code = program(smoke, screenshot) ? 0 : 1;
  } catch (const std::exception &error) {
    std::cerr << "Rubik: " << error.what() << '\n';
    code = 1;
  }
  // A search deep enough to outlive the window is abandoned rather than waited
  // for, so leave without running destructors it might still be racing.
  std::fflush(nullptr);
  std::_Exit(code);
}
