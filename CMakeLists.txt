cmake_minimum_required(VERSION 3.24)
project(Rubik LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# Prefer an installed raylib, otherwise fetch an immutable, verified 5.5 archive.
find_package(raylib 5.5 QUIET)
if(NOT raylib_FOUND)
  include(FetchContent)
  set(BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
  set(BUILD_GAMES OFF CACHE BOOL "" FORCE)
  FetchContent_Declare(raylib
    URL https://codeload.github.com/raysan5/raylib/tar.gz/c1ab645ca298a2801097931d1079b10ff7eb9df8
    URL_HASH SHA256=be3443c3fb97f7cbd18ae3f0ea2a73e6c1486128df33b639dce7e44070fc285d
    DOWNLOAD_EXTRACT_TIMESTAMP TRUE)
  FetchContent_MakeAvailable(raylib)
endif()

# raylib's own headers warn under -Wextra, so keep them out of our warning set.
get_target_property(raylib_includes raylib INTERFACE_INCLUDE_DIRECTORIES)
set_target_properties(raylib PROPERTIES
  INTERFACE_SYSTEM_INCLUDE_DIRECTORIES "${raylib_includes}")

find_package(Threads REQUIRED)

if(NOT EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/native/generated/rubik.cpp")
  message(FATAL_ERROR "Run 'opam exec -- make extract' before configuring C++.")
endif()

# The whole program is extracted, entry point included, so the executable is
# the generated file and nothing else. The only hand-written C++ in the tree is
# the binding headers the generated code includes.
add_executable(rubik native/generated/rubik.cpp)
target_include_directories(rubik PRIVATE native/generated native native/Bindings crane/theories/cpp)
target_link_libraries(rubik PRIVATE raylib Threads::Threads)
target_compile_options(rubik PRIVATE
  $<$<CXX_COMPILER_ID:Clang,AppleClang>:-fbracket-depth=1024>)

# The same extracted program, with its entry point renamed away, linked into a
# batch solver. It exists only to produce the word tables the solving chain
# uses; Rocq rechecks every word it prints, so nothing here is trusted.
add_library(rubik_core OBJECT native/generated/rubik.cpp)
target_compile_definitions(rubik_core PRIVATE main=rubik_generated_main)
target_include_directories(rubik_core PRIVATE native/generated native native/Bindings crane/theories/cpp)
target_link_libraries(rubik_core PRIVATE raylib)
target_compile_options(rubik_core PRIVATE
  $<$<CXX_COMPILER_ID:Clang,AppleClang>:-fbracket-depth=1024>)

add_executable(solve_tool tools/solve_tool.cpp $<TARGET_OBJECTS:rubik_core>)
target_include_directories(solve_tool PRIVATE native/generated native native/Bindings crane/theories/cpp)
target_link_libraries(solve_tool PRIVATE raylib Threads::Threads)

# Keep the licensed fonts next to the executable so launch does not depend on cwd.
set(rubik_font_files
  "${CMAKE_CURRENT_SOURCE_DIR}/assets/fonts/IBMPlexSans-Regular.ttf"
  "${CMAKE_CURRENT_SOURCE_DIR}/assets/fonts/IBMPlexSans-SemiBold.ttf"
  "${CMAKE_CURRENT_SOURCE_DIR}/assets/fonts/OFL.txt")
set_property(TARGET rubik APPEND PROPERTY LINK_DEPENDS "${rubik_font_files}")
add_custom_command(TARGET rubik POST_BUILD
  COMMAND ${CMAKE_COMMAND} -E make_directory "$<TARGET_FILE_DIR:rubik>/assets/fonts"
  COMMAND ${CMAKE_COMMAND} -E copy_if_different ${rubik_font_files}
          "$<TARGET_FILE_DIR:rubik>/assets/fonts"
  VERBATIM)
