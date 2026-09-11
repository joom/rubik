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

# The generated code includes the raylib helper header, so the core carries
# raylib's own include path to everything that links it.
add_library(rubik_core STATIC native/generated/rubik.cpp)
target_include_directories(rubik_core PUBLIC native/generated native crane/theories/cpp)
target_link_libraries(rubik_core PUBLIC raylib)
target_compile_options(rubik_core PRIVATE
  $<$<CXX_COMPILER_ID:Clang,AppleClang>:-fbracket-depth=1024>)

add_executable(rubik native/main.cpp)
target_link_libraries(rubik PRIVATE rubik_core Threads::Threads)
target_compile_options(rubik PRIVATE
  $<$<CXX_COMPILER_ID:Clang,AppleClang>:-fbracket-depth=1024>
  $<$<CXX_COMPILER_ID:Clang,AppleClang,GNU>:-Wall;-Wextra;-Wpedantic>)

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
