cmake_minimum_required(VERSION 3.26)
project(lc_interpreter)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_FLAGS "-Wall -Wextra -Werror")

add_executable(lc_interpreter main.cpp)