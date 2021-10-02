cmake_minimum_required(VERSION 3.13)
project(All8QueensProblem)
set(CMAKE_CXX_STANDARD 20)

set(Z3_INCLUDE "" CACHE STRING "Include directory of Z3")
set(Z3_LIB "" CACHE STRING "Path to z3lib.(lib|so|...) file")

if (NOT Z3_INCLUDE)
    message("Z3 include directory not set")
else ()
    message(${Z3_INCLUDE})
endif ()

if (NOT Z3_LIB)
    message("Z3 library path not set")
else ()
    message(${Z3_LIB})
endif ()

add_executable(All8QueensProblem All8QueensProblem.cpp)

target_include_directories(All8QueensProblem PRIVATE ${Z3_INCLUDE})
target_link_libraries(All8QueensProblem ${Z3_LIB})
