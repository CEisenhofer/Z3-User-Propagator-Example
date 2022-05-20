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

add_executable(All8QueensProblem example.cpp common.h user_propagator.h user_propagator_with_theory.h user_propagator_with_theory2.h user_propagator_subquery_maximisation.h user_propagator_internal_maximisation.h user_propagator_created_maximisation.h user_propagator_higher_dimension.h big_num.cpp big_num.h disjointness.cpp sorting1.cpp sorting2.cpp sorting3.cpp sorting4.cpp sorting5.cpp sorting6.cpp sorting7.cpp sorting8.cpp opt_sorting.cpp nqueens.cpp distinctness.cpp)

target_include_directories(All8QueensProblem PRIVATE ${Z3_INCLUDE})
target_link_libraries(All8QueensProblem PRIVATE ${Z3_LIB})
