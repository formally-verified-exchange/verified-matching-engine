cmake_minimum_required(VERSION 3.14)
project(matcher LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

# TLSF allocator (header-only)
add_subdirectory(tlsf-allocator)

# Engine is header-only; create an interface target
add_library(engine INTERFACE)
target_include_directories(engine INTERFACE src)
target_link_libraries(engine INTERFACE tlsf)

# Correctness tests
add_executable(test_correctness tests/test_correctness.cpp)
target_link_libraries(test_correctness PRIVATE engine)

# Performance benchmark
add_executable(test_performance tests/test_performance.cpp)
target_link_libraries(test_performance PRIVATE engine)
target_compile_options(test_performance PRIVATE -O3 -march=native)

# Conformance harness (TLA+ trace replay)
add_executable(conformance_harness tools/conformance/conformance_harness.cpp)
target_link_libraries(conformance_harness PRIVATE engine)

# Shadow model test (random differential testing)
add_executable(shadow_test tools/conformance/shadow_test.cpp)
target_link_libraries(shadow_test PRIVATE engine)
