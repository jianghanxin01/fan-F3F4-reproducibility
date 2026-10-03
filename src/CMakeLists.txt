cmake_minimum_required(VERSION 3.15)
project(fan_ramsey17 LANGUAGES CXX)

if(NOT CMAKE_CONFIGURATION_TYPES AND NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Build type" FORCE)
endif()

find_package(Threads REQUIRED)

add_executable(fan_ramsey17
    main.cpp
    checkpoint_io.hpp
    fan_solver.cpp
    fan_solver.hpp
    symmetry.hpp
    catalog.hpp
    vendor/minisat/minisat/core/Solver.cc
    vendor/minisat/minisat/utils/Options.cc
    vendor/minisat/minisat/utils/System.cc
)
target_compile_features(fan_ramsey17 PRIVATE cxx_std_17)
set_target_properties(fan_ramsey17 PROPERTIES CXX_EXTENSIONS OFF)
target_include_directories(fan_ramsey17 PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/vendor"
    "${CMAKE_CURRENT_SOURCE_DIR}/vendor/minisat"
    "${CMAKE_CURRENT_SOURCE_DIR}/vendor/nlohmann"
)
target_compile_definitions(fan_ramsey17 PRIVATE MINISAT_NO_ZLIB)
target_link_libraries(fan_ramsey17 PRIVATE Threads::Threads)

if(MSVC)
    # Static CRT: the Windows binary does not need the Visual C++ runtime installer.
    set_property(TARGET fan_ramsey17 PROPERTY
        MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:Debug>")
    target_compile_options(fan_ramsey17 PRIVATE /EHsc /utf-8)
    target_compile_definitions(fan_ramsey17 PRIVATE _CRT_SECURE_NO_WARNINGS)
else()
    target_compile_options(fan_ramsey17 PRIVATE $<$<CONFIG:Release>:-O3>)
endif()

# No -march=native or architecture-specific instruction flags: keep the build portable.
install(TARGETS fan_ramsey17 RUNTIME DESTINATION .)

# Optional generator for the six finite-domain proof certificates.
add_executable(fan_tail_certify csp_rows.cpp)
target_compile_features(fan_tail_certify PRIVATE cxx_std_17)
set_target_properties(fan_tail_certify PROPERTIES CXX_EXTENSIONS OFF)
if(MSVC)
    set_property(TARGET fan_tail_certify PROPERTY
        MSVC_RUNTIME_LIBRARY "MultiThreaded$<$<CONFIG:Debug>:Debug>")
    target_compile_options(fan_tail_certify PRIVATE /EHsc /utf-8)
else()
    target_compile_options(fan_tail_certify PRIVATE $<$<CONFIG:Release>:-O3>)
endif()
