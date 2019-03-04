cmake_minimum_required(VERSION 3.4.0)

# -------------------------------------------------------------------------------------------------------------------
#  -- Project information and versioning.

project(geas
        LANGUAGES CXX C)

# -------------------------------------------------------------------------------------------------------------------
#  -- Project build options

option(USE_ADDRESS_SANITIZER "Use GCC Address Sanitizer" OFF)

# -------------------------------------------------------------------------------------------------------------------
#  -- CMake initialisation

# Set build type when none is selected
set(DEFAULT_BUILD_TYPE "Release")
if(NOT CMAKE_BUILD_TYPE AND NOT CMAKE_CONFIGURATION_TYPES)
    message(STATUS "Setting build type to '${DEFAULT_BUILD_TYPE}' as none was specified.")
    set(CMAKE_BUILD_TYPE "${DEFAULT_BUILD_TYPE}" CACHE STRING "Choose the type of build." FORCE)
    # Set the possible values of build type for cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
        "Debug"
        "Release"
        "MinSizeRel"
        "RelWithDebInfo"
    )
endif()

# -------------------------------------------------------------------------------------------------------------------
#  -- Compiler configuration

set(CMAKE_CXX_STANDARD 11)

if(USE_ADDRESS_SANITIZER)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fsanitize=address -fno-omit-frame-pointer")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -fsanitize=address")
endif()

if(APPLE)
    execute_process(COMMAND xcrun --show-sdk-path OUTPUT_VARIABLE OSX_SYSROOT OUTPUT_STRIP_TRAILING_WHITESPACE)
    set(CMAKE_OSX_SYSROOT ${OSX_SYSROOT})
    set(CMAKE_OSX_DEPLOYMENT_TARGET "10.9" CACHE STRING "Minimum OS X deployment version")
endif(APPLE)

# -------------------------------------------------------------------------------------------------------------------
#  -- Geas compilation targets.

include_directories(${PROJECT_SOURCE_DIR})
# --- Libraries ---

add_library(geas_core
    engine/conflict.cc
    engine/persist.cc
    engine/propagator.cc
    engine/state.cc
    solver/branch.cc
    solver/solver.cc
    solver/solver_debug.cc
    utils/MurmurHash3.cc
    utils/Options.cc
    utils/System.cc
    vars/fpvar.cc
    vars/intvar.cc
)
add_library(geas_constraints
    constraints/flow/bipart.cc
    constraints/alldifferent.cc
    constraints/arith.cc
    constraints/bool-linear.cc
    constraints/cumulative.cc
    constraints/difflogic.cc
    constraints/disjunctive.cc
    constraints/element.cc
    constraints/linear.cc
    constraints/linear-ps.cc
    constraints/maximum.cc
    constraints/mdd.cc
    constraints/table.cc
    constraints/values-precede.cc
)

# --- Distributables ---

# Geas C Library
add_library(geas
    c/builtins.cc
    c/geas.cc
)
target_link_libraries(geas geas_core geas_constraints)

install(
    TARGETS geas
    RUNTIME DESTINATION bin
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
)
install(
    DIRECTORY c constraints engine utils vars
    DESTINATION include/geas
    FILES_MATCHING PATTERN "*.h"
)