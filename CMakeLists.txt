cmake_minimum_required(VERSION 3.17)
project(os_course_work)

set(CMAKE_CXX_STANDARD 17)

set(SOCI_SOURCE_DIR "${PROJECT_SOURCE_DIR}/soci")
set(CMAKE_MODULE_PATH ${SOCI_SOURCE_DIR}/cmake ${CMAKE_MODULE_PATH})
set(CMAKE_MODULE_PATH ${SOCI_SOURCE_DIR}/cmake/modules ${CMAKE_MODULE_PATH})
find_package(Soci REQUIRED)
list(APPEND LIBS ${SOCI_LIBRARY} ${SOCI_sqlite3_PLUGIN})

find_package(Boost 1.75 COMPONENTS program_options log REQUIRED)
include_directories( ${Boost_INCLUDE_DIR} )
list(APPEND LIBS ${Boost_LIBRARIES})

add_executable(${PROJECT_NAME} main.cpp helpers.h)

target_link_libraries(${PROJECT_NAME} PRIVATE ${LIBS})
