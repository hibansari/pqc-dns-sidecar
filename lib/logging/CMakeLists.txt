cmake_minimum_required(VERSION 3.0)

project(logging)

set(SOURCES src/log.c)

set(HEADERS include/log.h)

include_directories(include)

add_library(logging ${SOURCES} ${HEADERS})