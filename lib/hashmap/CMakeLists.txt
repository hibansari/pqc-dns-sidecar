cmake_minimum_required(VERSION 3.0)

project(hashmap)

set(SOURCES src/map.c)

set(HEADERS include/map.h)

include_directories(include)

add_library(hashmap ${SOURCES} ${HEADERS})