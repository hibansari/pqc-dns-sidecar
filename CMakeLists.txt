cmake_minimum_required(VERSION 3.0)

project(pqc-dns-sidecar)

add_subdirectory(lib/hashmap)

set(SOURCES
    src/daemon.c
    src/dns_message.c
    src/packedrr.c
    src/question.c
    src/resource_record.c
    src/rrfrag.c
)

set(HEADERS
    include/dns_message.h
    include/packedrr.h
    include/question.h
    include/resource_record.h
    include/rrfrag.h
)

include_directories(
    include
    lib/hashmap/include
)

add_executable(pqc-dns-sidecar ${SOURCES} ${HEADERS})

target_link_libraries(pqc-dns-sidecar PRIVATE
    hashmap
    netfilter_queue
    m
)