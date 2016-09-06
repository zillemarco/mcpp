cmake_minimum_required(VERSION 3.5.2 FATAL_ERROR)

if(MSVC)
    set(PATCH_FILE_NAME visualc.dif)
    set(MAKE_FILE_NAME visualc.mak)
else()
    message(FATAL_ERROR "Unrecognized compiler")
endif()

execute_process(COMMAND cp ${PROJECT_SOURCE_DIR}/noconfig/noconfig.h ${PROJECT_SOURCE_DIR}/src/noconfig.h)
execute_process(COMMAND patch ${PROJECT_SOURCE_DIR}/src/noconfig.h ${PROJECT_SOURCE_DIR}/noconfig/${PATCH_FILE_NAME})
execute_process(COMMAND cp ${PROJECT_SOURCE_DIR}/noconfig/${MAKE_FILE_NAME} ${PROJECT_SOURCE_DIR}/src/Makefile)

file(READ ${PROJECT_SOURCE_DIR}/src/Makefile makefile)

string(REPLACE "$_lib_dir_$" "${CMAKE_INSTALL_PREFIX}/lib" makefile ${makefile})
string(REPLACE "$_inc_dir_$" "${CMAKE_INSTALL_PREFIX}/include" makefile ${makefile})

file(WRITE ${PROJECT_SOURCE_DIR}/src/Makefile ${makefile})

file(MAKE_DIRECTORY "${CMAKE_INSTALL_PREFIX}/lib")
file(MAKE_DIRECTORY "${CMAKE_INSTALL_PREFIX}/include")