/* mcpp_lib.h: declarations of libmcpp exported (visible) functions */
#ifndef _MCPP_LIB_H
#define _MCPP_LIB_H

#ifndef _MCPP_OUT_H
#include    "mcpp_out.h"            /* declaration of OUTDEST   */
#endif

#if _WIN32 || _WIN64 || __CYGWIN__ || __CYGWIN64__ || __MINGW32__   \
            || __MINGW64__
#if     DLL_EXPORT || (__CYGWIN__ && PIC)
#define DLL_DECL    __declspec( dllexport)
#elif   DLL_IMPORT
#define DLL_DECL    __declspec( dllimport)
#else
#define DLL_DECL
#endif
#else
#define DLL_DECL
#endif

extern DLL_DECL int     mcpp_lib_main( int argc, char ** argv, processing_data_t* processingData);
extern DLL_DECL int     mcpp_lib_main_ext( int argc, char ** argv);
extern DLL_DECL void    mcpp_reset_def_out_func(processing_data_t* processingData);
extern DLL_DECL void    mcpp_set_out_func(
                    processing_data_t* processingData,
                    int (* func_fputc)  ( int c, OUTDEST od, processing_data_t* processingData),
                    int (* func_fputs)  ( const char * s, OUTDEST od, processing_data_t* processingData),
                    int (* func_fprintf)( OUTDEST od, processing_data_t* processingData, const char * format, ...)
                    );
extern DLL_DECL void    mcpp_use_mem_buffers( int tf, processing_data_t* processingData);
extern DLL_DECL char *  mcpp_get_mem_buffer( OUTDEST od, processing_data_t* processingData);
#endif  /* _MCPP_LIB_H  */
