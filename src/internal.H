/*-
 * Copyright (c) 1998, 2002-2008 Kiyoshi Matsui <kmatsui@t3.rim.or.jp>
 * All rights reserved.
 *
 * Some parts of this code are derived from the public domain software
 * DECUS cpp (1984,1985) written by Martin Minow.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 *                          I N T E R N A L . H
 *      I n t e r n a l   D e f i n i t i o n s   f o r   M C P P
 *
 * In general, definitions in this file should not be changed by implementor.
 */

#ifndef SYSTEM_H
    #error "system.H" must be included prior to "internal.H"
#endif

#include "../inc/mcpp.h"
#include "mcpp_out.h"

#define EOS             '\0'        /* End of string                */
#define CHAR_EOF        0           /* Returned by get_ch() on eof  */

#define VA_ARGS         (UCHARMAX + 1)      /* Signal of variable arguments */
#define GVA_ARGS        (VA_ARGS * 2)       /* GCC-specific variable args   */
#define AVA_ARGS        (VA_ARGS | GVA_ARGS)/* Any variable arguments       */
#define DEF_PRAGMA      (-1 - AVA_ARGS)     /* _Pragma() pseudo-macro       */
#define DEF_NOARGS      (-2 - AVA_ARGS)     /* #define foo vs #define foo() */
#define DEF_NOARGS_PREDEF_OLD   (DEF_NOARGS - 1)
                        /* Compiler-predefined macro without leading '_'    */
#define DEF_NOARGS_PREDEF   (DEF_NOARGS - 2)/* Compiler-predefined macro    */
#define DEF_NOARGS_STANDARD (DEF_NOARGS - 3)/* Standard predefined macro    */
#define DEF_NOARGS_DYNAMIC  (DEF_NOARGS - 4)/* Standard dynamically defined */

/*
 * These magic characters must be control characters which can't be used
 * in source file.
 */
/* for '#pragma MCPP debug macro_call' and -K option in STD mode.   */
#define MAC_INF         0x18        /* Magic for macro informations */
/* In STD and POST_STD modes (IN_SRC and TOK_SEP are for STD mode only).    */
#define DEF_MAGIC       0x19        /* Magic to prevent recursive expansion */
#define IN_SRC          0x1A        /* Magic of name from source    */
#define RT_END          0x1C        /* Magic of macro rescan boundary   */
#define ST_QUOTE        0x1D        /* Magic for stringizing        */
#define CAT             0x1E        /* Token concatenation delim.   */
#define TOK_SEP         0x1F        /* Magic to wrap expanded macro */
/* In OLD_PREP mode.    */
#define COM_SEP         0x1F        /* Comment of 0-length          */

#define MAC_PARM        0x7F        /* Macro parameter signal       */

/* Special character types  */
#define LET             1           /* Letter (alphabet and _)      */
#define DIG             2           /* Digit                        */
#define DOT             4           /* . might start a number       */
#define PUNC            8           /* Punctuators and operators    */
#define QUO             0x10        /* Both flavors of quotation ",'*/
#define SPA             0x20        /* White spaces                 */
#define HSP             0x40
                    /* Horizontal white spaces (' ', '\t', TOK_SEP) */

/*
 * Codes for operators used in #if expression.
 * The value of the scanned operator is stored in 'openum'.
 */
#define INV             0           /* Invalid, must be zero        */
#define OP_EOE          INV         /* End of expression            */
#define VAL             1           /* Value (operand)              */
#define OP_LPA          2           /* (    */
/* The following are unary.     */
#define FIRST_UNOP      OP_PLU      /* First unary operator         */
#define OP_PLU          3           /* +    */ 
#define OP_NEG          4           /* -    */
#define OP_COM          5           /* ~    */
#define OP_NOT          6           /* !    */
#define LAST_UNOP       OP_NOT      /* Last unary operator          */
/* The following are binary.    */
#define FIRST_BINOP     OP_MUL      /* First binary operator        */
#define OP_MUL          7           /* *    */
#define OP_DIV          8           /* /    */
#define OP_MOD          9           /* %    */
#define OP_ADD          10          /* +    */
#define OP_SUB          11          /* -    */
#define OP_SL           12          /* <<   */
#define OP_SR           13          /* >>   */
#define OP_LT           14          /* <    */
#define OP_LE           15          /* <=   */
#define OP_GT           16          /* >    */
#define OP_GE           17          /* >=   */
#define OP_EQ           18          /* ==   */
#define OP_NE           19          /* !=   */
#define OP_AND          20          /* &    */
#define OP_XOR          21          /* ^    */
#define OP_OR           22          /* |    */
#define OP_ANA          23          /* &&   */
#define OP_ORO          24          /* ||   */
#define OP_QUE          25          /* ?    */
#define OP_COL          26          /* :    */
#define LAST_BINOP      OP_COL      /* Last binary operator         */
/* Parenthesis  */
#define OP_RPA          27          /* )    */
#define OP_END          28          /* End of expression marker     */
#define OP_FAIL         (OP_END + 1)    /* For error returns        */

/*
 * The following are operators used in macro definition only.
 */
/* In STD and POST_STD modes.   */
#define OP_STR          30          /* #    */
#define OP_CAT          31          /* ##   */
#define OP_ELL          32          /* ...  */

/*
 * The following are C source operators or punctuators,
 * not preprocessing operators.
 * Note: "sizeof", "defined" are read as identifier for convenience.
 */
#define OP_1            33  /* Any other single byte ops or puncs   */
                                    /* =, ., ;, [, ], {, }, ','     */
#define OP_2            34  /* Any other two bytes operators        */
                    /* &=, |=, ++, +=, --, -=, ->, %=, *=, /=, ^=,  */
#define OP_3            35  /* Three bytes operators :  <<=, >>=    */
/*
 * The following are operators spelled in digraphs.
 */
/* In STD and POST_STD modes.   */
#define OP_LBRACE_D     0x40        /* <% i.e. {    */
#define OP_RBRACE_D     0x41        /* %> i.e. }    */
#define OP_LBRCK_D      0x42        /* <: i.e. [    */
#define OP_RBRCK_D      0x43        /* :> i.e. ]    */
#define OP_SHARP_D      0x44        /* %: i.e. #    */
#define OP_DSHARP_D     0x45        /* %:%: i.e. ## */
#define OP_DIGRAPH      0x40    /* (OP_*_D & OP_DIGRAPH) == 0x40    */

/*
 * The following are for lexical scanning only.
 */
/* Token types          */
#define NO_TOKEN        0
#define NAM             65          /* Identifier (name, keyword)   */
#define NUM             66          /* Preprocessing number         */
#define STR             67          /* Character string literal     */
#define CHR             69          /* Integer character constant   */

/* In STD and POST_STD modes.   */
#define WSTR            68          /* Wide string literal          */
#define WCHR            70          /* Wide character constant      */

#define OPE             71          /* Operator or punctuator       */
#define SPE             72          /* Unknown token (@ or others)  */
#define SEP             73          /* Token separator or magics    */

/*
 * The following are values of 'mcpp_debug' variable which is set by the
 * arguments of '#pragma MCPP debug' directive.
 */
#define PATH            1
#define TOKEN           2
#define EXPAND          4
#define MACRO_CALL      8
#define IF              16
#define EXPRESSION      32
#define GETC            64
#define MEMORY          128

/* MAC_* represent macro information types for -K option.   */
#define MAC_CALL_START  1
#define MAC_CALL_END    2
#define MAC_ARG_START   3
#define MAC_ARG_END     4

/* MB_ERROR signals wrong multi-byte character sequence.    */
#define MB_ERROR        0x8000

#if MCPP_LIB && HOST_COMPILER == GNUC   \
        && (SYS_FAMILY == SYS_UNIX && SYSTEM != SYS_CYGWIN)
    /* For GCC 4.* on UNIXes    */
#pragma GCC visibility push( hidden)    /* Hide these names from outside    */
#endif


typedef struct processing_data_ processing_data_t;


/*
 * The DEFBUF structure stores information about #defined macros.
 * Note that DEFBUF->parmnames is parameter names catenated with commas,
 * which is saved for the check of redefinition for STD mode.
 * 'parmnames' and 'repl' are allocated to the area succeding to name.
 */
typedef struct defbuf {
        struct defbuf * link;       /* Pointer to next def in chain */
        short           nargs;      /* Number of parameters         */
        char *          parmnames;  /* -> Parameter names catenated by ','  */
        char *          repl;       /* Pointer to replacement text  */
        const char *    fname;      /* Macro is defined in the source file  */
        long            mline;      /*          at the line.        */
        char            push;       /* Push level indicator         */
        char            name[1];    /* Macro name                   */
} DEFBUF;

// Anima ADD
typedef struct mfile {
	FILE* fp;
	char* start;
	char* end;
	char* cur;
} MFILE;
// Anima ADD

/*
 * The FILEINFO structure stores information about open files and macros
 * being expanded.
 */
typedef struct fileinfo {
        char *          bptr;       /* Current pointer into buffer  */
        long            line;       /* Current line number of file  */
        //FILE *          fp;         /* Source file if non-null      */	// Anima ADD
		MFILE *			mf;			/* Source mfile if non-null		*/ 		// Anima ADD
        long            pos;        /* Position next to #include    */
        struct fileinfo *   parent; /* Link to includer             */
        struct ifinfo *     initif; /* Initial ifstack (return there on EOF)*/
        int             sys_header; /* System header file or not    */
        int             include_opt;        /* Specified by -include option */
        const char **   dirp;       /* Include directory the file resides   */
        const char *    src_dir;    /* Directory of source file     */
        const char *    real_fname; /* Real file name               */
        const char *    full_fname; /* Real full path list          */
        char *          filename;   /* File/macro name (maybe changed)      */
        char *          buffer;     /* Buffer of current input line */
#if MCPP_LIB
        /* Save output functions during push/pop of #includes   */
        int (* last_fputc)  ( int c, OUTDEST od, processing_data_t* processingData);
        int (* last_fputs)  ( const char * s, OUTDEST od, processing_data_t* processingData);
        int (* last_fprintf)( OUTDEST od, processing_data_t* processingData, const char * format, ...);
#endif
} FILEINFO;

/*
 * IFINFO stores information of conditional compilation.
 */
typedef struct ifinfo {
        int             stat;       /* State of compilation         */
        long            ifline;     /* Line #if started             */
        long            elseline;   /* Line #else started           */
} IFINFO;

/*
 * These bits are set in IFINFO.stat
 */
#define WAS_COMPILING   1           /* TRUE if compile set at entry */
#define ELSE_SEEN       2           /* TRUE when #else processed    */
#define TRUE_SEEN       4           /* TRUE when #if TRUE processed */

#define compiling       ifstack[0].stat

#define FP2DEST(fp, pd) \
    (fp == pd->fp_out) ? OUT : \
    ((fp == pd->fp_err) ? ERR : \
    ((fp == pd->fp_debug) ? DBG : \
    ((OUTDEST) -1)))

/* VAL_SIGN structure stores information about evaluated number.    */
typedef struct val_sign {
        expr_t          val;        /* Value                        */
        int             sign;       /* Signed, unsigned, error      */
} VAL_SIGN;

/* Values of VAL_SIGN.sign. */
#define SIGNED          1
#define UNSIGNED        0
#define VAL_ERROR       (-1)

/* LINE_COL stores information of line and column data  */
typedef struct line_col {
        long            line;
        size_t          col;
} LINE_COL;

/* Value of macro_line on macro call error.         */
#define MACRO_ERROR     (-1L)

/*
 * Values of insert_sep (flag of insertion of token separator).
 * Used only in POST_STD mode.
 */
#define NO_SEP          0   /* No separator is inserted             */
#define INSERT_SEP      1   /* Next get_ch() insert a separator     */
#define INSERTED_SEP    2   /* Last get_ch() Inserted a separator   */

#define str_eq(s1, s2)  (strcmp(s1, s2) == 0)

#ifndef IO_SUCCESS
#define IO_SUCCESS      0
#endif
#ifndef IO_ERROR
#define IO_ERROR        (errno ? errno : 1)
#endif

/*
 * Externs
 */

/* The minimum translation limits specified by the Standards.       */
typedef struct std_limits_ {
    long    str_len;            /* Least maximum of string len. */
    size_t  id_len;             /* Least maximum of ident len.  */
    int     n_mac_pars;         /* Least maximum of num of pars.*/
    int     exp_nest;           /* Least maximum of expr nest   */
    int     blk_nest;           /* Least maximum of block nest  */
    int     inc_nest;           /* Least maximum of include nest*/
    long    n_macro;            /* Least maximum of num of macro*/
    long    line_num;           /* Maximum source line number   */
} std_limits_t;

/* The boolean flags specified by the execution options.    */
typedef struct option_flags_ {
    int     c;                  /* -C option (keep comments)    */
    int     k;                  /* -k option (keep white spaces)*/
    int     z;      /* -z option (no-output of included file)   */
    int     p;                  /* -P option (no #line output)  */
    int     q;                  /* -Q option (diag to mcpp.err) */
    int     v;                  /* -v option (verbose)          */
    int     trig;               /* -3 option (toggle trigraphs) */
    int     dig;                /* -2 option (toggle digraphs)  */
    int     lang_asm;           /* -a option (assembler source) */
    int     no_source_line;     /* Do not output line in diag.  */
    int     dollar_in_name;     /* Allow $ in identifiers       */
} option_flags_t;


/*
 * Global work_buf[] are used to store #define parameter lists and
 * parms[].name point to them.
 * 'nargs' contains the actual number of parameters stored.
 */
typedef struct param_name_
{
    char *name; /* -> Start of each parameter   */
    size_t len; /* Length of parameter name     */
} param_name_t;

typedef struct params_data_
{
    param_name_t parms[NMACPARS];
    int nargs;                                    /* Number of parameters         */
    char *token_p;                                /* Pointer to the token scanned */
    char *repl_base;                              /* Base of buffer for repl-text */
    char *repl_end;                               /* End of buffer for repl-text  */
    
    #if COMPILER == GNUC
        int gcc2_va_arg; /* GCC2-spec variadic macro     */
    #endif
} params_data_t;

typedef struct location
{                     /* Where macro or arg locate    */
    long start_line;  /* Beginning at 1   */
    size_t start_col; /* Beginning at 0   */
    long end_line;
    size_t end_col;
} LOCATION;
typedef struct magic_seq
{                      /* Data of a sequence inserted between tokens   */
    char *magic_start; /* First MAC_INF sequence   */
    char *magic_end;   /* End of last MAC_INF seq  */
    int space;         /* Space succeeds or not    */
} MAGIC_SEQ;

/* Variables for macro notification mode    */
typedef struct macro_inf
{                       /* Informations of a macro  */
    const DEFBUF *defp; /* Definition of the macro  */
    char *args;         /* Arguments, if any        */
    int num_args;       /* Number of real arguments */
    int recur;          /* Recurrence of this macro */
    LOCATION locs;      /* Location of macro call   */
    LOCATION *loc_args; /* Location of arguments    */
} MACRO_INF;

typedef struct macro_replace_data
{
    const DEFBUF *def; /* Macro definition             */
    int read_over;     /* Has read over repl-list      */
    /* 'read_over' is never used in POST_STD mode and in compat_mode*/
} macro_replace_data_t;     /* Macros currently replacing   */


typedef struct macros_data_
{
    MACRO_INF *mac_inf;
    int max_mac_num;    /* Current num of elements in mac_inf[] */
    int mac_num;        /* Index into mac_inf[]     */
    LOCATION *in_src;   /* Location of identifiers in macro arguments   */
    int max_in_src_num; /* Current num of elements in in_src[]  */
    int in_src_num;     /* Index into in_src[]      */
    int trace_macro;    /* Enable to trace macro infs   */
    int has_pragma; /* Flag of _Pragma() operator       */
    macro_replace_data_t replacing[RESCAN_LIMIT];
    
    int compat_mode;
    /* Expand recursive macro more than Standard (for compatibility with GNUC)  */
    #if COMPILER == GNUC
    int ansi; /* __STRICT_ANSI__ flag     */
    #endif

    int rescan_level; /* Times of macro rescan    */
    jmp_buf jump;
    char *arglist_pre[NMACPARS]; /* Pointers to args     */
} macros_data_t;

#define EXP_MAC_IND_MAX     16
#define MAX_CAT_LINE        256

/* Information of current expanding macros for diagnostic   */
typedef struct expanding_macro_ {
    const char *    name;       /* Name of the macro just expanded  */
    int             to_be_freed;    /* Name should be freed later   */
} expanding_macro_t;

/* Information on line catenated by <backslash><newline>    */
/* and by line-crossing comment.  This is for -K option.    */
typedef struct catenated_line {
    long    start_line;         /* Starting line of catenation      */
    long    last_line;          /* Ending line of catanation        */
    size_t  len[ MAX_CAT_LINE + 1];
                        /* Length of successively catenated lines   */
} CAT_LINE;

#if MCPP_LIB
    typedef struct  mem_buf {
        char *  buffer;
        char *  entry_pt;
        size_t  size;
        size_t  bytes_avail;
    } MEMBUF;
#endif

typedef struct support_data_ {
    expanding_macro_t expanding_macro[EXP_MAC_IND_MAX];

    int  exp_mac_ind;    /* Index into expanding_macro[] */
    int  in_token;       /* For token scanning functions */
    int  in_string;      /* For get_ch() and parse_line()*/
    int  squeezews;
    CAT_LINE bsl_cat_line; /* Datum on the last catenated line by <backslash><newline> */
    CAT_LINE com_cat_line; /* Datum on the last catenated line by a line-crossing comment  */

    int dollar_diagnosed;   /* Flag of diagnosing '$'   */
    
#if MCPP_LIB
    int  use_mem_buffers;
    MEMBUF   mem_buffers[ NUM_OUTDEST];
#endif

    int  cr_converted;

} support_data_t;

typedef struct inc_list {       /* List of directories or files     */
    char *      name;           /* Filename or directory-name       */
    size_t      len;                    /* Length of 'name'         */
} INC_LIST;

#define INIT_NUM_INCLUDE    32          /* Initial number of incdir[]   */
#define INIT_NUM_FNAMELIST  256         /* Initial number of fnamelist[]    */
#define INIT_NUM_ONCE       64          /* Initial number of once_list[]    */

#define MAX_DEF   256
#define MAX_UNDEF (MAX_DEF/4)

/* Values of mkdep. */
#define MD_MKDEP        1   /* Output source file dependency line   */
#define MD_SYSHEADER    2   /* Print also system-header names       */
#define MD_FILE         4   /* Output to the file named *.d         */
#define MD_PHONY        8   /* Print also phony targets for each header */
#define MD_QUOTE        16  /* 'Quote' $ and space in target name   */

#define MAX_ARCH_LEN    16

#if COMPILER == GNUC
    #define N_QUOTE_DIR     8
#endif

#if COMPILER == GNUC || COMPILER == MSC
    /*
    * preinclude points to the file specified by -include (-Fl for MSC) option,
    * which is included prior to the main input file.
    */
    #define         NPREINCLUDE 8
#endif

#if   SYSTEM == SYS_MAC
    #define         MAX_FRAMEWORK   8
#endif

#define NO_DIR  FALSE

typedef struct system_data_ {

    /* for mcpp_getopt()    */
    int      mcpp_optind;
    int      mcpp_opterr;
    int      mcpp_optopt;
    char *   mcpp_optarg;

    int      mb_changed;     /* Flag of -e option        */
    char     cur_work_dir[ PATHMAX + 1];     /* Current working directory*/

    /*
    * incdir[] stores the -I directories (and the system-specific #include <...>
    * directories).  This is set by set_a_dir().  A trailing PATH_DELIM is
    * appended if absent.
    */
    const char **    incdir;         /* Include directories      */
    const char **    incend;         /* -> active end of incdir  */
    int          max_inc;            /* Number of incdir[]       */

    /*
    * fnamelist[] stores the souce file names opened by #include directive for
    * debugging information.
    */
    INC_LIST *   fnamelist;          /* Source file names        */
    INC_LIST *   fname_end;          /* -> active end of fnamelist   */
    int          max_fnamelist;      /* Number of fnamelist[]    */

    /* once_list[] stores the #pragma once file names.  */
    INC_LIST *   once_list;          /* Once opened file         */
    INC_LIST *   once_end;           /* -> active end of once_list   */
    int          max_once;           /* Number of once_list[]    */

    /*
    * 'search_rule' holds searching rule of #include "header.h" to search first
    * before searching user specified or system-specific include directories.
    * 'search_rule' is initialized to SEARCH_INIT.  It can be changed by -I1, -I2
    * or -I3 option.  -I1 specifies CURRENT, -I2 SOURCE and -I3 both.
    */

    int      search_rule;  /* Rule to search include file  */

    int      nflag;          /* Flag of -N (-undef) option       */
    long     std_val;  /* Value of __STDC_VERSION__ or __cplusplus */

    char *   def_list[ MAX_DEF];     /* Macros to be defined     */
    char *   undef_list[ MAX_UNDEF]; /* Macros to be undefined   */
    int      def_cnt;                /* Count of def_list        */
    int      undef_cnt;              /* Count of undef_list      */

    FILE *   mkdep_fp;                       /* For -Mx option   */
    char *   mkdep_target;
    /* For -MT TARGET option and for GCC's queer environment variables.     */
    char *   mkdep_mf;               /* Argument of -MF option   */
    char *   mkdep_md;               /* Argument of -MD option   */
    char *   mkdep_mq;               /* Argument of -MQ option   */
    char *   mkdep_mt;               /* Argument of -MT option   */

    /* sharp_filename is filename for #line line, used only in cur_file()   */
    char *   sharp_filename;
    char *   argv0;      /* argv[ 0] for usage() and version()   */
    int      ansi;           /* __STRICT_ANSI__ flag for GNUC    */ 
    int      compat_mode;

    /* "Compatible" mode of recursive macro expansion   */
    char     arch[ MAX_ARCH_LEN];    /* -arch or -m64, -m32 options      */

    #if COMPILER == GNUC
    /* quote_dir[]:     Include directories for "header" specified by -iquote   */
    /* quote_dir_end:   Active end of quote_dir */
    const char *     quote_dir[ N_QUOTE_DIR];
    const char **    quote_dir_end = quote_dir;
    /* sys_dirp indicates the first directory to search for system headers.     */
    const char **    sys_dirp;        /* System header directory  */
    const char *     sysroot; /* Logical root directory of header */
    int      i_split;                /* For -I- option   */
    int      gcc_work_dir;           /* For -fworking-directory  */
    int      gcc_maj_ver;                    /* __GNUC__         */
    int      gcc_min_ver;                    /* __GNUC_MINOR__   */
    int      dDflag;         /* Flag of -dD option       */
    int      dMflag;         /* Flag of -dM option       */
    #endif

    #if COMPILER == GNUC || COMPILER == MSC
    /*
    * preinclude points to the file specified by -include (-Fl for MSC) option,
    * which is included prior to the main input file.
    */
    char *   preinclude[ NPREINCLUDE];       /* File to pre-include      */
    char **  preinc_end = preinclude;    /* -> active end of preinclude  */
    #endif

    #if COMPILER == MSC
    int      wchar_t_modified;   /* -Zc:wchar_t flag     */
    #endif

    #if COMPILER == LCC
    const char *     optim_name;
    #endif

    #if SYSTEM == SYS_CYGWIN
    int      no_cygwin;          /* -mno-cygwin          */

    #elif   SYSTEM == SYS_MAC
    char *   framework[ MAX_FRAMEWORK];  /* Framework directories*/
    int      num_framework;          /* Current number of framework[]    */
    int      sys_framework;          /* System framework dir     */
    const char **    to_search_framework;
                            /* Search framework[] next to the directory */
    int      in_import;          /* #import rather than #include */
    #endif

    #if NO_DIR
    /* Unofficial feature to strip directory part of include file   */
    int      no_dir;
    #endif

    int  diagnosed;

    char *   putdep_output;                 /* File names           */
    size_t * putdep_pos;                    /* Offset to filenames  */
    int      putdep_pos_num;                /* Index of pos[]       */
    char *   putdep_out_p;                  /* Pointer to output[]  */
    size_t   putdep_mkdep_len;              /* Size of output[]     */
    size_t   putdep_pos_max;                /* Size of pos[]        */
    FILE *   putdep_fp;         /* Path to output dependency line   */
    size_t   putdep_llen;       /* Length of current physical output line   */

    int max_open;
    
    FILEINFO *   sh_file;
    int  sh_line;

    int getopt_sp;

} system_data_t;

typedef struct processing_data_ {
    option_flags_t option_flags;
    std_limits_t std_limits;

    int      mcpp_mode;                         /* Mode of preprocessing        */
    int      stdc_val;                          /* Value of __STDC__            */
    long     stdc_ver;                          /* Value of __STDC_VERSION__    */
    long     cplus_val;                         /* Value of __cplusplus for C++ */
    int      stdc2;                             /* cplus_val or (stdc_ver >= 199901L)   */
    int      stdc3;                             /* (stdc_ver or cplus_val) >= 199901L   */
    int      standard;                          /* mcpp_mode is STD or POST_STD */
    int      std_line_prefix;                   /* #line in C source style      */
    int      warn_level;                        /* Level of warning             */
    int      errors;                            /* Error counter                */
    long     src_line;                          /* Current source line number   */
    int      wrong_line;                        /* Force #line to compiler      */
    int      newlines;                          /* Count of blank lines         */
    int      keep_comments;                     /* Don't remove comments        */
    int      keep_spaces;                       /* Don't remove white spaces    */
    int      include_nest;                      /* Nesting level of #include    */
    const char *     null;                      /* "" string for convenience    */
    const char **    inc_dirp;                  /* Directory of #includer       */
    const char *     cur_fname;                 /* Current source file name     */
    int      no_output;                         /* Don't output included file   */
    int      in_directive;                      /* In process of #directive     */
    int      in_define;                         /* In #define line              */
    int      in_getarg;                         /* Collecting arguments of macro*/
    int      in_include;                        /* In #include line             */
    int      in_if;                             /* In #if and non-skipped expr. */
    long     macro_line;                        /* Line number of macro call    */
    char *   macro_name;                        /* Currently expanding macro    */
    int      openum;                            /* Number of operator or punct. */
    IFINFO *     ifptr;                         /* -> current ifstack item      */
    FILEINFO *   infile;                        /* Current input file or macro  */
    MFILE*   mf_in;
    FILE *   fp_out;                            /* Output stream preprocessed   */
    FILE *   fp_err;                            /* Diagnostics stream           */
    FILE *   fp_debug;                          /* Debugging information stream */
    int      insert_sep;                        /* Inserted token separator flag*/
    int      mkdep;                             /* Output source file dependency*/
    int      mbchar;                            /* Encoding of multi-byte char  */
    int      mbchk;                             /* Possible multi-byte char     */
    int      bsl_in_mbchar;                     /* 2nd byte of mbchar has '\\'  */
    int      bsl_need_escape;                   /* '\\' in mbchar should be escaped */
    int      mcpp_debug;                        /* Class of debug information   */
    long     in_asm;                            /* In #asm - #endasm block      */
    jmp_buf  error_exit;                        /* Exit on fatal error          */
    char *   cur_fullname;                      /* Full name of current source  */
    short *  char_type;                         /* Character classifier         */
    char *   workp;                             /* Free space in work[]         */
    char *     work_end;                        /* End of work[] buffer         */
    char     identifier[IDMAX + IDMAX / 8];     /* Lastly scanned name          */
    IFINFO   ifstack[BLK_NEST + 1];             /* Information of #if nesting   */
    char     work_buf[NWORK + IDMAX];           /* Temporary buffer for directive line and macro expansion  */
    int      src_col;

    /*
    * output[] and out_ptr are used for:
    *      buffer to store preprocessed line (this line is put out or handed to
    *      post_preproc() via putout() in some cases)
    */
    char output[NMACWORK]; /* Buffer for preprocessed line */
    char * out_end;

    /* Limit of output line for other than GCC and VC   */
    char * out_wend;

    /* Buffer end of output line    */
    char *out_ptr; /* Current pointer into output[]*/

    /* Symbol table queue headers.  */
    DEFBUF *symtab[SBSIZE];
    long num_of_macro;

    VAL_SIGN ev;    /* Current value and signedness     */
    int skip;       /* 3-way signal of skipping expr*/

    int mbstart;
    int mb2;

    /* Function pointer to expand_macro() functions.    */
    char *(*expand_macro)(DEFBUF *defp, char *out, char *out_end, LINE_COL line_col, int *pragma_op, processing_data_t* processingData);
    /* Function pointer to mb_read_*() functions.   */
    size_t (*mb_read)(int c1, char **in_pp, char **out_pp, processing_data_t* processingData);

    /* Support for alternate output mechanisms (e.g. memory buffers) */
    int (* mcpp_fputc)( int c, OUTDEST od, processing_data_t* processingData);
    int (* mcpp_fputs)( const char * s, OUTDEST od, processing_data_t* processingData);
    int (* mcpp_fprintf)( OUTDEST od, processing_data_t* processingData, const char * format, ...);

    params_data_t parametersProcessingData;
    macros_data_t macrosProcessingData;
    support_data_t supportProcessingData;
    system_data_t systemData;

    file_loader* fileLoader;

} processing_data_t;

/* main.c   */

/* Undefine predefined macros */
extern void un_predefine( int clearall, processing_data_t* data);

/* Sets up the processing data */
extern void setup_processing_data(processing_data_t* data);

/* directive.c  */
extern void     directive(processing_data_t* data);
                /* Process #directive line      */
extern DEFBUF * do_define( int ignore_redef, int predefine, processing_data_t* data);
                /* Do #define directive         */
extern DEFBUF * look_id( const char * name, processing_data_t* data);
                /* Look for a #define'd thing   */
extern DEFBUF **    look_prev( const char * name, int * cmp, processing_data_t* data);
                /* Look for place to insert def.*/
extern DEFBUF * look_and_install( const char * name, int numargs
        , const char * parmnames, const char * repl, processing_data_t* data);
                /* Look and insert macro def.   */
extern DEFBUF * install_macro( const char * name, int numargs
        , const char * parmnames, const char * repl, DEFBUF ** prevp, int cmp
        , int predefine, processing_data_t* data);
                /* Install a def to symbol table*/
extern int      undefine( const char * name, processing_data_t* data);
                /* Delete from symbol table     */
extern void     dump_a_def( const char * why, const DEFBUF * dp, int newdef
        , int comment, FILE * fp, processing_data_t* data);
                /* Dump a specific macro def    */
extern void     dump_def( int comment, int K_opt, processing_data_t* data);
                /* Dump current macro defs      */

/* eval.c   */
extern expr_t   eval_if(processing_data_t* data);
                /* Evaluate #if expression      */
extern VAL_SIGN *   eval_num( const char * nump, processing_data_t* data);
                /* Evaluate preprocessing number*/

/* expand.c */
                /* Expand a macro completely    */
extern void     expand_init( int compat, int strict_ansi, processing_data_t* data);
                /* Initialize expand_macro()    */
extern DEFBUF * is_macro( char ** cp, processing_data_t* data);
                /* The sequence is a macro call?*/

/* mbchar.c     */
extern const char *     set_encoding( char * name, char * env, int pragma, processing_data_t* data);
                /* Multi-byte char encoding     */
extern void     mb_init(processing_data_t* data);
                /* Initialize mbchar variables  */
extern uexpr_t  mb_eval( char ** seq_pp, processing_data_t* data);
                /* Evaluate mbchar in #if       */
extern int      last_is_mbchar( const char * in, int len, processing_data_t* data);
                /* The line ends with MBCHAR ?  */

/* support.c    */
extern void     mcpp_init_def_out_func(processing_data_t* data);
extern int      get_unexpandable( int c, int diag, processing_data_t* data);
                /* Get next unexpandable token  */
extern void     skip_nl(processing_data_t* data);
                /* Skip to the end of the line  */
extern int      skip_ws(processing_data_t* data);
                /* Skip over white-spaces       */
extern int      scan_token( int c, char ** out_pp, char * out_end, processing_data_t* data);
                /* Get the next token           */
extern char *   scan_quote( int delim, char * out, char * out_end, int diag, processing_data_t* data);
                /* Scan a quoted literal        */
extern int      id_operator( const char * name);
                /* Check identifier-like ops    */
extern void     expanding( const char * name, int to_be_freed, processing_data_t* data);
                /* Save macro name expanding    */
extern void     clear_exp_mac(processing_data_t* data);
                /* Clear expanding macro infs   */
extern int      get_ch(processing_data_t* data);
                /* Get the next char from input */
extern int      cnv_trigraph( char * in, processing_data_t* data);
                /* Do trigraph replacement      */
extern int      cnv_digraph( char * in, processing_data_t* data);
                /* Convert digraphs to usual tok*/
extern void     unget_ch(processing_data_t* data);
                /* Push back the char to input  */
extern FILEINFO *   unget_string( const char * text, const char * name, processing_data_t* data); /* Push back the string to input*/
extern char *   save_string( const char * text); /* Stuff string in malloc mem.  */
extern FILEINFO *   get_file( const char * name, const char * src_dir, const char * fullname, size_t bufsize, int include_opt, processing_data_t* data);
                /* New FILEINFO initialization  */
extern char *   (xmalloc)( size_t size); /* Get memory or die            */
extern char *   (xrealloc)( char * ptr, size_t size); /* Reallocate memory or die     */
extern LINE_COL *   get_src_location( LINE_COL * p_line_col, processing_data_t* data); /* Get location on source file  */
extern void     cfatal( const char * format, const char * arg1, long arg2, const char * arg3, processing_data_t* data); /* Print a fatal error and exit */
extern void     cerror( const char * format, const char * arg1, long arg2, const char * arg3, processing_data_t* data); /* Print an error message       */
extern void     cwarn( const char * format, const char * arg1, long arg2, const char * arg3, processing_data_t* data); /* Print a warning message      */
extern void     dump_string( const char * why, const char * text, processing_data_t* data); /* Dump text readably           */
extern void     dump_unget( const char * why, processing_data_t* data);/* Dump all ungotten junk       */

// Anima ADD
/* mfile support, implemented in system.c */
extern MFILE* mfopen(const char* filename, processing_data_t* data);
extern void mfclose(MFILE* mf);
extern void mfseek(MFILE* mf, int pos);
extern char* mfgets(char* str, int size, MFILE* mf);
extern int mferror(MFILE* mf);
extern int mftell(MFILE* mf);
extern void mfset(file_loader* in_file_loader, processing_data_t* data);
extern int mfexists(const char* filename, processing_data_t* data);
// Anima ADD

/* system.c */
extern void     do_options( int argc, char ** argv, char ** in_pp, char ** out_pp, processing_data_t* data);
                /* Process command line args    */
extern void     init_sys_macro(processing_data_t* data);
                /* Define system-specific macro */
extern void     at_start(processing_data_t* data);
                /* Commands prior to main input */
extern void     put_depend( const char * filename, processing_data_t* data);
                /* Output source dependency line*/
extern int      do_include( int next, processing_data_t* data);
                /* Process #include directive   */
extern void     add_file( MFILE * mf, const char * src_dir							// Anima ADD
        , const char * filename, const char * fullname, int include_opt, processing_data_t* data);
                /* Chain the included file      */
extern void     sharp( FILEINFO * sharp_file, int marker, processing_data_t* data);
                /* Output # line number         */
extern void     do_pragma(processing_data_t* data);
                /* Process #pragma directive    */
extern void     put_asm(void);
                /* Putout an asm code line      */
extern void     do_old(processing_data_t* data);
                /* Process older directives     */
extern void     at_end(void);
                /* Do the final commands        */
extern void     print_heap(void);
                /* Print blocks of heap memory  */
#if ! HOST_HAVE_STPCPY
extern char *   stpcpy( char * dest, const char * src);
                /* Non-Standard library function*/
#endif

#if MCPP_LIB    /* Setting to use mcpp as a subroutine  */
/* directive.c  */
extern void     clear_symtable(processing_data_t* data);
                /* Free all macro definitions   */
/* system.c     */
extern void     clear_filelist(processing_data_t* data);
                /* Free filename and directory list     */
/* The following 5 functions are to Initialize static variables.    */
/* directive.c  */
extern void     init_directive(processing_data_t* data);
/* eval.c   */
extern void     init_eval( processing_data_t* data);
/* support.c    */
extern void     init_support( processing_data_t* data);
/* system.c */
extern void     init_system( processing_data_t* data);

#if HOST_COMPILER == GNUC && (SYS_FAMILY == SYS_UNIX && SYSTEM != SYS_CYGWIN)
#pragma GCC visibility pop
#endif
#endif

#if HOST_HAVE_STPCPY
extern char *   stpcpy( char * dest, const char * src);
#endif

#if MCPP_LIB
#include "mcpp_lib.h"   /* External interface when used as library  */
#endif