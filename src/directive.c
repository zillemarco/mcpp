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
 *                          D I R E C T I V E . C
 *              P r o c e s s   D i r e c t i v e  L i n e s
 *
 * The routines to handle directives other than #include and #pragma
 * are placed here.
 */

#if PREPROCESSED
#include "mcpp.H"
#else
#include "system.H"
#include "internal.H"
#endif

static int do_if(int hash, const char *directive_name, processing_data_t* processingData);
/* #if, #elif, #ifdef, #ifndef      */
static void sync_linenum(processing_data_t* processingData);
/* Synchronize number of newlines   */
static long do_line(processing_data_t* processingData);
/* Process #line directive          */
static int get_parm(processing_data_t* processingData);
/* Get parameters of macro, its nargs, names, lengths       */
static int get_repl(const char *macroname, processing_data_t* processingData);
/* Get replacement text embedding parameter number  */
static char *is_formal(const char *name, int conv, processing_data_t* processingData);
/* If formal parameter, save the number     */
static char *def_stringization(char *repl_cur, processing_data_t* processingData);
/* Define stringization     */
static char *mgtoken_save(const char *macroname, processing_data_t* processingData);
/* Prefix DEF_MAGIC to macro name in repl-text      */
static char *str_parm_scan(char *string_end, processing_data_t* processingData);
/* Scan the parameter in quote      */
static void do_undef(processing_data_t* processingData);
/* Process #undef directive         */
static void dump_repl(const DEFBUF *dp, FILE *fp, int gcc2_va, processing_data_t* processingData);
/* Dump replacement text            */

/*
 * Generate (by hand-inspection) a set of unique values for each directive.
 * MCPP won't compile if there are hash conflicts.
 */
#define L_if ('i' ^ (EOS << 1))
#define L_ifdef ('i' ^ ('d' << 1))
#define L_ifndef ('i' ^ ('n' << 1))
#define L_elif ('e' ^ ('i' << 1))
#define L_else ('e' ^ ('s' << 1))
#define L_endif ('e' ^ ('d' << 1))
#define L_define ('d' ^ ('f' << 1))
#define L_undef ('u' ^ ('d' << 1))
#define L_line ('l' ^ ('n' << 1))
#define L_include ('i' ^ ('c' << 1))
#if COMPILER == GNUC
#define L_include_next ('i' ^ ('c' << 1) ^ ('_' << 1))
#endif
#if SYSTEM == SYS_MAC
#define L_import ('i' ^ ('p' << 1))
#endif
#define L_error ('e' ^ ('r' << 1))
#define L_pragma ('p' ^ ('a' << 1))

static const char *const not_ident = "Not an identifier \"%s\"";     /* _E_      */
static const char *const no_arg = "No argument";                     /* _E_      */
static const char *const excess = "Excessive token sequence \"%s\""; /* _E_ _W1_ */

void directive(processing_data_t* processingData)
/*
 * Process #directive lines.  Each directive have their own subroutines.
 */
{
    const char *const many_nesting =
        "More than %.0s%ld nesting of #if (#ifdef) sections%s";                          /* _F_ _W4_ _W8_    */
    const char *const not_in_section = "Not in a #if (#ifdef) section in a source file"; /* _E_ _W1_ */
    const char *const illeg_dir = "Illegal #directive \"%s%.0ld%s\"";                    /* _E_ _W1_ _W8_    */
    const char *const in_skipped = " (in skipped block)";                                /* _W8_ */
    FILEINFO *file;
    int token_type;
    int hash;
    int c;
    char *tp;

    processingData->in_directive = TRUE;
    if (processingData->keep_comments)
    {
        processingData->mcpp_fputc('\n', OUT, processingData); /* Possibly flush out comments  */
        processingData->newlines--;
    }
    c = skip_ws(processingData);
    if (c == '\n') /* 'null' directive */
        goto ret;
    token_type = scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData);
    if (processingData->in_asm && (token_type != NAM || (!str_eq(processingData->identifier, "asm") && !str_eq(processingData->identifier, "endasm"))))
        /* In #asm block, ignore #anything other than #asm or #endasm       */
        goto skip_line;
    if (token_type != NAM)
    {
        if (processingData->mcpp_mode == OLD_PREP && token_type == NUM)
        { /* # 123 [fname]*/
            strcpy(processingData->identifier, "line");
        }
        else
        {
            if (processingData->compiling)
            {
                if (processingData->option_flags.lang_asm)
                {
                    if (processingData->warn_level & 1)
                        cwarn(illeg_dir, processingData->work_buf, 0L, NULL, processingData);
                }
                else
                {
                    cerror(illeg_dir, processingData->work_buf, 0L, NULL, processingData);
                }
            }
            else if (processingData->warn_level & 8)
            {
                cwarn(illeg_dir, processingData->work_buf, 0L, in_skipped, processingData);
            }
            goto skip_line;
        }
    }
    
    hash = (processingData->identifier[1] == EOS) ? processingData->identifier[0] : (processingData->identifier[0] ^ (processingData->identifier[2] << 1));
    if (strlen(processingData->identifier) > 7)
        hash ^= (processingData->identifier[7] << 1);

    /* hash is set to a unique value corresponding to the directive.*/
    switch (hash)
    {
    case L_if:
        tp = "if";
        break;
    case L_ifdef:
        tp = "ifdef";
        break;
    case L_ifndef:
        tp = "ifndef";
        break;
    case L_elif:
        tp = "elif";
        break;
    case L_else:
        tp = "else";
        break;
    case L_endif:
        tp = "endif";
        break;
    case L_define:
        tp = "define";
        break;
    case L_undef:
        tp = "undef";
        break;
    case L_line:
        tp = "line";
        break;
    case L_include:
        tp = "include";
        break;
#if COMPILER == GNUC
    case L_include_next:
        tp = "include_next";
        break;
#endif
#if SYSTEM == SYS_MAC
    case L_import:
        tp = "import";
        break;
#endif
    case L_error:
        tp = "error";
        break;
    case L_pragma:
        tp = "pragma";
        break;
    default:
        tp = NULL;
        break;
    }

    if (tp != NULL && !str_eq(processingData->identifier, tp))
    {              /* Hash conflict*/
        hash = 0;  /* Unknown directive, will  */
        tp = NULL; /*   be handled by do_old() */
    }

    if (!processingData->compiling)
    { /* Not compiling now    */
        switch (hash)
        {
        case L_elif:
            if (!processingData->standard)
            {
                if (processingData->warn_level & 8)
                    do_old(processingData);   /* Unknown directive    */
                goto skip_line; /* Skip the line        */
            }                   /* Else fall through    */
        case L_else:            /* Test the #if's nest, if 0, compile   */
        case L_endif:           /* Un-nest #if          */
            break;
        case L_if:     /* These can't turn     */
        case L_ifdef:  /*  compilation on, but */
        case L_ifndef: /*   we must nest #if's.*/
            if (&processingData->ifstack[BLK_NEST] < ++processingData->ifptr)
                goto if_nest_err;
            if (processingData->standard && (processingData->warn_level & 8) && &processingData->ifstack[processingData->std_limits.blk_nest + 1] == processingData->ifptr)
                cwarn(many_nesting, NULL, (long)processingData->std_limits.blk_nest, in_skipped, processingData);
            processingData->ifptr->stat = 0;          /* !WAS_COMPILING       */
            processingData->ifptr->ifline = processingData->src_line; /* Line at section start*/
            goto skip_line;
        default: /* Other directives     */
            if (tp == NULL && (processingData->warn_level & 8))
                do_old(processingData);   /* Unknown directive ?  */
            goto skip_line; /* Skip the line        */
        }
    }

    processingData->macro_line = 0; /* Reset error flag     */
    file = processingData->infile;  /* Remember the current file    */

    switch (hash)
    {

    case L_if:
    case L_ifdef:
    case L_ifndef:
        if (&processingData->ifstack[BLK_NEST] < ++processingData->ifptr)
            goto if_nest_err;
        if (processingData->standard && (processingData->warn_level & 4) &&
            &processingData->ifstack[processingData->std_limits.blk_nest + 1] == processingData->ifptr)
            cwarn(many_nesting, NULL, (long)processingData->std_limits.blk_nest, NULL, processingData);
        processingData->ifptr->stat = WAS_COMPILING;
        processingData->ifptr->ifline = processingData->src_line;
        goto ifdo;

    case L_elif:
        if (!processingData->standard)
        {
            do_old(processingData); /* Unrecognized directive       */
            break;
        }
        if (processingData->ifptr == &processingData->ifstack[0])
            goto nest_err;
        if (processingData->ifptr == processingData->infile->initif)
        {
            goto in_file_nest_err;
        }
        if (processingData->ifptr->stat & ELSE_SEEN)
            goto else_seen_err;
        if ((processingData->ifptr->stat & (WAS_COMPILING | TRUE_SEEN)) != WAS_COMPILING)
        {
            processingData->compiling = FALSE; /* Done compiling stuff */
            goto skip_line;    /* Skip this group      */
        }
        hash = L_if;
    ifdo:
        c = do_if(hash, tp, processingData);
        if (processingData->mcpp_debug & IF)
        {
            processingData->mcpp_fprintf(DBG, processingData, "#if (#elif, #ifdef, #ifndef) evaluate to %s.\n", processingData->compiling ? "TRUE" : "FALSE");
            processingData->mcpp_fprintf(DBG, processingData, "line %ld: %s", processingData->src_line, processingData->infile->buffer);
        }
        
        if (c == FALSE)
        {                      /* Error                */
            processingData->compiling = FALSE; /* Skip this group      */
            goto skip_line;    /* Prevent an extra error message   */
        }
        break;

    case L_else:
        if (processingData->ifptr == &processingData->ifstack[0])
            goto nest_err;
        if (processingData->ifptr == processingData->infile->initif)
        {
            if (processingData->standard)
                goto in_file_nest_err;
            else if (processingData->warn_level & 1)
                cwarn(not_in_section, NULL, 0L, NULL, processingData);
        }
        
        if (processingData->ifptr->stat & ELSE_SEEN)
            goto else_seen_err;
        
        processingData->ifptr->stat |= ELSE_SEEN;
        processingData->ifptr->elseline = processingData->src_line;

        if (processingData->ifptr->stat & WAS_COMPILING)
        {
            if (processingData->compiling || (processingData->ifptr->stat & TRUE_SEEN) != 0)
                processingData->compiling = FALSE;
            else
                processingData->compiling = TRUE;
        }
        
        if ((processingData->mcpp_debug & MACRO_CALL) && (processingData->ifptr->stat & WAS_COMPILING))
        {
            sync_linenum(processingData);
            processingData->mcpp_fprintf(OUT, processingData, "/*else %ld:%c*/\n", processingData->src_line, processingData->compiling ? 'T' : 'F'); /* Show that #else is seen  */
        }
        break;

    case L_endif:
        if (processingData->ifptr == &processingData->ifstack[0])
            goto nest_err;
        if (processingData->ifptr <= processingData->infile->initif)
        {
            if (processingData->standard)
                goto in_file_nest_err;
            else if (processingData->warn_level & 1)
                cwarn(not_in_section, NULL, 0L, NULL, processingData);
        }
        if (!processingData->compiling && (processingData->ifptr->stat & WAS_COMPILING))
            processingData->wrong_line = TRUE;
        processingData->compiling = (processingData->ifptr->stat & WAS_COMPILING);
        if ((processingData->mcpp_debug & MACRO_CALL) && processingData->compiling)
        {
            sync_linenum(processingData);
            processingData->mcpp_fprintf(OUT, processingData, "/*endif %ld*/\n", processingData->src_line);
            /* Show that #if block has ended    */
        }
        --processingData->ifptr;
        break;

    case L_define:
        do_define(FALSE, 0, processingData);
        break;

    case L_undef:
        do_undef(processingData);
        break;

    case L_line:
        if ((c = do_line(processingData)) > 0)
        {
            processingData->src_line = c;
            sharp(NULL, 0, processingData);            /* Putout the new line number and file name */
            processingData->infile->line = --processingData->src_line; /* Next line number is 'src_line'   */
            processingData->newlines = -1;
        }
        else
        { /* Error already diagnosed by do_line() */
            skip_nl(processingData);
        }
        break;

    case L_include:
        processingData->in_include = TRUE;
        if (do_include(FALSE, processingData) == TRUE && file != processingData->infile)
            processingData->newlines = -1; /* File has been included. Clear blank lines    */
        processingData->in_include = FALSE;
        break;

    case L_error:
        if (!processingData->standard)
        {
            do_old(processingData); /* Unrecognized directive       */
            break;
        }
        cerror(processingData->infile->buffer, NULL, 0L, NULL, processingData); /* _E_  */
        break;

    case L_pragma:
        if (!processingData->standard)
        {
            do_old(processingData); /* Unrecognized directive       */
            break;
        }
        do_pragma(processingData);
        processingData->newlines = -1; /* Do not putout excessive '\n' */
        break;

    default: /* Non-Standard or unknown directives   */
        do_old(processingData);
        break;
    }

    switch (hash)
    {
    case L_if:
    case L_elif:
    case L_define:
    case L_line:
        goto skip_line; /* To prevent duplicate error message   */
#if COMPILER == GNUC
    case L_include_next:
        if (file != infile) /* File has been included   */
            newlines = -1;
#endif
#if SYSTEM == SYS_MAC
    case L_import:
        if (file != infile) /* File has been included   */
            newlines = -1;
#endif
    case L_error:
        if (processingData->standard)
            goto skip_line;
        /* Else fall through    */
    case L_include:
    case L_pragma:
        if (processingData->standard)
            break; /* Already read over the line           */
        /* Else fall through    */
    default: /* L_else, L_endif, L_undef, etc.       */
        if (processingData->mcpp_mode == OLD_PREP)
        {
            /*
         * Ignore the rest of the #directive line so you can write
         *          #if     foo
         *          #endif  foo
         */
            ;
        }
        else if (skip_ws(processingData) != '\n')
        {
#if COMPILER == GNUC
            if (standard && hash != L_endif)
#else
            if (processingData->standard)
#endif
                cerror(excess, processingData->infile->bptr - 1, 0L, NULL, processingData);
            else if (processingData->warn_level & 1)
                cwarn(excess, processingData->infile->bptr - 1, 0L, NULL, processingData);
        }
        skip_nl(processingData);
    }
    goto ret;

in_file_nest_err:
    cerror(not_in_section, NULL, 0L, NULL, processingData);
    goto skip_line;
nest_err:
    cerror("Not in a #if (#ifdef) section", NULL, 0L, NULL, processingData); /* _E_  */
    goto skip_line;
else_seen_err:
    cerror("Already seen #else at line %.0s%ld" /* _E_  */
           ,
           NULL, processingData->ifptr->elseline, NULL, processingData);
skip_line:
    skip_nl(processingData); /* Ignore rest of line  */
    goto ret;

if_nest_err:
    cfatal(many_nesting, NULL, (long)BLK_NEST, NULL, processingData);

ret:
    processingData->in_directive = FALSE;
    processingData->keep_comments = processingData->option_flags.c && processingData->compiling && !processingData->no_output;
    processingData->keep_spaces = processingData->option_flags.k && processingData->compiling;
    /* keep_spaces is on for #define line even if no_output is TRUE  */
    if (!processingData->wrong_line)
        processingData->newlines++;
}

static int do_if(int hash, const char *directive_name, processing_data_t* processingData)
/*
 * Process an #if (#elif), #ifdef or #ifndef.  The latter two are straight-
 * forward, while #if needs a subroutine to evaluate the expression.
 * do_if() is called only if compiling is TRUE.  If false, compilation is
 * always supressed, so we don't need to evaluate anything.  This supresses
 * unnecessary warnings.
 */
{
    int c;
    int found;
    DEFBUF *defp;

    if ((c = skip_ws(processingData)) == '\n')
    {
        unget_ch(processingData);
        cerror(no_arg, NULL, 0L, NULL, processingData);
        return FALSE;
    }
    if (processingData->mcpp_debug & MACRO_CALL)
    {
        sync_linenum(processingData);
        processingData->mcpp_fprintf(OUT, processingData, "/*%s %ld*/", directive_name, processingData->src_line);
    }
    if (hash == L_if)
    { /* #if or #elif             */
        unget_ch(processingData);
        found = (eval_if(processingData) != 0L); /* Evaluate expression      */
        if (processingData->mcpp_debug & MACRO_CALL)
            processingData->in_if = FALSE; /* 'in_if' is dynamically set in eval_lex() */
        hash = L_ifdef;    /* #if is now like #ifdef   */
    }
    else
    { /* #ifdef or #ifndef        */
        if (scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData) != NAM)
        {
            cerror(not_ident, processingData->work_buf, 0L, NULL, processingData);
            return FALSE; /* Next token is not an identifier  */
        }
        found = ((defp = look_id(processingData->identifier, processingData)) != NULL); /* Look in table*/
        if (processingData->mcpp_debug & MACRO_CALL)
        {
            if (found)
                processingData->mcpp_fprintf(OUT, processingData, "/*%s*/", defp->name);
        }
    }
    if (found == (hash == L_ifdef))
    {
        processingData->compiling = TRUE;
        processingData->ifptr->stat |= TRUE_SEEN;
    }
    else
    {
        processingData->compiling = FALSE;
    }
    if (processingData->mcpp_debug & MACRO_CALL)
    {
        processingData->mcpp_fprintf(OUT, processingData, "/*i %c*/\n", processingData->compiling ? 'T' : 'F');
        /* Report wheather the directive is evaluated TRUE or FALSE */
    }
    return TRUE;
}

static void sync_linenum(processing_data_t* processingData)
/*
 * Put out newlines or #line line to synchronize line number with the
 * annotations about #if, #elif, #ifdef, #ifndef, #else or #endif on -K option.
 */
{
    if (processingData->wrong_line || processingData->newlines > 10)
    {
        sharp(NULL, 0, processingData);
    }
    else
    {
        while (processingData->newlines-- > 0)
            processingData->mcpp_fputc('\n', OUT, processingData);
    }
    processingData->newlines = -1;
}

static long do_line(processing_data_t* processingData)
/*
 * Parse the line to update the line number and "filename" field for the next
 * input line.
 * Values returned are as follows:
 *  -1:     syntax error or out-of-range error (diagnosed by do_line(),
 *          eval_num()).
 *  [1,32767]:  legal line number for C90, [1,2147483647] for C99.
 * Line number [32768,2147483647] in C90 mode is only warned (not an error).
 * do_line() always absorbs the line (except the <newline>).
 */
{
    const char *const not_digits = "Line number \"%s\" isn't a decimal digits sequence"; /* _E_ _W1_ */
    const char *const out_of_range = "Line number \"%s\" is out of range of [1,%ld]";    /* _E_ _W1_ */
    int token_type;
    VAL_SIGN *valp;
    char *save;
    int c;

    if ((c = skip_ws(processingData)) == '\n')
    {
        cerror(no_arg, NULL, 0L, NULL, processingData);
        unget_ch(processingData); /* Push back <newline>  */
        return -1L; /* Line number is not changed   */
    }

    if (processingData->standard)
    {
        token_type = get_unexpandable(c, FALSE, processingData);
        if (processingData->macro_line == MACRO_ERROR) /* Unterminated macro   */
            return -1L;                /*   already diagnosed. */
        if (token_type == NO_TOKEN)    /* Macro expanded to 0 token    */
            goto no_num;
        if (token_type != NUM)
            goto illeg_num;
    }
    else if (scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData) != NUM)
    {
        goto illeg_num;
    }
    for (processingData->workp = processingData->work_buf; *processingData->workp != EOS; processingData->workp++)
    {
        if (!isdigit(*processingData->workp & UCHARMAX))
        {
            if (processingData->standard)
            {
                cerror(not_digits, processingData->work_buf, 0L, NULL, processingData);
                return -1L;
            }
            else if (processingData->warn_level & 1)
            {
                cwarn(not_digits, processingData->work_buf, 0L, NULL, processingData);
            }
        }
    }
    valp = eval_num(processingData->work_buf, processingData); /* Evaluate number      */
    if (valp->sign == VAL_ERROR)
    { /* Error diagnosed by eval_num()*/
        return -1;
    }
    else if (processingData->standard && (processingData->std_limits.line_num < valp->val || valp->val <= 0L))
    {
        if (valp->val < LINE99LIMIT && valp->val > 0L)
        {
            if (processingData->warn_level & 1)
                cwarn(out_of_range, processingData->work_buf, processingData->std_limits.line_num, NULL, processingData);
        }
        else
        {
            cerror(out_of_range, processingData->work_buf, processingData->std_limits.line_num, NULL, processingData);
            return -1L;
        }
    }

    if (processingData->standard)
    {
        token_type = get_unexpandable(skip_ws(processingData), FALSE, processingData);
        if (processingData->macro_line == MACRO_ERROR)
            return -1L;
        if (token_type != STR)
        {
            if (token_type == NO_TOKEN)
            { /* Filename is absent   */
                return (long)valp->val;
            }
            else
            { /* Expanded macro should be a quoted string */
                goto not_fname;
            }
        }
    }
    else
    {
        if ((c = skip_ws(processingData)) == '\n')
        {
            unget_ch(processingData);
            return (long)valp->val;
        }
        if (scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData) != STR)
            goto not_fname;
    }
#if COMPILER == GNUC
    if (memcmp(workp - 3, "//", 2) == 0)
    {                            /* "/cur-dir//"         */
        save = infile->filename; /* Do not change the file name  */
    }
    else
#endif
    {
        *(processingData->workp - 1) = EOS;               /* Ignore right '"'     */
        save = save_string(&processingData->work_buf[1]); /* Ignore left '"'      */
    }

    if (processingData->standard)
    {
        if (get_unexpandable(skip_ws(processingData), FALSE, processingData) != NO_TOKEN)
        {
            cerror(excess, processingData->work_buf, 0L, NULL, processingData);
            free(save);
            return -1L;
        }
    }
    else if (processingData->mcpp_mode == OLD_PREP)
    {
        skip_nl(processingData);
        unget_ch(processingData);
    }
    else if ((c = skip_ws(processingData)) == '\n')
    {
        unget_ch(processingData);
    }
    else
    {
        if (processingData->warn_level & 1)
        {
            scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData);
            cwarn(excess, processingData->work_buf, 0, NULL, processingData);
        }
        skip_nl(processingData);
        unget_ch(processingData);
    }

    if (processingData->infile->filename)
        free(processingData->infile->filename);

    processingData->infile->filename = save; /* New file name        */
                             /* Note that this does not change infile->real_fname    */
    return (long)valp->val;  /* New line number      */

no_num:
    cerror("No line number", NULL, 0L, NULL, processingData); /* _E_  */
    return -1L;
illeg_num:
    cerror("Not a line number \"%s\"", processingData->work_buf, 0L, NULL, processingData); /* _E_  */
    return -1L;
not_fname:
    cerror("Not a file name \"%s\"", processingData->work_buf, 0L, NULL, processingData); /* _E_  */
    return -1L;
}

/*
 *                  M a c r o  D e f i n i t i o n s
 */

const char *const no_ident = "No identifier"; /* _E_  */

/*
 * look_id()    Looks for the name in the defined symbol table.  Returns a
 *              pointer to the definition if found, or NULL if not present.
 * install_macro()  Installs the definition.  Updates the symbol table.
 * undefine()   Deletes the definition from the symbol table.
 */

DEFBUF *do_define(
    int ignore_redef, /* Do not redefine   */
    int predefine,    /* Predefine compiler-specific name */
    /*
     * Note: The value of 'predefine' should be one of 0, DEF_NOARGS_PREDEF
     *      or DEF_NOARGS_PREDEF_OLD, the other values cause errors.
     */
    processing_data_t* processingData
)
/*
 * Called from directive() when a #define is scanned or called from
 *      do_options() when a -D option is scanned.  This module parses formal
 *      parameters by get_parm() and the replacement text by get_repl().
 *
 * There is some special case code to distinguish
 *      #define foo     bar     --  object-like macro
 * from #define foo()   bar     --  function-like macro with no parameter
 *
 * Also, we make sure that
 *      #define foo     foo
 * expands to "foo" but doesn't put MCPP into an infinite loop.
 *
 * A warning is printed if you redefine a symbol with a non-identical
 * text.  I.e,
 *      #define foo     123
 *      #define foo     123
 * is ok, but
 *      #define foo     123
 *      #define foo     +123
 * is not.
 *
 * The following subroutines are called from do_define():
 * get_parm()   parsing and remembering parameter names.
 * get_repl()   parsing and remembering replacement text.
 *
 * The following subroutines are called from get_repl():
 * is_formal()  is called when an identifier is scanned.  It checks through
 *              the array of formal parameters.  If a match is found, the
 *              identifier is replaced by a control byte which will be used
 *              to locate the parameter when the macro is expanded.
 * def_stringization()  is called when '#' operator is scanned.  It surrounds
 *              the token to stringize with magic-codes.
 *
 * modes other than STD ignore difference of parameter names in macro
 * redefinition.
 */
{
    const char *const predef = "\"%s\" shouldn't be redefined"; /* _E_  */
    
    
    // char repl_list[NMACWORK + IDMAX];                           /* Replacement text     */
    // char macroname[IDMAX + 1];                                  /* Name of the macro defining   */
    char* repl_list = xmalloc(NMACWORK + IDMAX);
    char* macroname = xmalloc(IDMAX + 1);

    DEFBUF *defp;                                               /* -> Old definition            */
    DEFBUF **prevp;                                             /* -> Pointer to previous def in list   */
    int c;
    int redefined;             /* TRUE if redefined    */
    int dnargs = 0;            /* defp->nargs          */
    int cmp;                   /* Result of name comparison    */
    size_t def_start, def_end; /* Column of macro definition   */

    processingData->parametersProcessingData.repl_base = repl_list;
    processingData->parametersProcessingData.repl_end = &repl_list[NMACWORK];

    c = skip_ws(processingData);
    if ((processingData->mcpp_debug & MACRO_CALL) && processingData->src_line) /* Start of definition  */
        def_start = processingData->infile->bptr - processingData->infile->buffer - 1;
    
    if (c == '\n')
    {
        cerror(no_ident, NULL, 0L, NULL, processingData);
        unget_ch(processingData);

        free(repl_list);
        free(macroname);
        return NULL;
    }
    else if (scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData) != NAM)
    {
        cerror(not_ident, processingData->work_buf, 0L, NULL, processingData);

        free(repl_list);
        free(macroname);
        return NULL;
    }
    else
    {
        prevp = look_prev(processingData->identifier, &cmp, processingData);
        /* Find place in the macro list to insert the definition    */
        defp = *prevp;
        if (processingData->standard)
        {
            if (cmp || defp->push)
            { /* Not known or 'pushed' macro      */
                if (str_eq(processingData->identifier, "defined") || ((processingData->stdc_val || processingData->cplus_val) && str_eq(processingData->identifier, "__VA_ARGS__")))
                {
                    cerror(
                        "\"%s\" shouldn't be defined", processingData->identifier, 0L, NULL, processingData); /* _E_  */
        
                    free(repl_list);
                    free(macroname);
                    return NULL;
                }
                redefined = FALSE; /* Quite new definition */
            }
            else
            { /* It's known:          */
                if (ignore_redef)
                {
                    free(repl_list);
                    free(macroname);
                    return defp;
                }
                dnargs = (defp->nargs == DEF_NOARGS_STANDARD || defp->nargs == DEF_NOARGS_PREDEF || defp->nargs == DEF_NOARGS_PREDEF_OLD)
                             ? DEF_NOARGS
                             : defp->nargs;
                if (dnargs <= DEF_NOARGS_DYNAMIC /* __FILE__ and such    */
                    || dnargs == DEF_PRAGMA      /* _Pragma() pseudo-macro   */
                )
                {
                    cerror(predef, processingData->identifier, 0L, NULL, processingData);
        
                    free(repl_list);
                    free(macroname);
                    return NULL;
                }
                else
                {
                    redefined = TRUE; /* Remember this fact   */
                }
            }
        }
        else
        {
            if (cmp)
            {
                redefined = FALSE; /* Quite new definition */
            }
            else
            { /* It's known:          */
                if (ignore_redef)
                {
                    free(repl_list);
                    free(macroname);
                    return defp;
                }
                dnargs = (defp->nargs == DEF_NOARGS_STANDARD || defp->nargs == DEF_NOARGS_PREDEF || defp->nargs == DEF_NOARGS_PREDEF_OLD)
                             ? DEF_NOARGS
                             : defp->nargs;
                redefined = TRUE;
            }
        }
    }

    strcpy(macroname, processingData->identifier); /* Remember the name    */

    processingData->in_define = TRUE; /* Recognize '#', '##'  */
    
    if (get_parm(processingData) == FALSE)
    { /* Get parameter list   */
        processingData->in_define = FALSE;
        
        free(repl_list);
        free(macroname);
        return NULL; /* Syntax error         */
    }
    
    if (get_repl(macroname, processingData) == FALSE)
    { /* Get replacement text */
        processingData->in_define = FALSE;
        
        free(repl_list);
        free(macroname);
        return NULL; /* Syntax error         */
    }
    
    if ((processingData->mcpp_debug & MACRO_CALL) && processingData->src_line)
    {
        /* Remember location on source  */
        char *cp;
        cp = processingData->infile->bptr - 1; /* Before '\n'          */
        while (processingData->char_type[*cp & UCHARMAX] & HSP)
            cp--;                      /* Trailing space       */

        cp++;                          /* Just after the last token    */
        def_end = cp - processingData->infile->buffer; /* End of definition    */
    }

    processingData->in_define = FALSE;
    if (redefined)
    {
        if (dnargs != processingData->parametersProcessingData.nargs || !str_eq(defp->repl, repl_list) || (processingData->mcpp_mode == STD && !str_eq(defp->parmnames, processingData->work_buf)))
        { /* Warn if differently redefined    */
            if (processingData->warn_level & 1)
            {
                cwarn(
                    "The macro is redefined", NULL, 0L, NULL, processingData); /* _W1_ */
                if (!processingData->option_flags.no_source_line)
                    dump_a_def("    previously macro", defp, FALSE, TRUE, processingData->fp_err, processingData);
            }
        }
        else
        { /* Identical redefinition   */
        
            free(repl_list);
            free(macroname);
            return defp;
        }
    } /* Else new or re-definition*/
    
    defp = install_macro(macroname, processingData->parametersProcessingData.nargs, processingData->work_buf, repl_list, prevp, cmp, predefine, processingData);
    
    if ((processingData->mcpp_debug & MACRO_CALL) && processingData->src_line)
    {
        /* Get location on source file  */
        LINE_COL s_line_col, e_line_col;
        s_line_col.line = processingData->src_line;
        s_line_col.col = def_start;
        get_src_location(&s_line_col, processingData);
        /* Convert to pre-line-splicing data    */
        e_line_col.line = processingData->src_line;
        e_line_col.col = def_end;
        get_src_location(&e_line_col, processingData);
        /* Putout the macro definition information embedded in comment  */
        processingData->mcpp_fprintf(OUT, processingData, "/*m%s %ld:%d-%ld:%d*/\n", defp->name, s_line_col.line, s_line_col.col, e_line_col.line, e_line_col.col);
        processingData->wrong_line = TRUE; /* Need #line later */
    }

    if (processingData->mcpp_mode == STD && processingData->cplus_val && id_operator(macroname) && (processingData->warn_level & 1))
        /* These are operators, not identifiers, in C++98   */
        cwarn("\"%s\" is defined as macro", macroname /* _W1_ */
              ,
              0L, NULL, processingData);
              
        
    free(repl_list);
    free(macroname);
    return defp;
}

static int get_parm(processing_data_t* processingData)
/*
 *   Get parameters i.e. numbers into nargs, name into work_buf[], name-length
 * into parms[].len.  parms[].name point into work_buf.
 *   Return TRUE if the parameters are legal, else return FALSE.
 *   In STD mode preprocessor must remember the parameter names, only for
 * checking the validity of macro redefinitions.  This is required by the
 * Standard (what an overhead !).
 */
{
    const char *const many_parms = "More than %.0s%ld parameters";          /* _E_ _W4_     */
    const char *const illeg_parm = "Illegal parameter \"%s\"";              /* _E_          */
    const char *const misplaced_ellip = "\"...\" isn't the last parameter"; /* _E_          */
    int token_type;
    int c;

    processingData->parametersProcessingData.parms[0].name = processingData->workp = processingData->work_buf;
    processingData->work_buf[0] = EOS;
#if COMPILER == GNUC
    processingData->parametersProcessingData.gcc2_va_arg = FALSE;
#endif

    /* POST_STD mode    */
    processingData->insert_sep = NO_SEP; /* Clear the inserted token separator   */
    c = get_ch(processingData);

    if (c == '(')
    {              /* With arguments?      */
        processingData->parametersProcessingData.nargs = 0; /* Init parms counter   */
        if (skip_ws(processingData) == ')')
            return TRUE; /* Macro with 0 parm    */
        else
            unget_ch(processingData);

        do
        { /* Collect parameters   */
            if (processingData->parametersProcessingData.nargs >= NMACPARS)
            {
                cerror(many_parms, NULL, (long)NMACPARS, NULL, processingData);
                return FALSE;
            }
            processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name = processingData->workp; /* Save its start       */
            if ((token_type = scan_token(c = skip_ws(processingData), &processingData->workp, processingData->work_end, processingData)) != NAM)
            {
                if (c == '\n')
                {
                    break;
                }
                else if (c == ',' || c == ')')
                {
                    cerror("Empty parameter", NULL, 0L, NULL, processingData); /* _E_  */
                    return FALSE;
                }
                else if (processingData->standard && (processingData->stdc_val || processingData->cplus_val) && token_type == OPE && processingData->openum == OP_ELL)
                {
                    /*
                     * Enable variable argument macro which is a feature of
                     * C99.  We enable this even on C90 or C++ for GCC
                     * compatibility.
                     */
                    if (skip_ws(processingData) != ')')
                    {
                        cerror(misplaced_ellip, NULL, 0L, NULL, processingData);
                        return FALSE;
                    }
                    processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs++].len = 3;
                    processingData->parametersProcessingData.nargs |= VA_ARGS;
                    goto ret;
                }
                else
                {
                    cerror(illeg_parm, processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name, 0L, NULL, processingData);
                    return FALSE; /* Bad parameter syntax */
                }
            }

            if (processingData->standard && (processingData->stdc_val || processingData->cplus_val) && str_eq(processingData->identifier, "__VA_ARGS__"))
            {
                cerror(illeg_parm, processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name, 0L, NULL, processingData);
                return FALSE;
                /* __VA_ARGS__ should not be used as a parameter    */
            }

            if (is_formal(processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name, FALSE, processingData))
            {
                cerror("Duplicate parameter name \"%s\"" /* _E_  */
                       , processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name, 0L, NULL, processingData);
                return FALSE;
            }

            processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].len = (size_t)(processingData->workp - processingData->parametersProcessingData.parms[processingData->parametersProcessingData.nargs].name);
            /* Save length of param */
            *processingData->workp++ = ',';
            processingData->parametersProcessingData.nargs++;
        } while ((c = skip_ws(processingData)) == ','); /* Get another parameter*/

        *--processingData->workp = EOS; /* Remove excessive ',' */
        if (c != ')')
        { /* Must end at )        */
#if COMPILER == GNUC
            /* Handle GCC2 variadic params like par...  */
            char *tp = processingData->workp;
            if (processingData->mcpp_mode == STD && (token_type = scan_token(c, &processingData->workp, processingData->work_end)) == OPE && processingData->openum == OP_ELL)
            {
                if ((c = skip_ws()) != ')')
                {
                    cerror(misplaced_ellip, NULL, 0L, NULL);
                    return FALSE;
                }
                *tp = EOS; /* Remove "..."         */
                processingData->parametersProcessingData.nargs |= VA_ARGS;
                processingData->parametersProcessingData.gcc2_va_arg = TRUE;
                goto ret;
            }
#endif
            unget_ch(processingData); /* Push back '\n'       */
            cerror(
                "Missing \",\" or \")\" in parameter list \"(%s\"" /* _E_  */
                ,
                processingData->work_buf, 0L, NULL, processingData);
            return FALSE;
        }
    }
    else
    {
        /*
         * DEF_NOARGS is needed to distinguish between
         * "#define foo" and "#define foo()".
         */
        processingData->parametersProcessingData.nargs = DEF_NOARGS; /* Object-like macro    */
        unget_ch(processingData);
    }
ret:
#if NMACPARS > NMACPARS90MIN
    if ((processingData->warn_level & 4) && (processingData->parametersProcessingData.nargs & ~AVA_ARGS) > processingData->std_limits.n_mac_pars)
        cwarn(many_parms, NULL, (long)processingData->std_limits.n_mac_pars, NULL, processingData);
#endif
    return TRUE;
}

static int get_repl(const char *macroname, processing_data_t* processingData)
/*
 *   Get replacement text i.e. names of formal parameters are converted to
 * the magic numbers, and operators #, ## is converted to magic characters.
 *   Return TRUE if replacement list is legal, else return FALSE.
 *   Any token separator in the text is converted to a single space, no token
 * sepatator is inserted by MCPP.  Those are required by the Standard for
 * stringizing of an argument by # operator.
 *   In POST_STD mode, inserts a space between any tokens in source (except a
 * macro name and the next '(' in macro definition), hence presence or absence
 * of token separator makes no difference.
 */
{
    const char *const mixed_ops = "Macro with mixing of ## and # operators isn't portable"; /* _W4_ */
    const char *const multiple_cats = "Macro with multiple ## operators isn't portable";    /* _W4_ */
    char *prev_token = NULL;                                                                /* Preceding token      */
    char *prev_prev_token = NULL;                                                           /* Pre-preceding token  */
    int multi_cats = FALSE;                                                                 /* Multiple ## operators*/
    int c;
    int token_type; /* Type of token        */
    char *temp;
    char *repl_cur = processingData->parametersProcessingData.repl_base; /* Pointer into repl-text buffer*/

    *repl_cur = EOS;
    processingData->parametersProcessingData.token_p = NULL;
    if (processingData->mcpp_mode == STD)
    {
        c = get_ch(processingData);
        unget_ch(processingData);
        if (((processingData->char_type[c] & SPA) == 0) && (processingData->parametersProcessingData.nargs < 0) && (processingData->warn_level & 1))
            cwarn("No space between macro name \"%s\" and repl-text" /* _W1_ */
                  ,
                  macroname, 0L, NULL, processingData);
    }
    c = skip_ws(processingData); /* Get to the body      */

    while (c != '\n')
    {
        if (processingData->standard)
        {
            prev_prev_token = prev_token;
            prev_token = processingData->parametersProcessingData.token_p;
        }
        processingData->parametersProcessingData.token_p = repl_cur; /* Remember the pointer */
        token_type = scan_token(c, &repl_cur, processingData->parametersProcessingData.repl_end, processingData);

        switch (token_type)
        {
        case OPE: /* Operator or punctuator       */
            if (!processingData->standard)
                break;

            switch (processingData->openum)
            {
            case OP_CAT: /* ##                   */
                if (prev_token == NULL)
                {
                    cerror("No token before ##" /* _E_  */
                           ,
                           NULL, 0L, NULL, processingData);
                    return FALSE;
                }
                else if (*prev_token == CAT)
                {
                    cerror("## after ##", NULL, 0L, NULL, processingData); /* _E_  */
                    return FALSE;
                }
                else if (prev_prev_token && *prev_prev_token == CAT)
                {
                    multi_cats = TRUE;
                }
                else if (prev_prev_token && *prev_prev_token == ST_QUOTE && (processingData->warn_level & 4))
                { /* # parm ##    */
                    cwarn(mixed_ops, NULL, 0L, NULL, processingData);
                }
                repl_cur = processingData->parametersProcessingData.token_p;
                *repl_cur++ = CAT; /* Convert to CAT       */
                break;
            case OP_STR:                                                  /* #                    */
                if (processingData->parametersProcessingData.nargs < 0)                                            /* In object-like macro */
                    break;                                                /* '#' is an usual char */
                if (prev_token && *prev_token == CAT && (processingData->warn_level & 4)) /* ## #         */
                    cwarn(mixed_ops, NULL, 0L, NULL, processingData);
                repl_cur = processingData->parametersProcessingData.token_p; /* Overwrite on #       */
                if ((temp = def_stringization(repl_cur, processingData)) == NULL)
                {
                    return FALSE; /* Error                */
                }
                else
                {
                    repl_cur = temp;
                }
                break;
            default: /* Any operator as it is    */
                break;
            }
            break;
        case NAM:
            /*
         * Replace this name if it's a parm.  Note that the macro name is a
         * possible replacement token.  We stuff DEF_MAGIC in front of the
         * token which is treated as a LETTER by the token scanner and eaten
         * by the macro expanding routine.  This prevents the macro expander
         * from looping if someone writes "#define foo foo".
         */
            temp = is_formal(processingData->identifier, TRUE, processingData);
            if (temp == NULL)
            { /* Not a parameter name */
                if (!processingData->standard)
                    break;
                if ((processingData->stdc_val || processingData->cplus_val) && str_eq(processingData->identifier, "__VA_ARGS__"))
                {
#if COMPILER == GNUC
                    if (processingData->parametersProcessingData.gcc2_va_arg)
                    {
                        cerror("\"%s\" cannot be used in GCC2-spec variadic macro" /* _E_  */
                               ,
                               processingData->identifier, 0L, NULL);
                        return FALSE;
                    }
#endif
                    cerror("\"%s\" without corresponding \"...\"" /* _E_  */
                           ,
                           processingData->identifier, 0L, NULL, processingData);
                    return FALSE;
                }
                if ((temp = mgtoken_save(macroname, processingData)) != NULL)
                    repl_cur = temp; /* Macro name           */
            }
            else
            { /* Parameter name       */
                repl_cur = temp;
#if COMPILER == GNUC
                if (processingData->mcpp_mode == STD && (processingData->parametersProcessingData.nargs & VA_ARGS) && *(repl_cur - 1) == (processingData->parametersProcessingData.nargs & ~AVA_ARGS))
                {
                    if (!str_eq(processingData->identifier, "__VA_ARGS__") && (processingData->warn_level & 2))
                        cwarn(
                            "GCC2-spec variadic macro is defined" /* _W2_ */
                            ,
                            NULL, 0L, NULL);
                    if (prev_token && *prev_token == CAT && prev_prev_token && *prev_prev_token == ',')
                        /* ", ## __VA_ARGS__" is sequence peculiar  */
                        /* to GCC3-spec variadic macro.             */
                        /* Or ", ## last_arg" is sequence peculiar  */
                        /* to GCC2-spec variadic macro.             */
                        processingData->parametersProcessingData.nargs |= GVA_ARGS;
                    /* Mark as sequence peculiar to GCC         */
                    /* This will be warned at expansion time    */
                }
#endif
            }
            break;

        case STR: /* String in mac. body  */
        case CHR: /* Character constant   */
            if (processingData->mcpp_mode == OLD_PREP)
                repl_cur = str_parm_scan(repl_cur, processingData);
            break;
        case SEP:
            if (processingData->mcpp_mode == OLD_PREP && c == COM_SEP)
                repl_cur--; /* Skip comment now     */
            break;
        default: /* Any token as it is   */
            break;
        }

        if ((c = get_ch(processingData)) == ' ' || c == '\t')
        {
            *repl_cur++ = ' '; /* Space                */
            while ((c = get_ch(processingData)) == ' ' || c == '\t')
                ; /* Skip excessive spaces        */
        }
    }

    while (processingData->parametersProcessingData.repl_base < repl_cur && (*(repl_cur - 1) == ' ' || *(repl_cur - 1) == '\t'))
        repl_cur--;  /* Remove trailing spaces   */
    *repl_cur = EOS; /* Terminate work       */

    unget_ch(processingData); /* For syntax check     */
    if (processingData->standard)
    {
        if (processingData->parametersProcessingData.token_p && *processingData->parametersProcessingData.token_p == CAT)
        {
            cerror("No token after ##", NULL, 0L, NULL, processingData); /* _E_  */
            return FALSE;
        }
        if (multi_cats && (processingData->warn_level & 4))
            cwarn(multiple_cats, NULL, 0L, NULL, processingData);
        if ((processingData->parametersProcessingData.nargs & VA_ARGS) && processingData->stdc_ver < 199901L && (processingData->warn_level & 2))
            /* Variable arg macro is the spec of C99, not C90 nor C++98     */
            cwarn("Variable argument macro is defined", /* _W2_ */
                  NULL, 0L, NULL, processingData);
    }

    return TRUE;
}

static char *is_formal(
    const char *name,
    int conv, /* Convert to magic number? */
    processing_data_t* processingData
)
/*
 * If the identifier is a formal parameter, save the MAC_PARM and formal
 * offset, returning the advanced pointer into the replacement text.
 * Else, return NULL.
 */
{
    char *repl_cur;
    const char *va_arg = "__VA_ARGS__";
    param_name_t parm;
    size_t len;
    int i;

    len = strlen(name);
    for (i = 0; i < (processingData->parametersProcessingData.nargs & ~AVA_ARGS); i++)
    { /* For each parameter   */
        parm = processingData->parametersProcessingData.parms[i];
        if ((len == parm.len
             /* Note: parms[].name are comma separated  */
             && memcmp(name, parm.name, parm.len) == 0) ||
            (processingData->standard && (processingData->parametersProcessingData.nargs & VA_ARGS) && i == (processingData->parametersProcessingData.nargs & ~AVA_ARGS) - 1 && conv && str_eq(name, va_arg)))
        {   /* __VA_ARGS__  */
            /* If it's known        */
#if COMPILER == GNUC
            if (processingData->parametersProcessingData.gcc2_va_arg && str_eq(name, va_arg))
                return NULL; /* GCC2 variadic macro  */
#endif
            if (conv)
            {
                repl_cur = processingData->parametersProcessingData.token_p;     /* Overwrite on the name*/
                *repl_cur++ = MAC_PARM; /* Save the signal      */
                *repl_cur++ = i + 1;    /* Save the parm number */
                return repl_cur;        /* Return "gotcha"      */
            }
            else
            {
                return parm.name; /* Duplicate parm name  */
            }
        }
    }

    return NULL; /* Not a formal param   */
}

static char *def_stringization(char *repl_cur, processing_data_t* processingData)
/*
 * Define token stringization.
 * We store a magic cookie (which becomes surrouding " on expansion) preceding
 * the parameter as an operand of # operator.
 * Return the current pointer into replacement text if the token following #
 * is a parameter name, else return NULL.
 */
{
    int c;
    char *temp;

    *repl_cur++ = ST_QUOTE; /* Prefix               */
    if (processingData->char_type[c = get_ch(processingData)] & HSP)
    { /* There is a space     */
        *repl_cur++ = ' ';
        while (processingData->char_type[c = get_ch(processingData)] & HSP) /* Skip excessive spaces*/
            ;
    }
    processingData->parametersProcessingData.token_p = repl_cur; /* Remember the pointer */
    if (scan_token(c, &repl_cur, processingData->parametersProcessingData.repl_end, processingData) == NAM)
    {
        if ((temp = is_formal(processingData->identifier, TRUE, processingData)) != NULL)
        {
            repl_cur = temp;
            return repl_cur;
        }
    }
    cerror("Not a formal parameter \"%s\"", processingData->parametersProcessingData.token_p, 0L, NULL, processingData); /* _E_  */
    return NULL;
}

static char *mgtoken_save(const char *macroname, processing_data_t* processingData)
/*
 * A magic cookie is inserted if the token is identical to the macro name,
 * so the expansion doesn't recurse.
 * Return the advanced pointer into the replacement text or NULL.
 */
{
    char *repl_cur;

    if (str_eq(macroname, processingData->identifier))
    {                            /* Macro name in body   */
        repl_cur = processingData->parametersProcessingData.token_p;      /* Overwrite on token   */
        *repl_cur++ = DEF_MAGIC; /* Save magic marker    */
        repl_cur = stpcpy(repl_cur, processingData->identifier);
        /* And save the token   */
        return repl_cur;
    }
    else
    {
        return NULL;
    }
}

static char *str_parm_scan(char *string_end, processing_data_t* processingData)
/*
 * String parameter scan.
 * This code -- if enabled -- recognizes a formal parameter in a string
 * literal or in a character constant.
 *      #define foo(bar, v) printf("%bar\n", v)
 *      foo( d, i)
 * expands to:
 *      printf("%d\n", i)
 * str_parm_scan() return the advanced pointer into the replacement text.
 * This has been superceded by # stringizing and string concatenation.
 * This routine is called only in OLD_PREP mode.
 */
{
    int delim;
    int c;
    char *tp;
    char *wp; /* Pointer into the quoted literal  */

    delim = *processingData->parametersProcessingData.token_p;
    unget_string(++processingData->parametersProcessingData.token_p, NULL, processingData);
    /* Pseudo-token-parsing in a string literal */
    wp = processingData->parametersProcessingData.token_p;
    while ((c = get_ch(processingData)) != delim)
    {
        processingData->parametersProcessingData.token_p = wp;
        if (scan_token(c, &wp, string_end, processingData) != NAM)
            continue;
        if ((tp = is_formal(processingData->parametersProcessingData.token_p, TRUE, processingData)) != NULL)
            wp = tp;
    }
    *wp++ = delim;
    return wp;
}

static void do_undef(processing_data_t* processingData)
/*
 * Remove the symbol from the defined list.
 * Called from directive().
 */
{
    DEFBUF *defp;
    int c;

    if ((c = skip_ws(processingData)) == '\n')
    {
        cerror(no_ident, NULL, 0L, NULL, processingData);
        unget_ch(processingData);
        return;
    }
    if (scan_token(c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData) != NAM)
    {
        cerror(not_ident, processingData->work_buf, 0L, NULL, processingData);
        skip_nl(processingData);
        unget_ch(processingData);
    }
    else
    {
        if ((defp = look_id(processingData->identifier, processingData)) == NULL)
        {
            if (processingData->warn_level & 8)
                cwarn("\"%s\" wasn't defined" /* _W8_ */
                      ,
                      processingData->identifier, 0L, NULL, processingData);
        }
        else if (processingData->standard && (defp->nargs <= DEF_NOARGS_STANDARD
                              /* Standard predef  */
                              || defp->nargs == DEF_PRAGMA))
        {
            /* _Pragma() pseudo-macro   */
            cerror("\"%s\" shouldn't be undefined" /* _E_  */
                   ,
                   processingData->identifier, 0L, NULL, processingData);
        }
        else if (processingData->standard)
        {
            c = skip_ws(processingData);
            unget_ch(processingData);
            if (c != '\n') /* Trailing junk    */
                return;
            else
                undefine(processingData->identifier, processingData);
        }
        else
        {
            undefine(processingData->identifier, processingData);
        }
    }
}

/*
 *                  C P P   S y m b o l   T a b l e s
 *
 * SBSIZE defines the number of hash-table slots for the symbol table.
 * It must be a power of 2.
 */


#if MCPP_LIB
void init_directive(processing_data_t* processingData)
/* Initialize static variables. */
{
    processingData->num_of_macro = 0;
}
#endif

DEFBUF *look_id(const char *name, processing_data_t* processingData)
/*
 * Look for the identifier in the symbol table.
 * If found, return the table pointer;  Else return NULL.
 */
{
    DEFBUF **prevp;
    int cmp;

    prevp = look_prev(name, &cmp, processingData);

    if (processingData->standard)
        return ((cmp == 0 && (*prevp)->push == 0) ? *prevp : NULL);
    else
        return ((cmp == 0) ? *prevp : NULL);
}

DEFBUF **look_prev(
    const char *name, /* Name of the macro    */
    int *cmp,         /* Result of comparison */
    processing_data_t* processingData
)
/*
 * Look for the place to insert the macro definition.
 * Return a pointer to the previous member in the linked list.
 */
{
    const char *np;
    DEFBUF **prevp;
    DEFBUF *dp;
    size_t s_name;
    size_t hash;

    for (hash = 0, np = name; *np != EOS;)
        hash += *np++;
    hash += s_name = (size_t)(np - name);
    s_name++;
    prevp = &processingData->symtab[hash & SBMASK];
    *cmp = -1; /* Initialize           */

    while ((dp = *prevp) != NULL)
    {
        // Anima ADD
        if ((*cmp = strncmp(dp->name, name, s_name)) >= 0)
            // Anima ADD
            break;
        prevp = &dp->link;
    }

    return prevp;
}

DEFBUF *look_and_install(
    const char *name,      /* Name of the macro    */
    int numargs,           /* The numbers of parms */
    const char *parmnames, /* Names of parameters concatenated */
    const char *repl,      /* Replacement text     */
    processing_data_t* processingData
)
/*
 * Look for the name and (re)define it.
 * Returns a pointer to the definition block.
 * Returns NULL if the symbol was Standard-predefined.
 */
{
    DEFBUF **prevp; /* Place to insert definition       */
    DEFBUF *defp;   /* New definition block */
    int cmp;        /* Result of comparison of new name and old */

    prevp = look_prev(name, &cmp, processingData);
    defp = install_macro(name, numargs, parmnames, repl, prevp, cmp, 0, processingData);
    return defp;
}

DEFBUF *install_macro(
    const char *name,      /* Name of the macro    */
    int numargs,           /* The numbers of parms */
    const char *parmnames, /* Names of parameters concatenated */
    const char *repl,      /* Replacement text     */
    DEFBUF **prevp,        /* The place to insert definition   */
    int cmp,               /* Result of comparison of new name and old */
    int predefine,         /* Predefined macro without leading '_'     */
    processing_data_t* processingData
)
/*
 * Enter this name in the lookup table.
 * Returns a pointer to the definition block.
 * Returns NULL if the symbol was Standard-predefined.
 * Note that predefinedness can be specified by either of 'numargs' or
 * 'predefine'.
 */
{
    DEFBUF *dp;
    DEFBUF *defp;
    size_t s_name, s_parmnames, s_repl;

    defp = *prevp; /* Old definition, if cmp == 0  */
    if (cmp == 0 && defp->nargs < DEF_NOARGS - 1)
        return NULL; /* Standard predefined  */
    if (parmnames == NULL || repl == NULL || (predefine && numargs > 0) || (predefine && predefine != DEF_NOARGS_PREDEF && predefine != DEF_NOARGS_PREDEF_OLD))
        /* Shouldn't happen */
        cfatal("Bug: Illegal macro installation of \"%s\"" /* _F_  */
               ,
               name, 0L, NULL, processingData); /* Use "" instead of NULL   */
    s_name = strlen(name);
    if (processingData->mcpp_mode == STD)
        s_parmnames = strlen(parmnames) + 1;
    else
        s_parmnames = 0;
    s_repl = strlen(repl) + 1;
    dp = (DEFBUF *)
        xmalloc(sizeof(DEFBUF) + s_name + s_parmnames + s_repl);
    if (cmp || (processingData->standard && (*prevp)->push))
    {                    /* New definition   */
        dp->link = defp; /* Insert to linked list    */
        *prevp = dp;
    }
    else
    {                          /* Redefinition             */
        dp->link = defp->link; /* Replace old def with new */
        *prevp = dp;
        free(defp);
    }
    dp->nargs = predefine ? predefine : numargs;
    if (processingData->standard)
    {
        dp->push = 0;
        dp->parmnames = (char *)dp + sizeof(DEFBUF) + s_name;
        dp->repl = dp->parmnames + s_parmnames;
        if (processingData->mcpp_mode == STD)
            memcpy(dp->parmnames, parmnames, s_parmnames);
    }
    else
    {
        dp->repl = (char *)dp + sizeof(DEFBUF) + s_name;
    }
    memcpy(dp->name, name, s_name + 1);
    memcpy(dp->repl, repl, s_repl);
    /* Remember where the macro is defined  */
    dp->fname = processingData->cur_fullname; /* Full-path-list of current file   */
    dp->mline = processingData->src_line;
    if (processingData->standard && cmp && ++processingData->num_of_macro == processingData->std_limits.n_macro + 1 && processingData->std_limits.n_macro && (processingData->warn_level & 4))
        /* '&& std_limits.n_macro' to avoid warning before initialization   */
        cwarn("More than %.0s%ld macros defined" /* _W4_ */
              ,
              NULL, processingData->std_limits.n_macro, NULL, processingData);
    return dp;
}

int undefine(
    const char *name, /* Name of the macro    */
    processing_data_t* processingData
)
/*
 * Delete the macro definition from the symbol table.
 * Returns TRUE, if deleted;
 * Else returns FALSE (when the macro was not defined or was Standard
 * predefined).
 */
{
    DEFBUF **prevp; /* Preceding definition in list     */
    DEFBUF *dp;     /* Definition to delete     */
    int cmp;        /* 0 if defined, else not defined   */

    prevp = look_prev(name, &cmp, processingData);
    dp = *prevp; /* Definition to delete     */
    if (cmp || dp->nargs <= DEF_NOARGS_STANDARD)
        return FALSE; /* Not defined or Standard predefined   */
    if (processingData->standard && dp->push)
        return FALSE;  /* 'Pushed' macro           */
    *prevp = dp->link; /* Link the previous and the next   */
    if ((processingData->mcpp_debug & MACRO_CALL) && dp->mline)
    {
        /* Notice this directive unless the macro is predefined     */
        processingData->mcpp_fprintf(OUT, processingData, "/*undef %ld*//*%s*/\n", processingData->src_line, dp->name);
        processingData->wrong_line = TRUE;
    }
    free(dp); /* Delete the definition    */
    if (processingData->standard)
        processingData->num_of_macro--;
    return TRUE;
}

static void dump_repl(
    const DEFBUF *dp,
    FILE *fp,
    int gcc2_va,
    processing_data_t* processingData)
/*
 * Dump replacement text.
 */
{
    int numargs = dp->nargs;
    char *cp1;
    size_t i;
    int c;
    const char *cp;

    for (cp = dp->repl; (c = *cp++ & UCHARMAX) != EOS;)
    {

        switch (c)
        {
        case MAC_PARM: /* Parameter    */
            c = (*cp++ & UCHARMAX) - 1;
            if (processingData->standard)
            {
                param_name_t parm = processingData->parametersProcessingData.parms[c];
                if ((numargs & VA_ARGS) && c == (numargs & ~AVA_ARGS) - 1)
                {
                    processingData->mcpp_fputs(gcc2_va ? parm.name : "__VA_ARGS__", FP2DEST(fp, processingData), processingData);
                    /* gcc2_va is possible only in STD mode */
                }
                else
                {
                    if (processingData->mcpp_mode == STD)
                    {
                        for (i = 0, cp1 = parm.name; i < parm.len; i++)
                            processingData->mcpp_fputc(*cp1++, FP2DEST(fp, processingData), processingData);
                    }
                    else
                    {
                        processingData->mcpp_fputc('a' + c % 26, FP2DEST(fp, processingData), processingData);
                        if (c > 26)
                            processingData->mcpp_fputc('0' + c / 26, FP2DEST(fp, processingData), processingData);
                    }
                }
            }
            else
            {
                processingData->mcpp_fputc('a' + c % 26, FP2DEST(fp, processingData), processingData);
                if (c > 26)
                    processingData->mcpp_fputc('0' + c / 26, FP2DEST(fp, processingData), processingData);
            }
            break;
        case DEF_MAGIC:
            if (!processingData->standard)
                processingData->mcpp_fputc(c, FP2DEST(fp, processingData), processingData);
            /* Else skip    */
            break;
        case CAT:
            if (processingData->standard)
                processingData->mcpp_fputs("##", FP2DEST(fp, processingData), processingData);
            else
                processingData->mcpp_fputc(c, FP2DEST(fp, processingData), processingData);
            break;
        case ST_QUOTE:
            if (processingData->standard)
                processingData->mcpp_fputs("#", FP2DEST(fp, processingData), processingData);
            else
                processingData->mcpp_fputc(c, FP2DEST(fp, processingData), processingData);
            break;
        case COM_SEP:
            /*
             * Though TOK_SEP coincides to COM_SEP, this cannot appear in
             * Standard mode.
             */
            if (processingData->mcpp_mode == OLD_PREP)
                processingData->mcpp_fputs("/**/", FP2DEST(fp, processingData), processingData);
            break;
        default:
            processingData->mcpp_fputc(c, FP2DEST(fp, processingData), processingData);
            break;
        }
    }
}

/*
 * If the compiler is so-called "one-pass" compiler, compiler-predefined
 * macros are commented out to avoid redefinition.
 */
#if ONE_PASS
#define CAN_REDEF DEF_NOARGS
#else
#define CAN_REDEF DEF_NOARGS_PREDEF
#endif

void dump_a_def(
    const char *why,
    const DEFBUF *dp,
    int newdef,  /* TRUE if parmnames are currently in parms[] */
    int comment, /* Show location of the definition in comment   */
    FILE *fp,
    processing_data_t* processingData)
/*
 * Dump a macro definition.
 */
{
    char *cp, *cp1;
    int numargs = dp->nargs & ~AVA_ARGS;
    int commented;       /* To be commented out  */
    int gcc2_va = FALSE; /* GCC2-spec variadic   */
    int i;

    if (processingData->standard && numargs == DEF_PRAGMA) /* _Pragma pseudo-macro */
        return;
    if ((numargs < CAN_REDEF) || (processingData->standard && dp->push))
        commented = TRUE;
    else
        commented = FALSE;
    if (!comment && commented) /* For -dM option       */
        return;
    if (why)
        processingData->mcpp_fprintf(FP2DEST(fp, processingData), processingData, "%s \"%s\" defined as: ", why, dp->name);
    processingData->mcpp_fprintf(FP2DEST(fp, processingData), processingData, "%s#define %s", commented ? "/* " : "",
                 dp->name); /* Macro name           */
    if (numargs >= 0)
    { /* Parameter list       */
        if (processingData->mcpp_mode == STD)
        {
            const char *appendix = processingData->null;
            if (!newdef)
            {
                /* Make parms[] for dump_repl() */
                for (i = 0, cp = dp->parmnames; i < numargs;
                     i++, cp = cp1 + 1)
                {
                    if ((cp1 = strchr(cp, ',')) == NULL) /* The last arg */
                        processingData->parametersProcessingData.parms[i].len = strlen(cp);
                    else
                        processingData->parametersProcessingData.parms[i].len = (size_t)(cp1 - cp);
                    processingData->parametersProcessingData.parms[i].name = cp;
                }
            }
#if COMPILER == GNUC
            if ((dp->nargs & VA_ARGS) && memcmp(processingData->parametersProcessingData.parms[numargs - 1].name, "...", 3) != 0)
            {
                appendix = "..."; /* Append ... so as to become 'args...' */
                gcc2_va = TRUE;
            }
#endif
            processingData->mcpp_fprintf(FP2DEST(fp, processingData), processingData, "(%s%s)", dp->parmnames, appendix);
        }
        else
        {
            if (newdef)
            {
                processingData->mcpp_fprintf(FP2DEST(fp, processingData), processingData, "(%s)", processingData->parametersProcessingData.parms[0].name);
            }
            else if (numargs == 0)
            {
                processingData->mcpp_fputs("()", FP2DEST(fp, processingData), processingData);
            }
            else
            {
                /* Print parameter list automatically made as:      */
                /* a, b, c, ..., a0, b0, c0, ..., a1, b1, c1, ...   */
                processingData->mcpp_fputc('(', FP2DEST(fp, processingData), processingData);
                for (i = 0; i < numargs; i++)
                { /* Make parameter list  */
                    processingData->mcpp_fputc('a' + i % 26, FP2DEST(fp, processingData), processingData);
                    if (i >= 26)
                        processingData->mcpp_fputc('0' + i / 26, FP2DEST(fp, processingData), processingData);
                    if (i + 1 < numargs)
                        processingData->mcpp_fputc(',', FP2DEST(fp, processingData), processingData);
                }
                processingData->mcpp_fputc(')', FP2DEST(fp, processingData), processingData);
            }
        }
    }
    if (*dp->repl)
    {
        processingData->mcpp_fputc(' ', FP2DEST(fp, processingData), processingData);
        dump_repl(dp, fp, gcc2_va, processingData); /* Replacement text     */
    }
    if (commented)
        /* Standard predefined or one-pass-compiler-predefined  */
        processingData->mcpp_fputs(" */", FP2DEST(fp, processingData), processingData);
    if (comment) /* Not -dM option       */
        processingData->mcpp_fprintf(FP2DEST(fp, processingData), processingData, " \t/* %s:%ld\t*/", dp->fname, dp->mline);
    processingData->mcpp_fputc('\n', FP2DEST(fp, processingData), processingData);
}

void dump_def(
    int comment, /* Location of definition in comment    */
    int K_opt,   /* -K option is specified   */
    processing_data_t* processingData
)
/*
 * Dump all the current macro definitions to output stream.
 */
{
    DEFBUF *dp;
    DEFBUF **symp;

    sharp(NULL, 0, processingData); /* Report the current source file & line    */
    if (comment)
        processingData->mcpp_fputs("/* Currently defined macros. */\n", OUT, processingData);
    for (symp = processingData->symtab; symp < &processingData->symtab[SBSIZE]; symp++)
    {
        if ((dp = *symp) != NULL)
        {
            do
            {
                if (K_opt)
                    processingData->mcpp_fprintf(OUT, processingData, "/*m%s*/\n", dp->name);
                else
                    dump_a_def(NULL, dp, FALSE, comment, processingData->fp_out, processingData);
            } while ((dp = dp->link) != NULL);
        }
    }
    processingData->wrong_line = TRUE; /* Line number is out of sync  */
}

#if MCPP_LIB
void clear_symtable(processing_data_t* processingData)
/*
 * Free all the macro definitions.
 */
{
    DEFBUF *next;
    DEFBUF *dp;
    DEFBUF **symp;

    for (symp = processingData->symtab; symp < &processingData->symtab[SBSIZE]; symp++)
    {
        for (next = *symp; next != NULL;)
        {
            dp = next;
            next = dp->link;
            free(dp); /* Free the symbol      */
        }
        *symp = NULL;
    }
}
#endif
