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
 *                          S U P P O R T . C
 *                  S u p p o r t   R o u t i n e s
 *
 * The common routines used by several source files are placed here.
 */

/*
 * The following are global functions.
 *
 * get_unexpandable()   Gets the next unexpandable token in the line, expanding
 *              macros.
 *              Called from #if, #line and #include processing routines.
 * skip_nl()    Skips over a line.
 * skip_ws()    Skips over white spaces but not skip over the end of the line.
 *              skip_ws() skips also COM_SEP and TOK_SEP.
 * scan_token() Reads the next token of any type into the specified output
 *              pointer, advances the pointer, returns the type of token.
 * scan_quote() Reads a string literal, character constant or header-name from
 *              the input stream, writes out to the specified buffer and
 *              returns the advanced output pointer.
 * get_ch()     Reads the next byte from the current input stream, handling
 *              end of (macro/file) input and embedded comments appropriately.
 * cnv_trigraph()   Maps trigraph sequence to C character.
 * cnv_digraph()    Maps digraph sequence to C character.
 * id_operator()    See whether the identifier is an operator in C++.
 * unget_ch()   Pushs last gotten character back on the input stream.
 * unget_string()   Pushs sequence on the input stream.
 * save_string() Saves a string in malloc() memory.
 * get_file()   Initializes a new FILEINFO structure, called when #include
 *              opens a new file, or from unget_string().
 * xmalloc()    Gets a specified number of bytes from heap memory.
 *              If malloc() returns NULL, exits with a message.
 * xrealloc()   realloc().  If it fails, exits with a message.
 * get_src_location()   Trace back line-column datum into pre-line-splicing
 *              phase.  A function for -K option.
 * cfatal(), cerror(), cwarn()
 *              These routines format print messages to the user.
 * mcpp_fputc(), mcpp_fputs(), mcpp_fprintf()
 *              Wrap library functions to support alternate output to memory
 *              buffer.
 */

#if PREPROCESSED
#include    "mcpp.H"
#else
#include    "system.H"
#include    "internal.H"
#endif

static void     scan_id( int c, processing_data_t* processingData);
                /* Scan an identifier           */
static char *   scan_number( int c, char * out, char * out_end, processing_data_t* processingData);
                /* Scan a preprocessing number  */
static char *   scan_number_prestd( int c, char * out, char * out_end, processing_data_t* processingData);
                /* scan_number() for pre-Standard mode  */
#if OK_UCN
static char *   scan_ucn( int cnt, char * out, processing_data_t* processingData);
                /* Scan an UCN sequence         */
#endif
static char *   scan_op( int c, char * out, processing_data_t* processingData);
                /* Scan an operator or a punctuator     */
static char *   parse_line(processing_data_t* processingData);
                /* Parse a logical line and convert comments    */
static char *   read_a_comment( char * sp, size_t * sizp, processing_data_t* processingData);
                /* Read over a comment          */
static char *   get_line( int in_comment, processing_data_t* processingData);
                /* Get a logical line from file, handle line-splicing   */
static char *   at_eof( int in_comment, processing_data_t* processingData);
                /* Check erroneous end of file  */
static void     do_msg( const char * severity, const char * format, const char * arg1, long arg2, const char * arg3, processing_data_t* processingData);
                /* Putout diagnostic message    */
static char *   cat_line( int del_bsl, processing_data_t* processingData);
                /* Splice the line              */
static void     put_line( char * out, FILE * fp, processing_data_t* processingData);
                /* Put out a logical line       */
static void     dump_token( int token_type, const char * cp, processing_data_t* processingData);
                /* Dump a token and its type    */

#if MCPP_LIB
static int  use_mem_buffers = FALSE;

void    init_support( void)
{
    in_token = in_string = squeezews = FALSE;
    bsl_cat_line.len[ 0] = com_cat_line.len[ 0] = 0;
    clear_exp_mac();
}

typedef struct  mem_buf {
    char *  buffer;
    char *  entry_pt;
    size_t  size;
    size_t  bytes_avail;
} MEMBUF;

static MEMBUF   mem_buffers[ NUM_OUTDEST];

void    mcpp_use_mem_buffers(
    int    tf
)
{
    int i;

    use_mem_buffers = tf ? TRUE : FALSE;

    for (i = 0; i < NUM_OUTDEST; ++i) {
        if (mem_buffers[ i].buffer)
            /* Free previously allocated memory buffer  */
            free( mem_buffers[ i].buffer);
        if (use_mem_buffers) {
            /* Output to memory buffers instead of files    */
            mem_buffers[ i].buffer = NULL;
            mem_buffers[ i].entry_pt = NULL;
            mem_buffers[ i].size = 0;
            mem_buffers[ i].bytes_avail = 0;
        }
    }
}

int    using_mem_buffers( void)
{
    return use_mem_buffers;
}

#define BUF_INCR_SIZE   (NWORK * 2)
#define MAX( a, b)      (((a) > (b)) ? (a) : (b))

static char *   append_to_buffer(
    MEMBUF *    mem_buf_p,
    const char *    string,
    size_t      length
)
{
    if (mem_buf_p->bytes_avail <= length) {  /* Need to allocate more memory */	// Anima ADD
        size_t size = MAX( BUF_INCR_SIZE, length);

        if (mem_buf_p->buffer == NULL) {            /* 1st append   */
            mem_buf_p->size = size;
            mem_buf_p->bytes_avail = size;
            mem_buf_p->buffer = xmalloc( mem_buf_p->size);
            mem_buf_p->entry_pt = mem_buf_p->buffer;
        } else {
            mem_buf_p->size += size;
            mem_buf_p->bytes_avail += size;
            mem_buf_p->buffer = xrealloc( mem_buf_p->buffer, mem_buf_p->size);
            mem_buf_p->entry_pt = mem_buf_p->buffer + mem_buf_p->size
                    - mem_buf_p->bytes_avail;
        }
    }

    /* Append the string to the tail of the buffer  */
    memcpy( mem_buf_p->entry_pt, string, length);
    mem_buf_p->entry_pt += length;
    mem_buf_p->entry_pt[ 0] = '\0';     /* Terminate the string buffer  */
    mem_buf_p->bytes_avail -= length;

    return mem_buf_p->buffer;
}

static int  mem_putc(
    int     c,
    OUTDEST od
)
{
    char string[ 1];

    string[ 0] = (char) c;

    if (append_to_buffer( &(mem_buffers[ od]), string, 1) != NULL)
        return 0;
    else
        return !0;
}

static int  mem_puts(
    const char *    s,
    OUTDEST od
)
{
    if (append_to_buffer( &(mem_buffers[od]), s, strlen(s)) != NULL)
        return 0;
    else
        return !0;
}

char *  mcpp_get_mem_buffer(
    OUTDEST od
)
{
    return mem_buffers[ od].buffer;
}

#endif  /* MCPP_LIB */

#define DEST2FP(od, pd) \
    (od == OUT) ? pd->fp_out : \
    ((od == ERR) ? pd->fp_err : \
    ((od == DBG) ? pd->fp_debug : \
    (NULL)))

/*
 * The following mcpp_*() wrapper functions are intended to centralize
 * the output generated by MCPP.  They support memory buffer alternates to
 * each of the primary output streams: out, err, debug.  The memory buffer
 * output option would be used in a setup where MCPP has been built as a
 * function call - i.e. mcpp_lib_main().
 */

int    mcpp_lib_fputc(
    int     c,
    OUTDEST od,
    processing_data_t* processingData
)
{
#if MCPP_LIB
    if (use_mem_buffers) {
        return mem_putc( c, od);
    } else {
#endif
        FILE *  stream = DEST2FP(od, processingData);

        return (stream != NULL) ? fputc( c, stream) : EOF;
#if MCPP_LIB
    }
#endif
}

int    mcpp_lib_fputs(
    const char *    s,
    OUTDEST od,
    processing_data_t* processingData
)
{
#if MCPP_LIB
    if (use_mem_buffers) {
        return mem_puts( s, od);
    } else {
#endif
        FILE *  stream = DEST2FP(od, processingData);

        return (stream != NULL) ? fputs( s, stream) : EOF;
#if MCPP_LIB
    }
#endif
}

#include <stdarg.h>

int    mcpp_lib_fprintf(
    OUTDEST od,
    processing_data_t* processingData,
    const char *    format,
    ...
)
{
    va_list ap;
    FILE *  stream = DEST2FP(od, processingData);

    if (stream != NULL) {
        int rc;

        va_start( ap, format);
#if MCPP_LIB
        if (use_mem_buffers) {
            static char     mem_buffer[ NWORK];

            rc = vsprintf( mem_buffer, format, ap);

            if (rc != 0) {
                rc = mem_puts( mem_buffer, od);
            }
        } else {
#endif
            rc = vfprintf( stream, format, ap);
#if MCPP_LIB
        }
#endif
        va_end( ap);

        return rc;

    } else {
        return EOF;
    }
}

void mcpp_init_def_out_func(processing_data_t* processingData)
{
    if(processingData->mcpp_fprintf == NULL)
        processingData->mcpp_fprintf = mcpp_lib_fprintf;

    if(processingData->mcpp_fputs == NULL)
        processingData->mcpp_fputs = mcpp_lib_fputs;

    if(processingData->mcpp_fputc == NULL)
        processingData->mcpp_fputc = mcpp_lib_fputc;
}

#if MCPP_LIB
void    mcpp_reset_def_out_func( void)
{
    processingData->mcpp_fputc = mcpp_lib_fputc;
    processingData->mcpp_fputs = mcpp_lib_fputs;
    processingData->mcpp_fprintf = mcpp_lib_fprintf;
}

void    mcpp_set_out_func(
    int (* func_fputc)( int c, OUTDEST od),
    int (* func_fputs)( const char * s, OUTDEST od),
    int (* func_fprintf)( OUTDEST od, const char * format, ...)
)
{
    processingData->mcpp_fputc = func_fputc;
    processingData->mcpp_fputs = func_fputs;
    processingData->mcpp_fprintf = func_fprintf;
}
#endif

int     get_unexpandable(
    int     c,                              /* First char of token  */
    int     diag,                           /* Flag of diagnosis    */
    processing_data_t* processingData
)
/*
 * Get the next unexpandable token in the line, expanding macros.
 * Return the token type.  The token is written in work_buf[].
 * The once expanded macro is never expanded again.
 * Called only from the routines processing #if (#elif, #assert), #line and
 * #include directives in order to diagnose some subtle macro expansions.
 */
{
    DEFBUF *    defp = NULL;
    FILEINFO *  file;
    MFILE *  mf = NULL;					// Anima ADD
    LINE_COL    line_col = { 0L, 0};
    int     token_type = NO_TOKEN;
    int     has_pragma;

    while (c != EOS && c != '\n'                /* In a line        */
            && (mf = processingData->infile->mf         /* Preserve current state   */				// Anima ADD
                , (token_type
                    = scan_token( c, (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData))
                    == NAM)                     /* Identifier       */
            && mf != NULL                       /* In source !      */				// Anima ADD
            && (defp = is_macro( NULL, processingData)) != NULL) {      /* Macro    */
        processingData->expand_macro( defp, processingData->work_buf, processingData->work_end, line_col, & has_pragma);
                                                /* Expand macro     */
        if (has_pragma)
            cerror( "_Pragma operator found in directive line"      /* _E_  */
                    , NULL, 0L, NULL, processingData);
        file = unget_string( processingData->work_buf, defp->name, processingData);     /* Stack to re-read */
        c = skip_ws(processingData);                          /* Skip TOK_SEP     */
        if (file != processingData->infile && processingData->macro_line != MACRO_ERROR && (processingData->warn_level & 1)) {
            /* This diagnostic is issued even if "diag" is FALSE.   */
            cwarn( "Macro \"%s\" is expanded to 0 token"    /* _W1_ */
                    , defp->name, 0L, NULL, processingData);
            if (! processingData->option_flags.no_source_line)
                dump_a_def( "    macro", defp, FALSE, TRUE, processingData->fp_err, processingData);
        }
    }

    if (c == '\n' || c == EOS) {
        unget_ch(processingData);
        return  NO_TOKEN;
    }

    if (diag && mf == NULL && defp && (processingData->warn_level & 1)) {							// Anima ADD
        char    tmp[ NWORK + 16];
        char *  tmp_end = tmp + NWORK;
        char *  tmp_p;
        file = unget_string( processingData->infile->buffer, defp->name, processingData);   /* To diagnose  */
        c = get_ch(processingData);
        while (file == processingData->infile) {    /* Search the expanded macro    */
            if (scan_token( c, (tmp_p = tmp, &tmp_p), tmp_end, processingData) != NAM) {
                c = get_ch(processingData);
                continue;
            }
            if (processingData->standard && str_eq( processingData->identifier, "defined")) {
                cwarn( "Macro \"%s\" is expanded to \"defined\""    /* _W1_ */
                        , defp->name, 0L, NULL, processingData);
                break;
            }
            if (! processingData->standard && str_eq( processingData->identifier, "sizeof")) {
                cwarn( "Macro \"%s\" is expanded to \"sizeof\""     /* _W1_ */
                        , defp->name, 0L, NULL, processingData);
                break;
            }
            c = get_ch(processingData);
        }
        if (file == processingData->infile) {
            processingData->infile->bptr += strlen( processingData->infile->bptr);
            get_ch(processingData);
        }
        unget_ch(processingData);
        if (token_type == OPE) {
            unget_string( processingData->work_buf, NULL, processingData);  /* Set again 'openum'   */
            scan_token( get_ch(processingData), (processingData->workp = processingData->work_buf, &processingData->workp), processingData->work_end, processingData);
        }
    }

    return  token_type;
}

void    skip_nl(processing_data_t* processingData)
/*
 * Skip to the end of the current input line.
 */
{
    processingData->insert_sep = NO_SEP;
    while (processingData->infile && processingData->infile->mf == NULL) {  /* Stacked text         */				// Anima ADD
        processingData->infile->bptr += strlen( processingData->infile->bptr);
        get_ch(processingData);                           /* To the parent        */
    }
    if (processingData->infile)
        processingData->infile->bptr += strlen( processingData->infile->bptr);  /* Source line      */
}

int     skip_ws(processing_data_t* processingData)
/*
 * Skip over horizontal whitespaces.
 */
{
    int     c;

    do {
        c = get_ch(processingData);
    } while (processingData->char_type[ c] & HSP);

    return  c;
}

#define MBMASK          0xFF    /* Mask to hide multibyte char      */

int     scan_token(
    int     c,                  /* The first character of the token */
    char ** out_pp,             /* Pointer to pointer to output buf */
    char *  out_end,            /* End of output buffer             */
    processing_data_t* processingData
)
/*
 *   Scan the next token of any type.
 *   The token is written out to the specified buffer and the output pointer
 * is advanced.  Token is terminated by EOS.  Return the type of token.
 *   If the token is an identifier, the token is also in identifier[].
 *   If the token is a operator or punctuator, return OPE.
 *   If 'c' is token separator, then return SEP.
 *   If 'c' is not the first character of any known token and not a token
 * separator, return SPE.
 *   In POST_STD mode, inserts token separator (a space) between any tokens of
 * source.
 */
{
    char *  out = *out_pp;              /* Output pointer           */
    int     ch_type;                    /* Type of character        */
    int     token_type = 0;             /* Type of token            */
    int     ch;

    if (processingData->standard)
        processingData->supportProcessingData.in_token = TRUE;                /* While a token is scanned */
    c = c & UCHARMAX;
    ch_type = processingData->char_type[ c] & MBMASK;

    switch (ch_type) {
    case LET:                           /* Probably an identifier   */
        switch (c) {
        case 'L':
            if (! processingData->standard)
                goto  ident;
            ch = get_ch(processingData);
            if (processingData->char_type[ ch] & QUO) { /* char_type[ ch] == QUO    */
                if (ch == '"')
                    token_type = WSTR;  /* Wide-char string literal */
                else
                    token_type = WCHR;  /* Wide-char constant       */
                c = ch;
                *out++ = 'L';
                break;                  /* Fall down to "case QUO:" */
            } else {
                unget_ch(processingData);
            }                           /* Fall through             */
        default:                        /* An identifier            */
ident:
            scan_id( c, processingData);
            out = stpcpy( out, processingData->identifier);
            token_type = NAM;
            break;
        }
        if (token_type == NAM)
            break;
        /* Else fall through    -- i.e. WSTR, WCHR  */
    case QUO:                   /* String or character constant     */
        out = scan_quote( c, out, out_end, FALSE, processingData);
        if (token_type == 0) {                  /* Without prefix L */
            if (c == '"')
                token_type = STR;
            else
                token_type = CHR;
        }   /* Else WSTR or WCHR    */
        break;
    case DOT:
        ch = get_ch(processingData);
        unget_ch(processingData);
        if ((processingData->char_type[ ch] & DIG) == 0)        /* Operator '.' or '...'    */
            goto  operat;
        /* Else fall through    */
    case DIG:                           /* Preprocessing number     */
        out = (processingData->standard ? scan_number( c, out, out_end, processingData)
                : scan_number_prestd( c, out, out_end, processingData));
        token_type = NUM;
        break;
    case PUNC:
operat: out = scan_op( c, out, processingData);         /* Operator or punctuator   */
        token_type = OPE;       /* Number is set in global "openum" */
        break;
    default:                /* Special tokens or special characters */
#if OK_UCN
        if (processingData->mcpp_mode == STD && c == '\\' && processingData->stdc2) {
            ch = get_ch(processingData);
            unget_ch(processingData);
            if (ch == 'U' || ch == 'u')
                goto  ident;            /* Universal-Characte-Name  */
        }
#endif
#if OK_MBIDENT
        if (mcpp_mode == STD && (char_type[ c] & mbchk) && stdc3) {
            char *  bptr = infile->bptr;
            processingData->mb_read( c, &infile->bptr, &out);
            infile->bptr = bptr;
            out = *out_pp;
            goto  ident;        /* An identifier with multi-byte characters */
            /* Mbchar cheking has been done in scan_quote() and others. */
        }
#endif
        if ((processingData->standard && (c == CAT || c == ST_QUOTE)) || (processingData->char_type[ c] & SPA))
            token_type = SEP;       /* Token separator or magic char*/
        else
            token_type = SPE;
            /* Unkown token ($, @, multi-byte character or Latin    */
        *out++ = c;
        *out = EOS;
        break;
    }

    if (out_end < out)
        cfatal( "Buffer overflow scanning token \"%s\""     /* _F_  */
                , *out_pp, 0L, NULL, processingData);
    if (processingData->mcpp_debug & TOKEN)
        dump_token( token_type, *out_pp, processingData);
    if (processingData->mcpp_mode == POST_STD && token_type != SEP && processingData->infile->mf != NULL			// Anima ADD
            && (processingData->char_type[ *processingData->infile->bptr & UCHARMAX] & SPA) == 0)
        processingData->insert_sep = INSERT_SEP;    /* Insert token separator       */
    *out_pp = out;

    processingData->supportProcessingData.in_token = FALSE;               /* Token scanning has been done */
    return  token_type;
}

static void scan_id(
    int     c, /* First char of id     */
    processing_data_t* processingData
)
/*
 * Reads the next identifier and put it into identifier[].
 * The caller has already read the first character of the identifier.
 */
{
    char * const     limit = &processingData->identifier[ IDMAX];
#if OK_UCN
    int     uc2 = 0, uc4 = 0;           /* Count of UCN16, UCN32    */
#endif
#if OK_MBIDENT
    int     mb = 0;                     /* Count of MBCHAR  */
#endif
    size_t  len;                        /* Length of identifier     */
    char *  bp = processingData->identifier;

    if (c == IN_SRC) {                  /* Magic character  */
        *bp++ = c;
        if ((processingData->mcpp_debug & MACRO_CALL) && ! processingData->in_directive) {
            *bp++ = get_ch(processingData);           /* Its 2-bytes      */
            *bp++ = get_ch(processingData);           /*      argument    */
        }
        c = get_ch(processingData);
    }

    do {
        if (bp < limit)
            *bp++ = c;
#if OK_UCN
        if (processingData->mcpp_mode == STD && c == '\\' && processingData->stdc2) {
            int     cnt;
            char *  tp = bp;
            
            if ((c = get_ch(processingData)) == 'u') {
                cnt = 4;
            } else if (c == 'U') {
                cnt = 8;
            } else {
                unget_ch(processingData);
                bp--;
                break;
            }
            *bp++ = c;
            if ((bp = scan_ucn( cnt, bp, processingData)) == NULL)      /* Error    */
                return;
            if (cnt == 4)
                uc2++;
            else if (cnt == 8)
                uc4++;
            if (limit <= tp)            /* Too long identifier      */
                bp = tp;                /* Back the pointer         */
            goto  next_c;
        }
#endif  /* OK_UCN   */
#if OK_MBIDENT
        if (mcpp_mode == STD && (char_type[ c] & mbchk) && stdc3) {
            len = processingData->mb_read( c, &infile->bptr, &bp);
            if (len & MB_ERROR) {
                if (infile->mf)													// Anima ADD
                    cerror(
                    "Illegal multi-byte character sequence."    /* _E_  */
                            , NULL, 0L, NULL);
            } else {
                mb += len;
            }
        }
#endif  /* OK_MBIDENT   */
#if OK_UCN
next_c:
#endif
        c = get_ch(processingData);
    } while ((processingData->char_type[ c] & (LET | DIG))      /* Letter or digit  */
#if OK_UCN
            || (processingData->mcpp_mode == STD && c == '\\' && processingData->stdc2)
#endif
#if OK_MBIDENT
            || (mcpp_mode == STD && (char_type[ c] & mbchk) && stdc3)
#endif
        );

    unget_ch(processingData);
    *bp = EOS;

    if (bp >= limit && (processingData->warn_level & 1))        /* Limit of token   */
        cwarn( "Too long identifier truncated to \"%s\""    /* _W1_ */
                , processingData->identifier, 0L, NULL, processingData);

    len = bp - processingData->identifier;
#if IDMAX > IDLEN90MIN
    /* UCN16, UCN32, MBCHAR are counted as one character for each.  */
#if OK_UCN
    if (processingData->mcpp_mode == STD)
        len -= (uc2 * 5) - (uc4 * 9);
#endif
#if OK_MBIDENT
    if (mcpp_mode == STD)
        len -= mb;
#endif
    if (processingData->standard && processingData->infile->mf && len > processingData->std_limits.id_len && (processingData->warn_level & 4))		// Anima ADD
        cwarn( "Identifier longer than %.0s%ld characters \"%s\""   /* _W4_ */
                , NULL, (long) processingData->std_limits.id_len, processingData->identifier, processingData);
#endif  /* IDMAX > IDLEN90MIN   */

    if (processingData->option_flags.dollar_in_name && processingData->supportProcessingData.dollar_diagnosed == FALSE
            && (processingData->warn_level & 2) && strchr( processingData->identifier, '$') != NULL) {
        cwarn( "'$' in identifier \"%s\"", processingData->identifier, 0L, NULL, processingData); /* _W2_ */
        processingData->supportProcessingData.dollar_diagnosed = TRUE;            /* Diagnose only once   */
    }
}

char *  scan_quote(
    int         delim,              /* ', " or < (header-name)      */
    char *      out,                /* Output buffer                */
    char *      out_end,            /* End of output buffer         */
    int         diag,               /* Diagnostic should be output  */
    processing_data_t* processingData
)
/*
 * Scan off a string literal or character constant to the output buffer.
 * Report diagnosis if the quotation is terminated by newline or character
 * constant is empty (provided 'diag' is TRUE).
 * Return the next output pointer or NULL (on error).
 */
{
    const char * const      skip_line = ", skipped the line";   /* _E_  */
    const char * const      unterm_string
                        = "Unterminated string literal%s";
    const char * const      unterm_char
                        = "Unterminated character constant %s%.0ld%s";
    const char * const      empty_const
                        = "Empty character constant %s%.0ld%s";
    const char *    skip;
    size_t      len;
    int         c;
    char *      out_p = out;

    /* Set again in case of called from routines other than scan_token().   */
    if (processingData->standard)
        processingData->supportProcessingData.in_token = TRUE;
    *out_p++ = delim;
    if (delim == '<')
        delim = '>';

scan:
    while ((c = get_ch(processingData)) != EOS) {

#if MBCHAR
        if (processingData->char_type[ c] & processingData->mbchk) {
            /* First of multi-byte character (or shift-sequence)    */
            char *  bptr = processingData->infile->bptr;
            len = processingData->mb_read( c, &processingData->infile->bptr, (*out_p++ = c, &out_p), processingData);
            if (len & MB_ERROR) {
                if (processingData->infile->mf != NULL && processingData->compiling && diag) {				// Anima ADD
                    if (processingData->warn_level & 1) {
                        char *  buf;
                        size_t  chlen;
                        buf = xmalloc( chlen = processingData->infile->bptr - bptr + 2);
                        memcpy( buf, bptr, chlen - 1);
                        buf[ chlen - 1] = EOS;
                        cwarn(
    "Illegal multi-byte character sequence \"%s\" in quotation",    /* _W1_ */
                        buf, 0L, NULL, processingData);
                        free( buf);
                    }
                }
                continue;
            } else {        /* Valid multi-byte character (or sequence) */
                goto  chk_limit;
            }
        }
#endif
        if (c == delim) {
            break;
        } else if (c == '\\' && delim != '>') { /* In string literal    */
#if OK_UCN
            if (processingData->mcpp_mode == STD && processingData->stdc2) {
                int         cnt;
                char *      tp;

                *out_p++ = c;
                if ((c = get_ch(processingData)) == 'u') {
                    cnt = 4;
                } else if (c == 'U') {
                    cnt = 8;
                } else {
                    goto  escape;
                }
                *out_p++ = c;
                if ((tp = scan_ucn( cnt, out_p, processingData)) != NULL)
                    out_p = tp;
                /* Else error   */
                continue;       /* Error or not, anyway continue    */
            }
#endif  /* OK_UCN   */
            *out_p++ = c;                   /* Escape sequence      */
            c = get_ch(processingData);
escape:
#if MBCHAR
            if (processingData->char_type[ c] & processingData->mbchk) {
                                /* '\\' followed by multi-byte char */
                unget_ch(processingData);
                continue;
            }
#endif
            if (! processingData->standard && c == '\n') {  /* <backslash><newline> */
                out_p--;                    /* Splice the lines     */
                if (cat_line( TRUE, processingData) == NULL)        /* End of file  */
                    break;
                c = get_ch(processingData);
            }
        } else if (processingData->mcpp_mode == POST_STD && c == ' ' && delim == '>'
                && processingData->infile->mf == NULL) {											// Anima ADD
            continue;   /* Skip space possibly inserted by macro expansion  */
        } else if (c == '\n') {
            break;
        }
        if (diag && iscntrl( c) && ((processingData->char_type[ c] & SPA) == 0)
                && (processingData->warn_level & 1))
            cwarn(
            "Illegal control character %.0s0lx%02x in quotation"    /* _W1_ */
                    , NULL, (long) c, NULL, processingData);
        *out_p++ = c;
chk_limit:
        if (out_end < out_p) {
            *out_end = EOS;
            cfatal( "Too long quotation", NULL, 0L, NULL, processingData);  /* _F_  */
        }
    }

    if (c == '\n' || c == EOS)
        unget_ch(processingData);
    if (c == delim)
        *out_p++ = delim;
    *out_p = EOS;
    if (diag) {                         /* At translation phase 3   */
        skip = (processingData->infile->mf == NULL) ? NULL : skip_line;								// Anima ADD
        if (c != delim) {
            if (processingData->mcpp_mode == OLD_PREP   /* Implicit closing of quote*/
                    && (delim == '"' || delim == '\''))
                goto  done;
            if (delim == '"') {
                if (processingData->mcpp_mode != POST_STD && processingData->option_flags.lang_asm) {
                    /* STD, KR      */
                    /* Concatenate the unterminated string to the next line */
                    if (processingData->warn_level & 1)
                        cwarn( unterm_string
                                , ", catenated to the next line"    /* _W1_ */
                                , 0L, NULL, processingData);
                    if (cat_line( FALSE, processingData) != NULL)
                        goto  scan;         /* Splice the lines     */
                    /* Else end of file     */
                } else {
                    cerror( unterm_string, skip, 0L, NULL, processingData); /* _E_  */
                }
            } else if (delim == '\'') {
                if (processingData->mcpp_mode != POST_STD && processingData->option_flags.lang_asm) {
                    /* STD, KR      */
                    if (processingData->warn_level & 1)
                        cwarn( unterm_char, out, 0L, NULL, processingData); /* _W1_ */
                    goto  done;
                } else {
                    cerror( unterm_char, out, 0L, skip, processingData);    /* _E_  */
                }
            } else {
                cerror( "Unterminated header name %s%.0ld%s"        /* _E_  */
                        , out, 0L, skip, processingData);
            }
            out_p = NULL;
        } else if (delim == '\'' && out_p - out <= 2) {
            if (processingData->mcpp_mode != POST_STD && processingData->option_flags.lang_asm) {
                /* STD, KR      */
                if (processingData->warn_level & 1)
                    cwarn( empty_const, out, 0L, skip, processingData);     /* _W1_ */
            } else {
                cerror( empty_const, out, 0L, skip, processingData);        /* _E_  */
                out_p = NULL;
                goto  done;
            }
        } else if (processingData->mcpp_mode == POST_STD && delim == '>' && (processingData->warn_level & 2)) {
            cwarn(
        "Header-name enclosed by <, > is an obsolescent feature %s" /* _W2_ */
                    , out, 0L, skip, processingData);
        }
#if NWORK-2 > SLEN90MIN
        if (processingData->standard && out_p - out > processingData->std_limits.str_len && (processingData->warn_level & 4))
            cwarn( "Quotation longer than %.0s%ld bytes"    /* _W4_ */
                    , NULL, processingData->std_limits.str_len, NULL, processingData);
#endif
    }

done:
    processingData->supportProcessingData.in_token = FALSE;
    return  out_p;
}

static char *   cat_line(
    int     del_bsl,        /* Delete the <backslash><newline> ?    */
    processing_data_t* processingData
)
/*
 * If del_bsl == TRUE:
 *     Delete <backslash><newline> sequence in string literal.
 * FALSE: Overwrite the <newline> with <backslash>'n'.
 * Return NULL on end of file.  Called only from scan_quote().
 * This routine is never called in POST_STD mode.
 */
{
    size_t  len;
    char *  save1, * save2;

    if (del_bsl) {          /* Delete the <backslash><newline>      */
        processingData->infile->bptr -= 2;
        len = processingData->infile->bptr - processingData->infile->buffer;
    } else {        /* Overwrite the <newline> with <backslash>'n'  */
        strcpy( processingData->infile->bptr, "\\n");
        len = strlen( processingData->infile->buffer);
    }
    save1 = save_string( processingData->infile->buffer);
    save2 = get_line( FALSE, processingData);   /* infile->buffer is overwritten    */
    if (save2 == NULL) {
        free( save1);
        return  NULL;
    }
    save2 = save_string( processingData->infile->buffer);
    memcpy( processingData->infile->buffer, save1, len);
    strcpy( processingData->infile->buffer + len, save2);               /* Catenate */
    free( save1);
    free( save2);
    if (! del_bsl)
        len -= 2;
    processingData->infile->bptr = processingData->infile->buffer + len;
    return  processingData->infile->bptr;
}

static char *   scan_number(
    int     c,                              /* First char of number */
    char *  out,                            /* Output buffer        */
    char *  out_end,                 /* Limit of output buffer       */
    processing_data_t* processingData
)
/*
 * Read a preprocessing number.
 * By scan_token() we know already that the first c is from 0 to 9 or dot,
 * and if c is dot then the second character is digit.
 * Returns the advanced output pointer.
 * Note: preprocessing number permits non-numeric forms such as 3E+xy,
 *   which are used in stringization or token-concatenation.
 */
{
    char *      out_p = out;        /* Current output pointer       */

    do {
        *out_p++ = c;
        if (c == 'E' || c == 'e'    /* Sign should follow 'E', 'e', */
                || (processingData->stdc3 && (c == 'P' || c == 'p'))
                                            /* 'P' or 'p'.          */
                ) {
            c = get_ch(processingData);
            if (c == '+' || c == '-') {
                *out_p++ = c;
                c = get_ch(processingData);
            }
#if OK_UCN
        } else if (processingData->mcpp_mode == STD && c == '\\' && processingData->stdc3) {
            int     cnt;
            char *  tp;

            if ((c = get_ch(processingData)) == 'u') {
                cnt = 4;
            } else if (c == 'U') {
                cnt = 8;
            } else {
                unget_ch(processingData);
                out_p--;
                break;
            }
            *out_p++ = c;
            if ((tp = scan_ucn( cnt, out_p, processingData)) == NULL)      /* Error    */
                break;
            else
                out_p = tp;
            c = get_ch(processingData);
#endif  /* OK_UCN   */
#if OK_MBIDENT
        } else if (mcpp_mode == STD && (char_type[ c] & mbchk) && stdc3) {
            len = processingData->mb_read( c, &infile->bptr, &out_p);
            if (len & MB_ERROR) {
                if (infile->mf)													// Anima ADD
                    cerror(
                    "Illegal multi-byte character sequence."    /* _E_  */
                            , NULL, 0L, NULL);
            }
#endif  /* OK_MBIDENT   */
        } else {
            c = get_ch(processingData);
        }
    } while ((processingData->char_type[ c] & (DIG | DOT | LET))    /* Digit, dot or letter */
#if OK_UCN
            || (processingData->mcpp_mode == STD && c == '\\' && processingData->stdc3)
#endif
#if OK_MBIDENT
            || (mcpp_mode == STD && (char_type[ c] & mbchk) && stdc3)
#endif
        );

    *out_p = EOS;
    if (out_end < out_p)
        cfatal( "Too long pp-number token \"%s\""           /* _F_  */
                , out, 0L, NULL, processingData);
    unget_ch(processingData);
    return  out_p;
}

/* Original version of DECUS CPP with slight modifications, */
/* too exact for Standard preprocessing.                    */
static char *   scan_number_prestd(
    int         c,                          /* First char of number */
    char *      out,                        /* Output buffer        */
    char *      out_end,            /* Limit of output buffer       */
    processing_data_t* processingData
)
/*
 * Process a number.  We know that c is from 0 to 9 or dot.
 * Algorithm from Dave Conroy's Decus C.
 * Returns the advanced output pointer.
 */
{
    char * const    out_s = out;            /* For diagnostics      */
    int             radix;                  /* 8, 10, or 16         */
    int             expseen;                /* 'e' seen in floater  */
    int             octal89;                /* For bad octal test   */
    int             dotflag;                /* TRUE if '.' was seen */

    expseen = FALSE;                        /* No exponent seen yet */
    octal89 = FALSE;                        /* No bad octal yet     */
    radix = 10;                             /* Assume decimal       */
    if ((dotflag = (c == '.')) != FALSE) {  /* . something?         */
        *out++ = '.';                       /* Always out the dot   */
        if ((processingData->char_type[(c = get_ch(processingData))] & DIG) == 0) {
                                            /* If not a float numb, */
            goto  nomore;                   /* All done for now     */
        }
    }                                       /* End of float test    */
    else if (c == '0') {                    /* Octal or hex?        */
        *out++ = c;                         /* Stuff initial zero   */
        radix = 8;                          /* Assume it's octal    */
        c = get_ch(processingData);                       /* Look for an 'x'      */
        if (c == 'x' || c == 'X') {         /* Did we get one?      */
            radix = 16;                     /* Remember new radix   */
            *out++ = c;                     /* Stuff the 'x'        */
            c = get_ch(processingData);                   /* Get next character   */
        }
    }
    while (1) {                             /* Process curr. char.  */
        /*
         * Note that this algorithm accepts "012e4" and "03.4"
         * as legitimate floating-point numbers.
         */
        if (radix != 16 && (c == 'e' || c == 'E')) {
            if (expseen)                    /* Already saw 'E'?     */
                break;                      /* Exit loop, bad nbr.  */
            expseen = TRUE;                 /* Set exponent seen    */
            radix = 10;                     /* Decimal exponent     */
            *out++ = c;                     /* Output the 'e'       */
            if ((c = get_ch(processingData)) != '+' && c != '-')
                continue;
        }
        else if (radix != 16 && c == '.') {
            if (dotflag)                    /* Saw dot already?     */
                break;                      /* Exit loop, two dots  */
            dotflag = TRUE;                 /* Remember the dot     */
            radix = 10;                     /* Decimal fraction     */
        }
        else {                              /* Check the digit      */
            switch (c) {
            case '8': case '9':             /* Sometimes wrong      */
                octal89 = TRUE;             /* Do check later       */
            case '0': case '1': case '2': case '3':
            case '4': case '5': case '6': case '7':
                break;                      /* Always ok            */

            case 'a': case 'b': case 'c': case 'd': case 'e': case 'f':
            case 'A': case 'B': case 'C': case 'D': case 'E': case 'F':
                if (radix == 16)            /* Alpha's are ok only  */
                    break;                  /* if reading hex.      */
            default:                        /* At number end        */
                goto done;                  /* Break from for loop  */
            }                               /* End of switch        */
        }                                   /* End general case     */
        *out++ = c;                         /* Accept the character */
        c = get_ch(processingData);                       /* Read another char    */
    }                                       /* End of scan loop     */

    if (out_end < out)                      /* Buffer overflow      */
        goto  nomore;
    /*
     * When we break out of the scan loop, c contains the first
     * character (maybe) not in the number.  If the number is an
     * integer, allow a trailing 'L' for long.  If not those, push
     * the trailing character back on the input stream.
     * Floating point numbers accept a trailing 'L' for "long double".
     */
done:
    if (! (dotflag || expseen)) {           /* Not floating point   */
        /*
         * We know that dotflag and expseen are both zero, now:
         *   dotflag signals "saw 'L'".
         */
        for (;;) {
            switch (c) {
            case 'l':
            case 'L':
                if (dotflag)
                    goto nomore;
                dotflag = TRUE;
                break;
            default:
                goto nomore;
            }
            *out++ = c;                     /* Got 'L' .            */
            c = get_ch(processingData);                   /* Look at next, too.   */
        }
    }

nomore: *out = EOS;
    if (out_end < out)
        goto  overflow;
    unget_ch(processingData);                             /* Not part of a number */
    if (octal89 && radix == 8 && (processingData->warn_level & 1))
        cwarn( "Illegal digit in octal number \"%s\""       /* _W1_ */
                , out_s, 0L, NULL, processingData);
    return  out;

overflow:
    cfatal( "Too long number token \"%s\"", out_s, 0L, NULL, processingData);       /* _F_  */
    return  out;
}

#if OK_UCN
static char *   scan_ucn(
    int     cnt,                            /* Bytes of sequence    */
    char *  out,                             /* Output buffer        */
    processing_data_t* processingData
)
/*
 * Scan an UCN sequence and put the sequence to 'out'.
 * Return the advanced pointer or NULL on failure.
 * This routine is never called in POST_STD mode.
 */
{
    uexpr_t value;                              /* Value of UCN     */
    int     i, c;

    value = 0L;
    for (i = 0; i < cnt; i++) {
        c = get_ch(processingData);
        if (! isxdigit( c)) {
            if (processingData->infile->mf)													// Anima ADD
                cerror( "Illegal UCN sequence"              /* _E_  */
                        , NULL, 0L, NULL, processingData);
                *out = EOS;
                unget_ch(processingData);
                return  NULL;
        }
        c = tolower( c);
        *out++ = c;
        c = (isdigit( c) ? (c - '0') : (c - 'a' + 10));
        value = (value << 4) | c;
    }
    if (processingData->infile->mf                              /* In source        */		// Anima ADD
            && ((value >= 0L && value <= 0x9FL
                && value != 0x24L && value != 0x40L && value != 0x60L)
                                    /* Basic source character       */
            || (processingData->stdc3 && (value >= 0xD800L && value <= 0xDFFFL))))
                                    /* Reserved for special chars   */
        cerror( "UCN cannot specify the value %.0s\"%08lx\""    /* _E_    */
                    , NULL, (long) value, NULL, processingData);
    return  out;
}
#endif  /* OK_UCN   */

static char *   scan_op(
    int     c,                          /* First char of the token  */
    char *  out,                         /* Output buffer            */
    processing_data_t* processingData
)
/*
 * Scan C operator or punctuator into the specified buffer.
 * Return the advanced output pointer.
 * The code-number of the operator is stored to global variable 'openum'.
 * Note: '#' is not an operator nor a punctuator in other than directive line,
 *   nevertheless is handled as a punctuator in this cpp for convenience.
 */
{
    int     c2, c3, c4;

    *out++ = c;

    switch (c) {
    case '~':   processingData->openum = OP_COM;    break;
    case '(':   processingData->openum = OP_LPA;    break;
    case ')':   processingData->openum = OP_RPA;    break;
    case '?':   processingData->openum = OP_QUE;    break;
    case ';':    case '[':    case ']':    case '{':
    case '}':    case ',':
        processingData->openum = OP_1;
        break;
    default:
        processingData->openum = OP_2;                  /* Tentative guess          */
    }

    if (processingData->openum != OP_2) {               /* Single byte operators    */
        *out = EOS;
        return  out;
    }

    c2 = get_ch(processingData);                      /* Possibly two bytes ops   */
    *out++ = c2;

    switch (c) {
    case '=':
        processingData->openum = ((c2 == '=') ? OP_EQ : OP_1);          /* ==, =    */
        break;
    case '!':
        processingData->openum = ((c2 == '=') ? OP_NE : OP_NOT);        /* !=, !    */
        break;
    case '&':
        switch (c2) {
        case '&':   processingData->openum = OP_ANA;        break;      /* &&       */
        case '=':   /* openum = OP_2; */    break;      /* &=       */
        default :   processingData->openum = OP_AND;        break;      /* &        */
        }
        break;
    case '|':
        switch (c2) {
        case '|':   processingData->openum = OP_ORO;        break;      /* ||       */
        case '=':   /* openum = OP_2; */    break;      /* |=       */
        default :   processingData->openum = OP_OR;         break;      /* |        */
        }
        break;
    case '<':
        switch (c2) {
        case '<':   c3 = get_ch(processingData);
            if (c3 == '=') {
                processingData->openum = OP_3;                          /* <<=      */
                *out++ = c3;
            } else {
                processingData->openum = OP_SL;                         /* <<       */
                unget_ch(processingData);
            }
            break;
        case '=':   processingData->openum = OP_LE;         break;      /* <=       */
        case ':':                                   /* <: i.e. [    */
            if (processingData->mcpp_mode == STD && processingData->option_flags.dig)
                processingData->openum = OP_LBRCK_D;
            else
                processingData->openum = OP_LT;
            break;
        case '%':                                   /* <% i.e. {    */
            if (processingData->mcpp_mode == STD && processingData->option_flags.dig)
                processingData->openum = OP_LBRACE_D;
            else
                processingData->openum = OP_LT;
            break;
        default :   processingData->openum = OP_LT;         break;      /* <        */
        }
        break;
    case '>':
        switch (c2) {
        case '>':   c3 = get_ch(processingData);
            if (c3 == '=') {
                processingData->openum = OP_3;                          /* >>=      */
                *out++ = c3;
            } else {
                processingData->openum = OP_SR;                         /* >>       */
                unget_ch(processingData);
            }
            break;
        case '=':   processingData->openum = OP_GE;     break;          /* >=       */
        default :   processingData->openum = OP_GT;     break;          /* >        */
        }
        break;
    case '#':
        if (processingData->standard && (processingData->in_define || processingData->macro_line))  /* in #define or macro  */
            processingData->openum = ((c2 == '#') ? OP_CAT : OP_STR);   /* ##, #    */
        else
            processingData->openum = OP_1;                              /* #        */
        break;
    case '+':
        switch (c2) {
        case '+':                                       /* ++       */
        case '=':   /* openum = OP_2; */    break;      /* +=       */
        default :   processingData->openum = OP_ADD;        break;      /* +        */
        }
        break;
    case '-':
        switch (c2) {
        case '-':                                       /* --       */
        case '=':                                       /* -=       */
            /* openum = OP_2;   */
            break;
        case '>':
            if (processingData->cplus_val) {
                if ((c3 = get_ch(processingData)) == '*') {           /* ->*      */
                    processingData->openum = OP_3;
                    *out++ = c3;
                } else {
                    /* openum = OP_2;   */
                    unget_ch(processingData);
                }
            }   /* else openum = OP_2;  */              /* ->       */
            /* else openum = OP_2;      */
            break;
        default :   processingData->openum = OP_SUB;        break;      /* -        */
        }
        break;
    case '%':
        switch (c2) {
        case '=':                           break;      /* %=       */
        case '>':                                   /* %> i.e. }    */
            if (processingData->mcpp_mode == STD && processingData->option_flags.dig)
                processingData->openum = OP_RBRACE_D;
            else
                processingData->openum = OP_MOD;
            break;
        case ':':
            if (processingData->mcpp_mode == STD && processingData->option_flags.dig) {
                if ((c3 = get_ch(processingData)) == '%') {
                    if ((c4 = get_ch(processingData)) == ':') {   /* %:%: i.e. ## */
                        processingData->openum = OP_DSHARP_D;
                        *out++ = c3;
                        *out++ = c4;
                    } else {
                        unget_ch(processingData);
                        unget_ch(processingData);
                        processingData->openum = OP_SHARP_D;        /* %: i.e. #    */
                    }
                } else {
                    unget_ch(processingData);
                    processingData->openum = OP_SHARP_D;            /* %: i.e. #    */
                }
                if (processingData->in_define) {                    /* in #define   */
                    if (processingData->openum == OP_DSHARP_D)
                        processingData->openum = OP_CAT;
                    else
                        processingData->openum = OP_STR;
                }
            } else {
                processingData->openum = OP_MOD;
            }
            break;
        default :   processingData->openum = OP_MOD;        break;      /* %        */
        }
        break;
    case '*':
        if (c2 != '=')                                  /* *        */
            processingData->openum = OP_MUL;
        /* else openum = OP_2;  */                      /* *=       */
        break;
    case '/':
        if (c2 != '=')                                  /* /        */
            processingData->openum = OP_DIV;
        /* else openum = OP_2;  */                      /* /=       */
        break;
    case '^':
        if (c2 != '=')                                  /* ^        */
            processingData->openum = OP_XOR;
        /* else openum = OP_2;  */                      /* ^=       */
        break;
    case '.':
        if (processingData->standard) {
            if (c2 == '.') {
                c3 = get_ch(processingData);
                if (c3 == '.') {
                    processingData->openum = OP_ELL;                    /* ...      */
                    *out++ = c3;
                    break;
                } else {
                    unget_ch(processingData);
                    processingData->openum = OP_1;
                }
            } else if (processingData->cplus_val && c2 == '*') {        /* .*       */
                /* openum = OP_2    */  ;
            } else {                                    /* .        */
                processingData->openum = OP_1;
            }
        } else {    
            processingData->openum = OP_1;
        }
        break;
    case ':':
        if (processingData->cplus_val && c2 == ':')                     /* ::       */
            /* openum = OP_2    */  ;
        else if (processingData->mcpp_mode == STD && c2 == '>' && processingData->option_flags.dig)
            processingData->openum = OP_RBRCK_D;                    /* :> i.e. ]    */
        else                                            /* :        */
            processingData->openum = OP_COL;
        break;
    default:                                    /* Never reach here */
        cfatal( "Bug: Punctuator is mis-implemented %.0s0lx%x"      /* _F_  */
                , NULL, (long) c, NULL, processingData);
        processingData->openum = OP_1;
        break;
    }

    switch (processingData->openum) {
    case OP_STR:
        if (processingData->mcpp_mode == STD && c == '%')    break;              /* %:   */
    case OP_1:
    case OP_NOT:    case OP_AND:    case OP_OR:     case OP_LT:
    case OP_GT:     case OP_ADD:    case OP_SUB:    case OP_MOD:
    case OP_MUL:    case OP_DIV:    case OP_XOR:    case OP_COM:
    case OP_COL:    /* Any single byte operator or punctuator       */
        unget_ch(processingData);
        out--;
        break;
    default:        /* Two or more bytes operators or punctuators   */
        break;
    }

    *out = EOS;
    return  out;
}

int     id_operator(const char *    name)
/*
 * Check whether the name is identifier-like operator in C++.
 * Return the operator number if matched, return 0 if not matched.
 * Note: these identifiers are defined as macros in <iso646.h> in C95.
 * This routine is never called in POST_STD mode.
 */
{
    typedef struct  id_op {
        const char *    name;
        int             op_num;
    } ID_OP;

    ID_OP   id_ops[] = {
        { "and",    OP_ANA},
        { "and_eq", OP_2},
        { "bitand", OP_AND},
        { "bitor",  OP_OR},
        { "compl",  OP_COM},
        { "not",    OP_NOT},
        { "not_eq", OP_NE},
        { "or",     OP_ORO},
        { "or_eq",  OP_2},
        { "xor",    OP_XOR},
        { "xor_eq", OP_2},
        { NULL,     0},
    };

    ID_OP *     id_p = id_ops;

    while (id_p->name != NULL) {
        if (str_eq( name, id_p->name))
            return  id_p->op_num;
        id_p++;
    }
    return  0;
}

void    expanding(
    const char *    name,       /* The name of (nested) macro just expanded. */
    int             to_be_freed,/* The name should be freed later.  */
    processing_data_t* processingData
)
/*
 * Remember used macro name for diagnostic.
 */
{
    if (processingData->supportProcessingData.exp_mac_ind < EXP_MAC_IND_MAX - 1) {
        processingData->supportProcessingData.exp_mac_ind++;
    } else {
        clear_exp_mac(processingData);
        processingData->supportProcessingData.exp_mac_ind++;
    }
    processingData->supportProcessingData.expanding_macro[processingData->supportProcessingData.exp_mac_ind].name = name;
    processingData->supportProcessingData.expanding_macro[processingData->supportProcessingData.exp_mac_ind].to_be_freed = to_be_freed;
}

void    clear_exp_mac(processing_data_t* processingData)
/*
 * Initialize expanding_macro[] freeing names registered in
 * name_to_be_freed[].
 */
{
    int     i;

    for (i = 1; i < EXP_MAC_IND_MAX; i++) {
        if (processingData->supportProcessingData.expanding_macro[ i].to_be_freed) {
            free( (void *) processingData->supportProcessingData.expanding_macro[ i].name);
            processingData->supportProcessingData.expanding_macro[ i].to_be_freed = FALSE;
        }
    }
    processingData->supportProcessingData.exp_mac_ind = 0;
}

int     get_ch(processing_data_t* processingData)
/*
 * Return the next character from a macro or the current file.
 * Always return the value representable by unsigned char.
 */
{
    int             len;
    int             c;
    FILEINFO *      file;

    /*
     * 'in_token' is set to TRUE while scan_token() is executed (and
     * scan_id(), scan_quote(), scan_number(), scan_ucn() and scan_op()
     * via scan_token()) in Standard mode to simplify tokenization.
     * Any token cannot cross "file"s.
     */
    if (processingData->supportProcessingData.in_token)
        return (*processingData->infile->bptr++ & UCHARMAX);

    if ((file = processingData->infile) == NULL)
        return  CHAR_EOF;                   /* End of all input     */

    if (processingData->mcpp_mode == POST_STD && file->mf) {        /* In a source file     */		// Anima ADD
        switch (processingData->insert_sep) {
        case NO_SEP:
            break;
        case INSERT_SEP:                /* Insert a token separator */
            processingData->insert_sep = INSERTED_SEP;      /* Remember this fact   */
            return  ' ';                    /*   for unget_ch().    */
        case INSERTED_SEP:                  /* Has just inserted    */
            processingData->insert_sep = NO_SEP;            /* Clear the flag       */
            break;
        }
    }
    if (! processingData->standard && processingData->supportProcessingData.squeezews) {
        if (*file->bptr == ' ')
            file->bptr++;                   /* Squeeze white spaces */
        processingData->supportProcessingData.squeezews = FALSE;
    }

    if (processingData->mcpp_debug & GETC) {
        processingData->mcpp_fprintf( DBG, processingData, "get_ch(%s) '%c' line %ld, bptr = %d, buffer"
            , file->mf ? processingData->cur_fullname : file->real_fname ? file->real_fname			// Anima ADD
            : file->filename ? file->filename : "NULL"
            , *file->bptr & UCHARMAX
            , processingData->src_line, (int) (file->bptr - file->buffer));
        dump_string( NULL, file->buffer, processingData);
        dump_unget( "get entrance", processingData);
    }

    /*
     * Read a character from the current input logical line or macro.
     * At EOS, either finish the current macro (freeing temporary storage)
     * or get another logical line by parse_line().
     * At EOF, exit the current file (#included) or, at EOF from the MCPP input
     * file, return CHAR_EOF to finish processing.
     * The character is converted to int with no sign-extension.
     */
    if ((c = (*file->bptr++ & UCHARMAX)) != EOS) {
        if (processingData->standard)
            return  c;                      /* Just a character     */
        if (! processingData->supportProcessingData.in_string && c == '\\' && *file->bptr == '\n'
                && processingData->in_define        /* '\\''\n' is deleted in #define line, */
                    /*   provided the '\\' is not the 2nd byte of mbchar.   */
                && ! last_is_mbchar( file->buffer, strlen( file->buffer) - 2
                && ! processingData->keep_spaces, processingData)
            ) {
            if (*(file->bptr - 2) == ' ')
                processingData->supportProcessingData.squeezews = TRUE;
        } else {
            return  c;
        }
    }

    /*
     * Nothing in current line or macro.  Get next line (if input from a
     * file), or do end of file/macro processing, and reenter get_ch() to
     * restart from the top.
     */
    if (file->mf &&                         /* In source file       */		// Anima ADD
            parse_line(processingData) != NULL)           /* Get line from file   */
        return  get_ch(processingData);
    /*
     * Free up space used by the (finished) file or macro and restart
     * input from the parent file/macro, if any.
     */
    processingData->infile = file->parent;                  /* Unwind file chain    */
    free( file->buffer);                    /* Free buffer          */
    if (processingData->infile == NULL) {                   /* If at end of input   */
        free( file->filename);
        free( file->src_dir);
        free( file);    /* full_fname is the same with filename for main file*/
        return  CHAR_EOF;                   /* Return end of file   */
    }
    if (file->mf) {                         /* Source file included */		// Anima ADD
        free( file->filename);              /* Free filename        */
        free( file->src_dir);               /* Free src_dir         */
        //fclose( file->fp);                  /* Close finished file  */	// Anima ADD
		mfclose(file->mf);
        /* Do not free file->real_fname and file->full_fname        */
        processingData->cur_fullname = processingData->infile->full_fname;
        processingData->cur_fname = processingData->infile->real_fname;     /* Restore current fname*/
        if (processingData->infile->pos != 0L) {            /* Includer was closed  */
            //infile->fp = fopen( cur_fullname, "r");						// Anima ADD
            //fseek( infile->fp, infile->pos, SEEK_SET);					// Anima ADD
			processingData->infile->mf = mfopen(processingData->cur_fullname);								// Anima ADD
			mfseek(processingData->infile->mf, processingData->infile->pos);								// Anima ADD
        }   /* Re-open the includer and restore the file-position   */
        len = (int) (processingData->infile->bptr - processingData->infile->buffer);
        processingData->infile->buffer = xrealloc( processingData->infile->buffer, NBUFF);
            /* Restore full size buffer to get the next line        */
        processingData->infile->bptr = processingData->infile->buffer + len;
        processingData->src_line = processingData->infile->line;            /* Reset line number    */
        processingData->inc_dirp = processingData->infile->dirp;            /* Includer's directory */
#if MCPP_LIB
        mcpp_set_out_func( infile->last_fputc, infile->last_fputs,
                           infile->last_fprintf);
#endif
        processingData->include_nest--;
        processingData->src_line++;                         /* Next line to #include*/
        sharp( NULL, processingData->infile->include_opt ? 1 : (file->include_opt ? 0 : 2), processingData);
            /* Need a #line now.  Marker depends on include_opt.    */
            /* The file of include_opt should be marked as 1.       */
            /* Else if returned from include_opt file, it is the    */
            /* main input file, and should not be marked.           */
            /* Else, it is normal includer file, and marked as 2.   */
        processingData->src_line--;
        processingData->newlines = 0;                       /* Clear the blank lines*/
        if (processingData->mcpp_debug & MACRO_CALL)    /* Should be re-initialized */
            processingData->supportProcessingData.com_cat_line.last_line = processingData->supportProcessingData.bsl_cat_line.last_line = 0L;
    } else if (file->filename) {            /* Expanding macro      */
        if (processingData->macro_name)     /* file->filename should be freed later */
            expanding( file->filename, TRUE, processingData);
        else
            free( file->filename);
    }
    free( file);                            /* Free file space      */
    return  get_ch(processingData);                       /* Get from the parent  */
}

static char *   parse_line(processing_data_t* processingData)
/*
 * ANSI (ISO) C: translation phase 3.
 * Parse a logical line.
 * Check illegal control characters.
 * Check unterminated string literal, character constant or comment.
 * Convert each comment to one space (or spaces of the comment length on
 * 'keep_spaces' mode)..
 * Squeeze succeding white spaces other than <newline> (including comments) to
 * one space (unless keep_spaces == TRUE).
 * The lines might be spliced by comments which cross the lines.
 */
{
    char *      temp;                       /* Temporary buffer     */
    char *      limit;                      /* Buffer end           */
    char *      tp;     /* Current pointer into temporary buffer    */
    char *      sp;                 /* Pointer into input buffer    */
    size_t      com_size;
    int         c;

    if ((sp = get_line( FALSE, processingData)) == NULL)    /* Next logical line    */
        return  NULL;                       /* End of a file        */
    if (processingData->in_asm) {                           /* In #asm block        */
        while (processingData->char_type[ *sp++ & UCHARMAX] & SPA)
            ;
        if (*--sp == '#')                   /* Directive line       */
            processingData->infile->bptr = sp;
        return  processingData->infile->bptr;               /* Don't tokenize       */
    }
    tp = temp = xmalloc( (size_t) NBUFF);
    limit = temp + NBUFF - 2;

    while (processingData->char_type[ c = *sp++ & UCHARMAX] & HSP) {
        if (processingData->mcpp_mode != POST_STD)
            /* Preserve line top horizontal white spaces    */
            /*      as they are for human-readability       */
            *tp++ = c;
        /* Else skip the line top spaces    */
    }
    sp--;

    while ((c = *sp++ & UCHARMAX) != '\n') {

        switch (c) {
        case '/':
            switch (*sp++) {
            case '*':                       /* Start of a comment   */
com_start:
                if ((sp = read_a_comment( sp, &com_size, processingData)) == NULL) {
                    free( temp);            /* End of file with un- */
                    return  NULL;           /*   terminated comment */
                }
                if (processingData->keep_spaces && processingData->mcpp_mode != OLD_PREP) {
                    if (tp + com_size >= limit - 1)     /* Too long comment */
                        com_size = limit - tp - 1;      /* Truncate */
                    while (com_size--)
                        *tp++ = ' ';        /* Spaces of the comment length */
                    break;
                }
                switch (processingData->mcpp_mode) {
                case POST_STD:
                    if (temp < tp && *(tp - 1) != ' ')
                        *tp++ = ' ';        /* Squeeze white spaces */
                    break;
                case OLD_PREP:
                    if (temp == tp
                            || ! (processingData->char_type[ *(tp - 1) & UCHARMAX] & HSP))
                        *tp++ = COM_SEP;    /* Convert to magic character   */
                    break;
                default:
                    if (temp == tp ||
                            ! (processingData->char_type[ *(tp - 1) & UCHARMAX] & HSP))
                        *tp++ = ' ';        /* Squeeze white spaces */
                    break;
                }
                break;
            case '/':                                       /* //   */
                if (! processingData->standard)
                    goto  not_comment;
                /* Comment when C++ or __STDC_VERSION__ >= 199901L      */
                /* Need not to convert to a space because '\n' follows  */
                if (! processingData->stdc2 && (processingData->warn_level & 2))
                    cwarn( "Parsed \"//\" as comment"       /* _W2_ */
                            , NULL, 0L, NULL, processingData);
                if (processingData->keep_comments) {
                    sp -= 2;
                    while (*sp != '\n')     /* Until end of line    */
                        processingData->mcpp_fputc( *sp++, OUT, processingData);
                }
                goto  end_line;
            default:                        /* Not a comment        */
not_comment:
// Anima ADD
				if (limit < tp) {
					cfatal( "Failed to parse non-comment and wrote beyond temp area"     /* _F_  */
						   , NULL, 0L, NULL, processingData);
					*tp = EOS;
				}
// Anima ADD
                *tp++ = '/';
                sp--;                       /* To re-read           */
                break;
            }
            break;
        case '\r':                          /* Vertical white spaces*/
                /* Note that [CR+LF] is already converted to [LF].  */
        case '\f':
        case '\v':
            if (processingData->warn_level & 4)
                cwarn( "Converted %.0s0x%02lx to a space"   /* _W4_ */
                    , NULL, (long) c, NULL, processingData);
        case '\t':                          /* Horizontal space     */
        case ' ':
// Anima ADD
			if (limit < tp) {
				cfatal( "Failed to parse space and wrote beyond temp area"     /* _F_  */
					   , NULL, 0L, NULL, processingData);
				*tp = EOS;
			}
            if (processingData->keep_spaces) {
                if (c == '\t')
                    *tp++ = '\t';
                else
					*tp++ = ' ';            /* Convert to ' '       */
            } else if (tp > temp && !(processingData->char_type[ *(tp - 1) & UCHARMAX] & HSP)) {
                *tp++ = ' ';                /* Squeeze white spaces */
            } else if (processingData->mcpp_mode == OLD_PREP && tp > temp && *(tp - 1) == COM_SEP) {
                *(tp - 1) = ' ';    /* Replace COM_SEP with ' '     */
            }
// Anima ADD
			break;
        case '"':                           /* String literal       */
        case '\'':                          /* Character constant   */
            processingData->infile->bptr = sp;
            if (processingData->standard) {
                tp = scan_quote( c, tp, limit, TRUE, processingData);
            } else {
                processingData->supportProcessingData.in_string = TRUE;   /* Enable line splicing by scan_quote() */
                tp = scan_quote( c, tp, limit, TRUE, processingData);   /* (not by get_ch())*/
                processingData->supportProcessingData.in_string = FALSE;
            }
            if (tp == NULL) {
                free( temp);                /* Unbalanced quotation */
                return  parse_line(processingData);       /* Skip the line        */
            }
            sp = processingData->infile->bptr;
            break;
        default:
            if (iscntrl( c)) {
                cerror(             /* Skip the control character   */
    "Illegal control character %.0s0x%lx, skipped the character"    /* _E_  */
                        , NULL, (long) c, NULL, processingData);
            } else {                        /* Any valid character  */
                *tp++ = c;
            }
            break;
        }

        if (limit < tp) {
            *tp = EOS;
            cfatal( "Too long line spliced by comments"     /* _F_  */
                    , NULL, 0L, NULL, processingData);
        }
    }

end_line:
    if (temp < tp && (processingData->char_type[ *(tp - 1) & UCHARMAX] & HSP))
        tp--;                       /* Remove trailing white space  */
    *tp++ = '\n';
    *tp = EOS;
    processingData->infile->bptr = strcpy( processingData->infile->buffer, temp);   /* Write back to buffer */
    free( temp);
    if (processingData->macro_line != 0 && processingData->macro_line != MACRO_ERROR) { /* Expanding macro  */
        temp = processingData->infile->buffer;
        while (processingData->char_type[ *temp & UCHARMAX] & HSP)
            temp++;
        if (*temp == '#'        /* This line starts with # token    */
                || (processingData->mcpp_mode == STD && *temp == '%' && *(temp + 1) == ':'))
            if (processingData->warn_level & 1)
                cwarn(
    "Macro started at line %.0s%ld swallowed directive-like line"   /* _W1_ */
                    , NULL, processingData->macro_line, NULL, processingData);
    }
    return  processingData->infile->buffer;
}

static char *   read_a_comment(
    char *      sp,                         /* Source               */
    size_t *    sizp,                       /* Size of the comment  */
    processing_data_t* processingData
)
/*
 * Read over a comment (which may cross the lines).
 */
{
    int         c;
    char *      saved_sp;
    int         cat_line = 0;       /* Number of catenated lines    */

    if (processingData->keep_spaces) {
        saved_sp = sp - 2;          /* '-2' for beginning / and *   */
        *sizp = 0;
    }        
    if (processingData->keep_comments)                      /* If writing comments  */
        processingData->mcpp_fputs( "/*", OUT, processingData);             /* Write the initializer*/
    c = *sp++;

    while (1) {                             /* Eat a comment        */
        if (processingData->keep_comments)
            processingData->mcpp_fputc( c, OUT, processingData);

        switch (c) {
        case '/':
            if ((c = *sp++) != '*')         /* Don't let comments   */
                continue;                   /*   nest.              */
            if (processingData->warn_level & 1)
                cwarn( "\"/*\" within comment", NULL, 0L, NULL, processingData);    /* _W1_ */
            if (processingData->keep_comments)
                processingData->mcpp_fputc( c, OUT, processingData);
                                            /* Fall into * stuff    */
        case '*':
            if ((c = *sp++) != '/')         /* If comment doesn't   */
                continue;                   /*   end, look at next. */
            if (processingData->keep_comments) {            /* Put out comment      */
                processingData->mcpp_fputc( c, OUT, processingData);        /*   terminator, too.   */
                processingData->mcpp_fputc( '\n', OUT, processingData);     /* Append '\n' to avoid */
                    /*  trouble on some other tools such as rpcgen. */
                processingData->wrong_line = TRUE;
            }
            if (processingData->keep_spaces)                /* Save the length      */
                *sizp = *sizp + (sp - saved_sp);
            if ((processingData->mcpp_debug & MACRO_CALL) && processingData->compiling) {
                if (cat_line) {
                    cat_line++;
                    processingData->supportProcessingData.com_cat_line.len[ cat_line]         /* Catenated length */
                            = processingData->supportProcessingData.com_cat_line.len[ cat_line - 1]
                                + strlen( processingData->infile->buffer) - 1;
                                            /* '-1' for '\n'        */
                    processingData->supportProcessingData.com_cat_line.last_line = processingData->src_line;
                }
            }
            return  sp;                     /* End of comment       */
        case '\n':                          /* Line-crossing comment*/
            if (processingData->keep_spaces)                /* Save the length      */
                *sizp = *sizp + (sp - saved_sp) - 1;    /* '-1' for '\n'    */
            if ((processingData->mcpp_debug & MACRO_CALL) && processingData->compiling) {
                                    /* Save location informations   */
                if (cat_line == 0)  /* First line of catenation     */
                    processingData->supportProcessingData.com_cat_line.start_line = processingData->src_line;
                if (cat_line >= MAX_CAT_LINE - 1) {
                    *sizp = 0;      /* Discard the too long comment */
                    cat_line = 0;
                    if (processingData->warn_level & 4)
                        cwarn(
                        "Too long comment, discarded up to here"    /* _W4_ */
                                , NULL, 0L, NULL, processingData);
                }
                cat_line++;
                processingData->supportProcessingData.com_cat_line.len[ cat_line]
                        = processingData->supportProcessingData.com_cat_line.len[ cat_line - 1]
                            + strlen( processingData->infile->buffer) - 1;
            }
            if ((saved_sp = sp = get_line( TRUE, processingData)) == NULL)
                return  NULL;       /* End of file within comment   */
                /* Never happen, because at_eof() supplement closing*/
            processingData->wrong_line = TRUE;      /* We'll need a #line later     */
            break;
        default:                            /* Anything else is     */
            break;                          /*   just a character   */
        }                                   /* End switch           */

        c = *sp++;
    }                                       /* End comment loop     */

    return  sp;                             /* Never reach here     */
}

static char *   mcpp_fgets(
    char *  s,
    int     size,
    MFILE *  mf		// Anima ADD
)
{
    return mfgets( s, size, mf);	// Anima ADD
}

static char *   get_line(int in_comment, processing_data_t* processingData)
/*
 * ANSI (ISO) C: translation phase 1, 2.
 * Get the next logical line from source file.
 * Convert [CR+LF] to [LF]. 
 */
{
#if COMPILER == INDEPENDENT
#define cr_warn_level 1
#else
#define cr_warn_level 2
#endif
    static int  cr_converted;
    int     converted = FALSE;
    int     len;                            /* Line length - alpha  */
    char *  ptr;
    int     cat_line = 0;           /* Number of catenated lines    */

    if (processingData->infile == NULL)                     /* End of a source file */
        return  NULL;
    ptr = processingData->infile->bptr = processingData->infile->buffer;
    if ((processingData->mcpp_debug & MACRO_CALL) && processingData->src_line == 0) /* Initialize   */
        processingData->supportProcessingData.com_cat_line.last_line = processingData->supportProcessingData.bsl_cat_line.last_line = 0L;

    while (mcpp_fgets( ptr, (int) (processingData->infile->buffer + NBUFF - ptr), processingData->infile->mf)	// Anima ADD
            != NULL) {
        /* Translation phase 1  */
        processingData->src_line++;                 /* Gotten next physical line    */
        if (processingData->standard && processingData->src_line == processingData->std_limits.line_num + 1
                && (processingData->warn_level & 1))
            cwarn( "Line number %.0s\"%ld\" got beyond range"       /* _W1_ */
                    , NULL, processingData->src_line, NULL, processingData);
        if (processingData->mcpp_debug & (TOKEN | GETC)) {  /* Dump it to DBG       */
            processingData->mcpp_fprintf( DBG, processingData, "\n#line %ld (%s)", processingData->src_line, processingData->cur_fullname);
            dump_string( NULL, ptr, processingData);
        }
        len = strlen( ptr);
        if (NBUFF - 1 <= ptr - processingData->infile->buffer + len
                && *(ptr + len - 1) != '\n') {
                /* The line does not yet end, though the buffer is full.    */
            if (NBUFF - 1 <= len)
                cfatal( "Too long source line"              /* _F_  */
                        , NULL, 0L, NULL, processingData);
            else
                cfatal( "Too long logical line"             /* _F_  */
                        , NULL, 0L, NULL, processingData);
        }
        if (len == 0 || *(ptr + len - 1) != '\n')   /* Unterminated source line */	// Anima ADD
            break;
        if (len >= 2 && *(ptr + len - 2) == '\r') {         /* [CR+LF]      */
            *(ptr + len - 2) = '\n';
            *(ptr + --len) = EOS;
            if (! cr_converted && (processingData->warn_level & cr_warn_level)) {
                cwarn( "Converted [CR+LF] to [LF]"  /* _W1_ _W2_    */
                        , NULL, 0L, NULL, processingData);
                cr_converted = TRUE;
            }
        }
        if (processingData->standard) {
            if (processingData->option_flags.trig)
                converted = cnv_trigraph( ptr, processingData);
            if (processingData->mcpp_mode == POST_STD && processingData->option_flags.dig)
                converted += cnv_digraph( ptr, processingData);
            if (converted)
                len = strlen( ptr);
            /* Translation phase 2  */
            len -= 2;
            if (len >= 0) {
                if ((*(ptr + len) == '\\') && ! last_is_mbchar( ptr, len, processingData)) {
                            /* <backslash><newline> (not MBCHAR)    */
                    ptr = processingData->infile->bptr += len;  /* Splice the lines */
                    processingData->wrong_line = TRUE;
                    if ((processingData->mcpp_debug & MACRO_CALL) && processingData->compiling) {
                                    /* Save location informations   */
                        if (cat_line == 0)      /* First line of catenation */
                            processingData->supportProcessingData.bsl_cat_line.start_line = processingData->src_line;
                        if (cat_line < MAX_CAT_LINE)
                                    /* Record the catenated length  */
                            processingData->supportProcessingData.bsl_cat_line.len[ ++cat_line]
                                    = strlen( processingData->infile->buffer) - 2;
                        /* Else ignore  */
                    }
                    continue;
                }
            }
#if NBUFF-2 > SLEN90MIN
            if (ptr - processingData->infile->buffer + len + 2 > processingData->std_limits.str_len + 1
                    && (processingData->warn_level & 4))    /* +1 for '\n'          */
            cwarn( "Logical source line longer than %.0s%ld bytes"  /* _W4_ */
                        , NULL, processingData->std_limits.str_len, NULL, processingData);
#endif
        }
        if ((processingData->mcpp_debug & MACRO_CALL) && processingData->compiling) {
            if (cat_line && cat_line < MAX_CAT_LINE) {
                processingData->supportProcessingData.bsl_cat_line.len[ ++cat_line] = strlen( processingData->infile->buffer) - 1;
                                /* Catenated length: '-1' for '\n'  */
                processingData->supportProcessingData.bsl_cat_line.last_line = processingData->src_line;
            }
        }
        return  processingData->infile->bptr = processingData->infile->buffer;      /* Logical line */
    }

    /* End of a (possibly included) source file */
    //if (ferror( infile->fp))		// Anima ADD
	if (mferror(processingData->infile->mf))		// Anima ADD
        cfatal( "File read error", NULL, 0L, NULL, processingData);         /* _F_  */
    if ((ptr = at_eof( in_comment, processingData)) != NULL)        /* Check at end of file */
        return  ptr;                        /* Partial line supplemented    */
    if (processingData->option_flags.z) {
        processingData->no_output--;                        /* End of included file */
        processingData->keep_comments = processingData->option_flags.c && processingData->compiling && !processingData->no_output;
    }
    return  NULL;
}

#define TRIOFFSET       10

int     cnv_trigraph(
    char *      in, processing_data_t* processingData
)
/*
 * Perform in-place trigraph replacement on a physical line.  This was added
 * to the C90.  In an input text line, the sequence ??[something] is
 * transformed to a character (which might not appear on the input keyboard).
 */
{
    const char * const  tritext = "=(/)'<!>-\0#[\\]^{|}~";
    /*                             ^          ^
     *                             +----------+
     *                             this becomes this
     */
    int     count = 0;
    const char *    tp;

    while ((in = strchr( in, '?')) != NULL) {
        if (*++in != '?')
            continue;
        while (*++in == '?')
            ;
        if ((tp = strchr( tritext, *in)) == NULL)
            continue;
        *(in - 2) = *(tp + TRIOFFSET);
        in--;
        memmove( in, in + 2, strlen( in + 1));
        count++;
    }

    if (count && (processingData->warn_level & 16))
        cwarn( "%.0s%ld trigraph(s) converted"          /* _W16_    */
                , NULL, (long) count, NULL, processingData);
    return  count;
}

int     cnv_digraph(
    char *      in, processing_data_t* processingData
)
/*
 * Perform in-place digraph replacement on a physical line.
 * Called only in POST_STD mode.
 */
{
    int     count = 0;
    int     i;
    int     c1, c2;

    while ((i = strcspn( in, "%:<")), (c1 = *(in + i)) != '\0') {
        in += i + 1;
        c2 = *in;
        switch (c1) {
        case '%'    :
            switch (c2) {
            case ':'    :   *(in - 1) = '#';    break;
            case '>'    :   *(in - 1) = '}';    break;
            default     :   continue;
            }
            break;
        case ':'    :
            switch (c2) {
            case '>'    :   *(in - 1) = ']';    break;
            default     :   continue;
            }
            break;
        case '<'    :
            switch (c2) {
            case '%'    :   *(in - 1) = '{';    break;
            case ':'    :   *(in - 1) = '[';    break;
            default     :   continue;
            }
            break;
        }
        memmove( in, in + 1, strlen( in));
        count++;
    }

    if (count && (processingData->warn_level & 16))
        cwarn( "%.0s%ld digraph(s) converted"           /* _W16_    */
                , NULL, (long) count, NULL, processingData);
    return  count;
}

static char *   at_eof(
    int     in_comment, processing_data_t* processingData
)
/*
 * Check the partial line, unterminated comment, unbalanced #if block,
 * uncompleted macro call at end of a file or at end of input.
 * Supplement the line terminator, if possible.
 * Return the supplemented line or NULL on unrecoverable error.
 */
{
    const char * const  format
            = "End of %s with %.0ld%s";                 /* _E_ _W1_ */
    const char * const  unterm_if_format
= "End of %s within #if (#ifdef) section started at line %ld";  /* _E_ _W1_ */
    const char * const  unterm_macro_format
            = "End of %s within macro call started at line %ld";/* _E_ _W1_ */
    const char * const  input
            = processingData->infile->parent ? "file" : "input";        /* _E_ _W1_ */
    const char * const  no_newline
            = "no newline, supplemented newline";       /* _W1_     */
    const char * const  unterm_com
            = "unterminated comment, terminated the comment";   /* _W1_     */
    const char * const  backsl = "\\, deleted the \\";  /* _W1_     */
    const char * const  unterm_asm_format
= "End of %s with unterminated #asm block started at line %ld"; /* _E_ _W1_ */
    size_t  len;
    char *  cp;

    cp = processingData->infile->buffer;
    len = strlen( cp);
    if (len && *(cp += (len - 1)) != '\n') {
        *++cp = '\n';                       /* Supplement <newline> */
        *++cp = EOS;
        if (processingData->mcpp_mode != OLD_PREP && (processingData->warn_level & 1))
            cwarn( format, input, 0L, no_newline, processingData);
        return  processingData->infile->bptr = processingData->infile->buffer;
    }
    if (processingData->standard && processingData->infile->buffer < processingData->infile->bptr) {
                            /* No line after <backslash><newline>   */
        cp = processingData->infile->bptr;
        *cp++ = '\n';                       /* Delete the \\        */
        *cp = EOS;
        if (processingData->warn_level & 1)
            cwarn( format, input, 0L, backsl, processingData);
        return  processingData->infile->bptr = processingData->infile->buffer;
    }
    if (in_comment) {               /* End of file within a comment */
        if (processingData->mcpp_mode != OLD_PREP && (processingData->warn_level & 1))
            cwarn( format, input, 0L, unterm_com, processingData);
        /* The partial comment line has been already read by        */
        /* read_a_comment(), so supplement the  next line.          */
        strcpy( processingData->infile->buffer, "*/\n");
        return  processingData->infile->bptr = processingData->infile->buffer;
    }

    if (processingData->infile->initif < processingData->ifptr) {
        IFINFO *    ifp = processingData->infile->initif + 1;
        if (processingData->standard) {
            cerror( unterm_if_format, input, ifp->ifline, NULL, processingData);
            processingData->ifptr = processingData->infile->initif;         /* Clear information of */
            processingData->compiling = processingData->ifptr->stat;        /*   erroneous grouping */
        } else if (processingData->mcpp_mode == KR && (processingData->warn_level & 1)) {
            cwarn( unterm_if_format, input, ifp->ifline, NULL, processingData);
        }
    }

    if (processingData->macro_line != 0 && processingData->macro_line != MACRO_ERROR
            && ((processingData->mcpp_mode == STD && processingData->in_getarg) || ! processingData->standard)) {
        if (processingData->standard) {
            cerror( unterm_macro_format, input, processingData->macro_line, NULL, processingData);
            processingData->macro_line = MACRO_ERROR;
        } else if (processingData->warn_level & 1) {
            cwarn( unterm_macro_format, input, processingData->macro_line, NULL, processingData);
        }
    }

    if (processingData->in_asm && processingData->mcpp_mode == KR && (processingData->warn_level & 1))
        cwarn( unterm_asm_format, input, processingData->in_asm, NULL, processingData);

    return  NULL;
}

void    unget_ch(processing_data_t* processingData)
/*
 * Back the pointer to reread the last character.  Fatal error (code bug)
 * if we back too far.  unget_ch() may be called, without problems, at end of
 * file.  Only one character may be ungotten.  If you need to unget more,
 * call unget_string().
 */
{
    if (processingData->supportProcessingData.in_token) {
        processingData->infile->bptr--;
        return;
    }

    if (processingData->infile != NULL) {
        if (processingData->mcpp_mode == POST_STD && processingData->infile->mf) {		// Anima ADD
            switch (processingData->insert_sep) {
            case INSERTED_SEP:  /* Have just read an inserted separator */
                processingData->insert_sep = INSERT_SEP;
                return;
            case INSERT_SEP:
                cfatal( "Bug: unget_ch() just after scan_token()"   /* _F_  */
                        , NULL, 0L, NULL, processingData);
                break;
            default:
                break;
            }
        }
        --processingData->infile->bptr;
        if (processingData->infile->bptr < processingData->infile->buffer)      /* Shouldn't happen */
            cfatal( "Bug: Too much pushback", NULL, 0L, NULL, processingData);      /* _F_  */
    }

    if (processingData->mcpp_debug & GETC)
        dump_unget( "after unget", processingData);
}

FILEINFO *  unget_string(
    const char *    text,               /* Text to unget            */
    const char *    name,               /* Name of the macro, if any*/
    processing_data_t* processingData
)
/*
 * Push a string back on the input stream.  This is done by treating
 * the text as if it were a macro or a file.
 */
{
    FILEINFO *      file;
    size_t          size;

    if (text)
        size = strlen( text) + 1;
    else
        size = 1;
    file = get_file( name, NULL, NULL, size, FALSE, processingData);
    if (text)
        memcpy( file->buffer, text, size);
    else
        *file->buffer = EOS;
    return  file;
}

char *  save_string(
    const char *      text
)
/*
 * Store a string into free memory.
 */
{
    char *      result;
    size_t      size;

    size = strlen( text) + 1;
    result = xmalloc( size);
    memcpy( result, text, size);
    return  result;
}

FILEINFO *  get_file(
    const char *    name,                   /* File or macro name   */
    const char *    src_dir,                /* Source file directory*/
    const char *    fullname,               /* Full path list       */
    size_t      bufsize,                    /* Line buffer size     */
    int         include_opt,         /* Specified by -include opt (for GCC)  */
    processing_data_t* processingData
)
/*
 * Common FILEINFO buffer initialization for a new file or macro.
 */
{
    FILEINFO *  file;

    file = (FILEINFO *) xmalloc( sizeof (FILEINFO));
    file->buffer = xmalloc( bufsize);
    file->bptr = file->buffer;              /* Initialize line ptr  */
    file->buffer[ 0] = EOS;                 /* Force first read     */
    file->line = 0L;                        /* (Not used just yet)  */
    file->mf = NULL;                        /* No file yet          */		// Anima ADD
    file->pos = 0L;                         /* No pos to remember   */
    file->parent = processingData->infile;                  /* Chain files together */
    file->initif = processingData->ifptr;                   /* Initial ifstack      */
    file->include_opt = include_opt;        /* Specified by -include*/
    file->dirp = NULL;                      /* No include dir yet   */
    file->real_fname = name;                /* Save file/macro name */
    file->full_fname = fullname;            /* Full path list       */
    if (name) {
        file->filename = xmalloc( strlen( name) + 1);
        strcpy( file->filename, name);      /* Copy for #line       */
    } else {
        file->filename = NULL;
    }
    if (src_dir) {
        file->src_dir = xmalloc( strlen( src_dir) + 1);
        strcpy( file->src_dir, src_dir);
    } else {
        file->src_dir = NULL;
    }
#if MCPP_LIB
    file->last_fputc = mcpp_lib_fputc;
    file->last_fputs = mcpp_lib_fputs;
    file->last_fprintf = mcpp_lib_fprintf;
#endif
    if (processingData->infile != NULL) {                   /* If #include file     */
        processingData->infile->line = processingData->src_line;            /* Save current line    */
#if MCPP_LIB
        infile->last_fputc = processingData->mcpp_fputc;
        infile->last_fputs = processingData->mcpp_fputs;
        infile->last_fprintf = processingData->mcpp_fprintf;
#endif
    }
    processingData->infile = file;                          /* New current file     */

    return  file;                           /* All done.            */
}

static const char * const   out_of_memory
    = "Out of memory (required size is %.0s0x%lx bytes)";   /* _F_  */

char *
(xmalloc)(
    size_t      size
)
/*
 * Get a block of free memory.
 */
{
    char *      result;

    if ((result = (char *) malloc( size)) == NULL) {
        // ANIMA ADD if (mcpp_debug & MEMORY)
        // ANIMA ADD     print_heap();
       // ANIMA ADD cfatal( out_of_memory, NULL, (long) size, NULL);
    }
    return  result;
}

char *  (xrealloc)(
    char *      ptr,
    size_t      size
)
/*
 * Reallocate malloc()ed memory.
 */
{
    char *      result;

    if ((result = (char *) realloc( ptr, size)) == NULL && size != 0) {
        /* 'size != 0' is necessary to cope with some               */
        /*   implementation of realloc( ptr, 0) which returns NULL. */
        // ANIMA ADD if (mcpp_debug & MEMORY)
        // ANIMA ADD     print_heap();
        // ANIMA ADD cfatal( out_of_memory, NULL, (long) size, NULL);
    }
    return  result;
}

LINE_COL *  get_src_location(
    LINE_COL *  p_line_col,          /* Line and column on phase 4   */
    processing_data_t* processingData
)
/*
 * Convert line-column datum of just after translation phase 3 into that of
 * phase 2, tracing back line splicing by a comment and <backslash><newline>.
 * Note: This conversion does not give correct datum on a line catenated by
 * both of <backslash><newline> and line-crossing-comment at the same time.
 *
 * com_cat_line and bsl_cat_line have data only on last catenated line.
 * com_cat_line.len[] and bsl_cat_line.len[] have the length of catenated
 * line, and len[ 0] is always 0, followed by len[ 1], len[ 2], ..., as
 * accumulated length of successively catenated lines.
 */
{
    long        line;
    size_t      col;
    size_t *    cols;
    CAT_LINE *  l_col_p;
    int         i;

    line = p_line_col->line;
    col = p_line_col->col;

    for (i = 0; i <= 1; i++) {
        l_col_p = i ? & processingData->supportProcessingData.bsl_cat_line : & processingData->supportProcessingData.com_cat_line;
        if (l_col_p->last_line != line)
            continue;
        /* Else just catenated line */
        cols = l_col_p->len + 1;
        while (*cols < col)
            cols++;
        if (col <= *cols) {
            cols--;
            col -= *cols;
        }
        line = l_col_p->start_line + (cols - l_col_p->len);
    }

    p_line_col->line = line;
    p_line_col->col = col + 1;
                    /* col internally start at 0, output start at 1 */

    return  p_line_col;
}

static void put_line(
    char *  out,
    FILE *  fp,
    processing_data_t* processingData
)
/*
 * Put out a logical source line.
 * This routine is called only in OLD_PREP mode.
 */
{
    int     c;

    while ((c = *out++) != EOS) {
        if (c != COM_SEP)           /* Skip 0-length comment        */
            processingData->mcpp_fputc( c, FP2DEST( fp, processingData), processingData);
    }
}

static void do_msg(
    const char *    severity,       /* "fatal", "error", "warning"  */
    const char *    format,         /* Format for the error message */
    const char *    arg1,           /* String arg. for the message  */
    long            arg2,           /* Integer argument             */
    const char *    arg3,           /* Second string argument       */
    processing_data_t* processingData
)
/*
 * Print filenames, macro names, line numbers and error messages.
 * Also print macro definitions on macro expansion problems.
 */
{
    FILEINFO *  file;
    DEFBUF *    defp;
    int         i;
    size_t      slen;
    const char *    arg_s[ 2];
    char *      arg_t[ 2];
    char *      tp;
    const char *    sp;
    int         c;
    int         ind;

    fflush( processingData->fp_out);                /* Synchronize output and diagnostics   */
    arg_s[ 0] = arg1;  arg_s[ 1] = arg3;

    for (i = 0; i < 2; i++) {   /* Convert special characters to visible    */
        sp = arg_s[ i];
        if (sp != NULL)
            slen = strlen( sp) + 1;
        else
            slen = 1;
        tp = arg_t[ i] = (char *) malloc( slen);
            /* Don't use xmalloc() so as not to cause infinite recursion    */
        if (sp == NULL || *sp == EOS) {
            *tp = EOS;
            continue;
        }

        while ((c = *sp++) != EOS) {
            switch (c) {
            case TOK_SEP:
                if (processingData->mcpp_mode == OLD_PREP)      /* COM_SEP          */
                    break;              /* Skip magic characters    */
                /* Else fall through    */
            case RT_END:
            case CAT:
            case ST_QUOTE:
            case DEF_MAGIC:
                if (! processingData->standard)
                    *tp++ = ' ';
                break;                  /* Skip the magic characters*/
            case IN_SRC:
                if (! processingData->standard)
                    *tp++ = ' ';
                if ((processingData->mcpp_debug & MACRO_CALL) && ! processingData->in_directive)
                    sp += 2;            /* Skip two more bytes      */
                break;
            case MAC_INF:
                if (processingData->mcpp_mode != STD) {
                    *tp++ = ' ';
                    /* Illegal control character, convert to a space*/
                } else {
                    switch (*sp++) {    /* Skip the magic characters*/
                    case MAC_ARG_START  :
                        sp++;
                        /* Fall through */
                    case MAC_CALL_START :
                        sp += 2;
                        break;
                    case MAC_ARG_END    :
                        if (! processingData->option_flags.v)
                            break;
                        else
                            sp++;
                            /* Fall through */
                    case MAC_CALL_END   :
                        if (processingData->option_flags.v)
                            sp += 2;
                        break;
                    }
                }
                break;
            case '\n':
                *tp++ = ' ';            /* Convert '\n' to a space  */
                break;
            default:
                *tp++ = c;
                break;
            }
        }

        if (*(sp - 2) == '\n')
            tp--;
        *tp = EOS;
    }

    /* Print source location and diagnostic */
    file = processingData->infile;
    while (file != NULL && (file->mf == NULL || file->mf == (MFILE *)-1))		// Anima ADD
        file = file->parent;                        /* Skip macro   */
    if (file != NULL) {
        file->line = processingData->src_line;
        processingData->mcpp_fprintf( ERR, processingData, "%s:%ld: %s: ", processingData->cur_fullname, processingData->src_line, severity);
    }
    processingData->mcpp_fprintf( ERR, processingData, format, arg_t[ 0], arg2, arg_t[ 1]);
    processingData->mcpp_fputc( '\n', ERR, processingData);
    if (processingData->option_flags.no_source_line)
        goto  free_arg;

    /* Print source line, includers and expanding macros    */
    file = processingData->infile;
    if (file != NULL && file->mf != NULL) {										// Anima ADD
        if (processingData->mcpp_mode == OLD_PREP) {
            processingData->mcpp_fputs( "    ", ERR, processingData);
            put_line( file->buffer, processingData->fp_err, processingData);
        } else {
            processingData->mcpp_fprintf( ERR, processingData, "    %s", file->buffer);
                                            /* Current source line  */
        }
        file = file->parent;
    }
    while (file != NULL) {                  /* Print #includes, too */
        if (file->mf == NULL) {             /* Macro                */			// Anima ADD
            if (file->filename) {
                defp = look_id( file->filename, processingData);
                if ((defp->nargs > DEF_NOARGS_STANDARD)
                    && ! (file->parent && file->parent->filename
                        && str_eq( file->filename, file->parent->filename)))
                        /* If the name is not duplicate of parent   */
                    dump_a_def( "    macro", defp, FALSE, TRUE, processingData->fp_err, processingData);
            }
        } else {                            /* Source file          */
            if (file->buffer[ 0] == '\0')
                strcpy( file->buffer, "\n");
            if (processingData->mcpp_mode != OLD_PREP) {
                processingData->mcpp_fprintf( ERR, processingData, "    from %s: %ld:    %s",
                    file->line ? file->full_fname       /* Full-path-list   */
                        : "<stdin>",        /* Included by -include */
                    file->line,             /* Current line number  */
                    file->buffer);          /* The source line      */
            } else {
                processingData->mcpp_fprintf( ERR, processingData, "    from %s: %ld:    ", file->full_fname
                        , file->line);
                put_line( file->buffer, processingData->fp_err, processingData);
            }
        }
        file = file->parent;
    }

    if (! processingData->macro_name)
        goto  free_arg;
    /* Additional information of macro definitions  */
    processingData->supportProcessingData.expanding_macro[ 0].name = processingData->macro_name;
    for (ind = 0; ind <= processingData->supportProcessingData.exp_mac_ind; ind++) {
        int         ind_done;

        for (ind_done = 0; ind_done < ind; ind_done++)
            if (str_eq( processingData->supportProcessingData.expanding_macro[ ind].name
                    , processingData->supportProcessingData.expanding_macro[ ind_done].name))
                break;                      /* Already reported     */
        if (ind_done < ind)
            continue;
        for (file = processingData->infile; file; file = file->parent)
            if (file->mf == NULL && file->filename								// Anima ADD
                    && str_eq( processingData->supportProcessingData.expanding_macro[ ind].name, file->filename))
                break;                      /* Already reported     */
        if (file)
            continue;
        if ((defp = look_id( processingData->supportProcessingData.expanding_macro[ ind].name, processingData)) != NULL) {
            if (defp->nargs <= DEF_NOARGS_STANDARD)
                continue;                   /* Standard predefined  */
            dump_a_def( "    macro", defp, FALSE, TRUE, processingData->fp_err, processingData);
            /* Macro already read over  */
        }
    }

free_arg:
    for (i = 0; i < 2; i++)
        free( arg_t[ i]);
}

void    cfatal(
    const char *    format,
    const char *    arg1,
    long    arg2,
    const char *    arg3,
    processing_data_t* processingData
)
/*
 * A real disaster.
 */
{
    do_msg( "fatal error", format, arg1, arg2, arg3, processingData);
    longjmp( processingData->error_exit, -1);
}

void    cerror(
    const char *    format,
    const char *    arg1,
    long    arg2,
    const char *    arg3,
    processing_data_t* processingData
)
/*
 * Print a error message.
 */
{
    do_msg( "error", format, arg1, arg2, arg3, processingData);
    processingData->errors++;
}

void    cwarn(
    const char *    format,
    const char *    arg1,
    long    arg2,
    const char *    arg3,
    processing_data_t* processingData
)
/*
 * Maybe an error.
 */
{
    do_msg( "warning", format, arg1, arg2, arg3, processingData);
}

void    dump_string(
    const char *    why,
    const char *    text,
    processing_data_t* processingData
)
/*
 * Dump text readably.
 * Bug: macro argument number may be putout as a control character or any
 * other character, just after MAC_PARM has been read away.
 */
{
    const char *    cp;
    const char *    chr;
    int     c, c1, c2;

    if (why != NULL)
        processingData->mcpp_fprintf( DBG, processingData, " (%s)", why);
    processingData->mcpp_fputs( " => ", DBG, processingData);

    if (text == NULL) {
        processingData->mcpp_fputs( "NULL", DBG, processingData);
        return;
    }

    for (cp = text; (c = *cp++ & UCHARMAX) != EOS; ) {
        chr = NULL;

        switch (c) {
        case MAC_PARM:
            c = *cp++ & UCHARMAX;       /* Macro parameter number   */
            processingData->mcpp_fprintf(DBG, processingData, "<%d>", c);
            break;
        case MAC_INF:
            if (! (processingData->mcpp_mode == STD && (processingData->mcpp_debug & MACRO_CALL)))
                goto  no_magic;
            /* Macro informations inserted by -K option */
            c2 = *cp++ & UCHARMAX;
            if (processingData->option_flags.v || c2 == MAC_CALL_START
                    || c2 == MAC_ARG_START) {
                c = ((*cp++ & UCHARMAX) - 1) * UCHARMAX;
                c += (*cp++ & UCHARMAX) - 1;
            }
            switch (c2) {
            case MAC_CALL_START:
                processingData->mcpp_fprintf( DBG, processingData, "<MAC%d>", c);
                break;
            case MAC_CALL_END:
                if (processingData->option_flags.v)
                    processingData->mcpp_fprintf( DBG, processingData, "<MAC_END%d>", c);
                else
                    chr = "<MAC_END>";
                break;
            case MAC_ARG_START:
                c1 = *cp++ & UCHARMAX;
                processingData->mcpp_fprintf( DBG, processingData, "<MAC%d:ARG%d>", c, c1 - 1);
                break;
            case MAC_ARG_END:
                if (processingData->option_flags.v) {
                    c1 = *cp++ & UCHARMAX;
                    processingData->mcpp_fprintf( DBG, processingData, "<ARG_END%d-%d>", c, c1 - 1);
                } else {
                    chr = "<ARG_END>";
                }
                break;
            }
            break;
        case DEF_MAGIC:
            if (processingData->standard) {
                chr = "<MAGIC>";
                break;
            }       /* Else fall through    */
        case CAT:
            if (processingData->standard) {
                chr = "##";
                break;
            }       /* Else fall through    */
        case ST_QUOTE:
            if (processingData->standard) {
                chr = "#";
                break;
            }       /* Else fall through    */
        case RT_END:
            if (processingData->standard) {
                chr = "<RT_END>";
                break;
            }       /* Else fall through    */
        case IN_SRC:
            if (processingData->standard) {
                if ((processingData->mcpp_debug & MACRO_CALL) && ! processingData->in_directive) {
                    int     num;
                    num = ((*cp++ & UCHARMAX) - 1) * UCHARMAX;
                    num += (*cp++ & UCHARMAX) - 1;
                    processingData->mcpp_fprintf( DBG, processingData, "<SRC%d>", num);
                } else {
                    chr = "<SRC>";
                }
            } else {                        /* Control character    */
                processingData->mcpp_fprintf( DBG, processingData, "<^%c>", c + '@');
            }
            break;
        case TOK_SEP:
            if (processingData->mcpp_mode == STD) {
                chr = "<TSEP>";
                break;
            } else if (processingData->mcpp_mode == OLD_PREP) {     /* COM_SEP      */
                chr = "<CSEP>";
                break;
            }       /* Else fall through    */
        default:
no_magic:
            if (c < ' ')
                processingData->mcpp_fprintf( DBG, processingData, "<^%c>", c + '@');
            else
                processingData->mcpp_fputc( c, DBG, processingData);
            break;
        }

        if (chr)
            processingData->mcpp_fputs( chr, DBG, processingData);
    }

    processingData->mcpp_fputc( '\n', DBG, processingData);
}

void    dump_unget(
    const char *    why,
    processing_data_t* processingData
)
/*
 * Dump all ungotten junk (pending macros and current input lines).
 */
{
    const FILEINFO *    file;

    processingData->mcpp_fputs( "dump of pending input text", DBG, processingData);
    if (why != NULL) {
        processingData->mcpp_fputs( "-- ", DBG, processingData);
        processingData->mcpp_fputs( why, DBG, processingData);
    }
    processingData->mcpp_fputc( '\n', DBG, processingData);

    for (file = processingData->infile; file != NULL; file = file->parent)
        dump_string( file->real_fname ? file->real_fname
                : file->filename ? file->filename : "NULL", file->bptr, processingData);
}

static void dump_token(
    int     token_type,
    const char *    cp,                              /* Token        */
    processing_data_t* processingData
)
/*
 * Dump a token.
 */
{
    static const char * const   t_type[]
            = { "NAM", "NUM", "STR", "WSTR", "CHR", "WCHR", "OPE", "SPE"
            , "SEP", };

    processingData->mcpp_fputs( "token", DBG, processingData);
    dump_string( t_type[ token_type - NAM], cp, processingData);
}

