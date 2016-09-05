/* n_12.t:  Integer preprocessing number token and type of #if expression.  */

#include    <limits.h>

/* 12.1:    Type long.  */
#if     LONG_MAX <= LONG_MIN
    Bad evaluation of long.
#endif
#if     LONG_MAX <= 1073741823  /* 0x3FFFFFFF   */
    Bad evaluation of long.
#endif

/* 12.2:    Type unsigned long. */
#if     ULONG_MAX / 2 < LONG_MAX
    Bad evaluation of unsigned long.
#endif

/* 12.3:    Octal number.   */
#if     0177777 != 65535
    Bad evaluation of octal number.
#endif

/* 12.4:    Hexadecimal number. */
#if     0Xffff != 65535 || 0xFfFf != 65535
    Bad evaluation of hexadecimal number.
#endif

/* 12.5:    Suffix 'L' or 'l'.  */
#if     0L != 0 || 0l != 0
    Bad evaluation of 'L' suffix.
#endif

/* 12.6:    Suffix 'U' or 'u'.  */
#if     1U != 1 || 1u != 1
    Bad evaluation of 'U' suffix.
#endif

/* 12.7:    Negative integer.   */
#if     0 <= -1
    Bad evaluation of negative number.
#endif

