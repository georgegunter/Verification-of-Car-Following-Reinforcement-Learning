/*======================================================================
<macro>               t <- ISOBJECT(a)

Test for object.

Inputs
  a  : a Word.

Outputs
  t  :  a BETA-digit.
        t = 1 if a is an object,
        t = 0 otherwise.
======================================================================*/
#ifndef NO_SACLIB_MACROS
#define NO_SACLIB_MACROS
#endif
#include "saclib.h"

Word ISOBJECT(a)
       Word a;
{
 return(ISATOM(a) || ISLIST(a));
}
