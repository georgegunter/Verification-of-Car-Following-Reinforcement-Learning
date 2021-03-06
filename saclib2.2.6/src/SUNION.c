/*======================================================================
                      C <- SUNION(A,B)

Set union.

Inputs
  A, B : ordered lists of of BETA-integers.
         (A, B represent sets of BETA-integers.)

Outputs
  C    : the ordered list representing the union of the sets A and B.
======================================================================*/
#include "saclib.h"

Word SUNION(A,B)
       Word A,B;
{
       Word Ap,Bp,C,Cp,a,b;
       /* hide Ap,Bp,C,a,b; */

Step1: /* Compute. */
       Cp = NIL;
       Ap = A;
       Bp = B;
       while (Ap != NIL && Bp != NIL)
         {
         a = FIRST(Ap);
         b = FIRST(Bp);
         if (a == b)
           {
           Cp = COMP(a,Cp);
           Ap = RED(Ap);
           Bp = RED(Bp);
           }
         else
           if (a < b)
             {
             Cp = COMP(a,Cp);
             Ap = RED(Ap);
             }
           else
             {
             Cp = COMP(b,Cp);
             Bp = RED(Bp);
             }
         }
       if (Ap == NIL)
         Ap = Bp;
       if (Cp == NIL)
         C = Ap;
       else
         {
         C = INV(Cp);
         SRED(Cp,Ap);
         }

Return: /* Prepare for return. */
       return(C);
}
