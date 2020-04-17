(* ======================================================================== *)
(* Core Arithmetical Machinery for Generalised (Non-Compact) Real Intervals *)
(* with interval endpoint values taken over Q_ext = (Q union {-inf, +inf}). *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature IntvlsQ = 
sig

(* Type for ICP return values: 

   Either

    (i) ICP made no progress on the problem (no term in the formula
    could be bound within any interval other than ]-inf, +inf[), or
 
    (ii) ICP made progress but did not narrow any term to be within an
    empty interval, or

    (iii) ICP did narrow some term to be within an empty interval, thus
    refuting the satisfiability of the formula upon which ICP was
    applied. *)

datatype icp_r = ICP_NO_PROGRESS | ICP_PROGRESS | ICP_EMPTY;

(* Run ICP upon ``ICP friendly'' formulas, returning one of the
   constructors of type icp_r.  Roughly, a formula is ``ICP friendly''
   iff it can be represented as a conjunction of RCF atoms.  If the
   formula is not ICP friendly, then we return ICP_NO_PROGRESS. 

   In addition to the formula, an integer argument specifying an ICP
   contraction count limit must be given. *)

val icp_on_fml : Formula.formula * int -> icp_r;

end;
