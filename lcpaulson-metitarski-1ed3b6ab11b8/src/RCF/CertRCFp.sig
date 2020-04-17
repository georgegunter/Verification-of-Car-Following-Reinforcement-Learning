(* ======================================================================== *)
(*               Proof Procedures for Certified RCF Judgments               *)
(*                      - Derived proof procedures -                        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature CertRCFp =
sig

(* A complete univariate RCF decision procedure using the proof system
   defined in the CertRCF kernel. Given an implicitly existential RCF
   formula Phi(x), we work to decide its status, returning either

   (Fml Phi(x)) -|- True (w : RealAlg.real_alg)

    or

   (Fml Phi(x)) -|- False. *)

val univ_prove : Formula.formula -> CertRCFk.thm;

(* A complete univariate RCF decision procedure for refuting an
   implicitly existential RCF conjecture. We attempt to refute the
   given RCF formula, returning true if we're successful, false
   otherwise. 

   This is the simplest interface through which MetiTarski will access
   this certified RCF module.  

   Note that this throws away the real algebraic witnesses we compute
   when an input formula is satisfiable. We'll want to later retrieve
   these for, e.g., an extended real algebraic version of the model-
   sharing framework. *)

val univ_refute : Formula.formula -> bool;

(* A version of univ_prove supporting quantified formulas *)

val univ_prove_q : Formula.formula -> bool

end
