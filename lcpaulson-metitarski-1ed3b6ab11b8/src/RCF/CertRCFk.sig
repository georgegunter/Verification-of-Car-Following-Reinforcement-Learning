(* ======================================================================== *)
(*               Proof Procedures for Certified RCF Judgments               *)
(*                       - An LCF-style kernel -                            *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

signature CertRCFk =
sig

datatype fml = 
	 Fml of Formula.formula 
       | Disj of Formula.formula * RealAlg.real_alg list
       | True of RealAlg.real_alg
       | False;

(* Abstract type of theorems *)

type thm;

(* Accessors *)

val thm_l : thm -> fml;
val thm_r : thm -> fml;

(* An exception for an invalid application of an inference rule *)

exception Invalid_inference of string;

(* An exception for the finding of a satisfying RCF witness during the
   failed application of an inference rule. This allows proof
   strategies (whose aim it is to refute an Exists RCF formula) to
   `short-circuit' their operation when a satisfying witness has
   `accidentally' been found. *)

exception Witness of RealAlg.real_alg;

(* Primitive inference rules, documented in CertRCFk.sml *)

val ra : fml -> thm;

val rd : thm -> thm;

val re : thm -> thm;

val rt : thm -> thm;

val rf : thm -> thm;

end

