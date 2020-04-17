(* ======================================================================== *)
(*               Proof Procedures for Certified RCF Judgments               *)
(*                       - An LCF-style kernel -                            *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure CertRCFk : CertRCFk =
struct

open Algebra;
open MTAlgebra;
open Sturm;
open Resultant;
open RealAlg;

(* ========================================================================
      A simple LCF-style real-algebraic proof system for univariate RCF 
   ========================================================================

   * Our formula language consists of four types of formulas:
     
     - Fml of Formula.formula 

        A univariate (implicitly existentially quantified) RCF
        formula.

     - Disj of Formula.formula * RealAlg.real_alg list 

        A quantifier-free formula and a list of real algebraic
        numbers.  The intended interpretation of Disj (Phi, Alpha) is:
          
            \/_{alpha in Alpha) Phi(alpha).

     - True of RealAlg.real_alg 

        A terminal judgement of truth, as witnessed by a real
        algebraic number.

     - False
 
        A terminal judgment of falsity.

   ========================================================================   

   * Our theorems are equivalences of the form

                  f  -|-  g 

     with f, g : formula.  The infix constructor `-|-' is meant to
     connote `|- and -|,' as in a meta-level `iff.'

   ========================================================================

   * Our inference rules (named RA, RD, RE, RT, RF):


     RA ------------------------------------
          Fml (Phi(x))  -|-  Fml (Phi(x)) 



                    Fml (Phi(x))  -|-  Fml (Psi(x))  
     RD ----------------------------------------------------------   
          Fml (Phi(x))  -|-  Disj (Psi, [alpha_1, ..., alpha_k])          
                                                     

            s.t. [alpha_1, ..., alpha_k] is a complete set of real
                 algebraic sample points derived from a CAD of R^1
                 induced by the polynomials of Psi.



          Fml (Phi(x))  -|-  Disj (Psi, [alpha_1, ..., alpha_k]) 
     RE ----------------------------------------------------------
          Fml (Phi(x))  -|-  Disj (Psi, [alpha_2, ..., alpha_k])


            s.t. Psi(alpha_1) is false.



          Fml (Phi(x))  -|-  Disj (Psi, [alpha_1, ..., alpha_k]) 
     RT ----------------------------------------------------------
                     Fml (Phi(x))  -|-  True (alpha_1)


            s.t. Psi(alpha_1) is true.
          


                   Fml (Phi(x))  -|-  Disj (Psi, []) 
     RF         -------------------------------------
                      Fml (Phi(x))  -|-  False

   ========================================================================

     Note that all computations performed (including, e.g., the
     isolation of a complete set of CAD sample points, evaluation of RCF
     formulas upon real algebraic sample points, etc.) are done
     internally by MetiTarski, without the use of any external decision
     methods. Thus, we can easily extend our proof system with more
     constructors and inference rules in order to `trace' the internal
     algebraic computations explicitly within a generated proof object.

     We envision this proof system being extended over time in order to
     accommodate the needs of an Isabelle/HOL effort to reconstruct
     MetiTarski proofs in a fully expansive manner.

   ======================================================================== *)

datatype fml = 
	 Fml of Formula.formula 
       | Disj of Formula.formula * RealAlg.real_alg list
       | True of RealAlg.real_alg
       | False;

(* Our theorems are equivalences; `-|-' as in `|- and -|' *)
 
datatype thm = -|- of fml * fml;                  infix -|-;

fun thm_l (fm -|- _)  = fm;
fun thm_r (_ -|- fm') = fm';

(* An exception for an invalid application of an inference rule *)

exception Invalid_inference of string;

(* An exception for the finding of a satisfying RCF witness during the
   failed application of an inference rule. This allows proof
   strategies (whose aim it is to refute an Exists RCF formula) to
   `short-circuit' their operation when a satisfying witness has
   `accidentally' been found. *)

exception Witness of RealAlg.real_alg;

(* Simple tracing of kernel inference rule applications *)

fun trace_i x r s =
    (print ("[CertRCF:kernel:" ^ r ^ "] " ^ s ^ ".\n");
     x);

(* ======================================================================== *)
(*  Begin primitive thm constructors                                        *)
(* ======================================================================== *)

(* Inference rule RA (`RCF Axiom') *)

fun ra (Fml fm) = 
    trace_i (Fml fm -|- Fml fm) 
	    "ra"
	    ("Introduced trivial equivalence (Fml fm) -|- (Fml fm)\n  where fm = " 
		 ^ (Formula.toString fm))
  | ra _ = raise Invalid_inference "ra";

(* Inference rule RD (`RCF Disj') using algebraic decomposition *)

fun rd (Fml fm -|- Fml fm') =
    let val vh = mk_vv_ht 10
	val ps = polys_of_fm (vh, fm')
	val sps = RealAlg.univ_cad_sample ps
	val s_k = Int.toString (length sps)
    in
	trace_i (Fml fm -|- Disj (fm', sps))
		"rd"
		("Created Disj over sequence of " ^ s_k ^ 
		 " real algebraic sample points")
    end
  | rd _ = raise Invalid_inference "rd";

(* Inference rule RE (`RCF sample point Elimination') using real
   algebraic number computation. *)

fun re (Fml fm -|- Disj (fm', sp::sps)) =
    if MTAlgebra.eval_fm_at_sp fm' sp true then
	raise Witness sp
    else
	trace_i (Fml fm -|- Disj (fm', sps))
		"re"
		("Eliminated real algebraic sample point " ^
		 "(" ^ RealAlg.toIsabelleString sp ^ ")")
  | re _ = raise Invalid_inference "re";

(* Inference rule RT (`RCF formula is True') using real algebraic
   number computation. *)

fun rt (Fml fm -|- Disj (fm', sp::_)) =
    if MTAlgebra.eval_fm_at_sp fm' sp false then
	trace_i (Fml fm -|- True sp)
		"rt"
		("Satisfied formula with witness " ^
		 "(" ^ RealAlg.toIsabelleString sp ^ ")")
    else
	raise Invalid_inference "rt"
  | rt _ = raise Invalid_inference "rt";

(* Inference rule RF (`RCF formula is False') *)

fun rf (Fml fm -|- Disj (_, [])) = 
    trace_i (Fml fm -|- False)
	    "rf"
	    "Refuted formula"
  | rf _ = raise Invalid_inference "rf";

(* ======================================================================== *)
(*  End primitive thm constructors                                          *)
(* ======================================================================== *)

end

(* Find all univariate MetiTarski problems in tptp/Problems:
    grep "Dimension.*1" *.tptp | wc -l

    grep -l "Dimension.*1" ../tptp/Problems/*.tptp
 *)
