(* ======================================================================== *)
(*               Proof Procedures for Certified RCF Judgments               *)
(*                      - Derived proof procedures -                        *)
(*                                                                          *)
(*  by G.O.Passmore, LFCS, Univ. Edinburgh and Clare Hall, Univ. Cambridge  *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure CertRCFp : CertRCFp =
struct

open CertRCFk; (* LCF-style kernel for univariate RCF *)

(* A complete univariate RCF decision procedure using the proof system
   defined in the CertRCF kernel. Given an implicitly existential RCF
   formula Phi(x), we work to decide its status, returning either

   (Fml Phi(x)) -|- True (w : RealAlg.real_alg)

    or

   (Fml Phi(x)) -|- False. *)

fun univ_prove (fm : Formula.formula) =
    let val t0 = ra (Fml fm)
	val t1 = rd t0
	val tk = ref t1
	val wf = ref false
    in 
	while ((thm_r (!tk) <> False)
	       andalso not(!wf))
	      do
	      (case thm_r (!tk) of
		   Disj (_, []) => tk := rf (!tk)
		 | _ => tk := re (!tk))
	handle (Witness r) =>
	       (tk := rt (!tk);
		wf := true);
	(!tk)		
  end;	

(* Attempt to refute an existential RCF formula, returning true if
   we're successful, false otherwise. This is the simplest interface
   through which MetiTarski will access this certified RCF module.
   Note that this throws away the real algebraic witnesses we compute
   when an input formula is satisfiable. We'll want to later retrieve
   these for, e.g., an extended real algebraic version of the model-
   sharing framework. *)

fun univ_refute (fm : Formula.formula) =
    case fm of
	Formula.True => false (* We can't refute True! *)
      | Formula.False => true (* Obviously ... *)
      | _ =>  
	case thm_r (univ_prove fm) of
	    True _ => false
	  | False => true
	  | _ => raise Useful.Error 
		       ("Univ_refute failed to decide its input formula. " ^
			"This shouldn't be possible."); 

(* Univ prove for an explicitly quantified formula *)

fun univ_prove_q (fm : Formula.formula) =
    let val _ = print("- CertRCF is working directly upon the input formula.\n") 
    in
    if Formula.isForall fm then
	(print "- Input formula is universal. Searching for counterexample...\n\n";
	 univ_refute (Formula.Not (#2 (Formula.destForall fm))))
    else (print "- Input formula is existential. Searching for witness...\n\n";
	  not (univ_refute (#2 (Formula.destExists fm))))
    end

end
