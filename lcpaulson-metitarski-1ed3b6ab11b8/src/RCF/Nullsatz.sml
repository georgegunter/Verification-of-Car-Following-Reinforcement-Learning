(* ======================================================================== *)
(*             A Proof-Producing Exists RCF proof procedure                 *)
(*                   based on the Real Nullstellensatz                      *)
(*          (including Groebner reduction, in the spirit of Tiwari)         *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure Nullsatz :> Nullsatz =
struct

open Algebra;
open MTAlgebra;
open Groebner;
open IntvlsFP;
open List;

(* Given a list of arithmetical atoms, convert it into an equational
   system with PD and PSD vars introduced as slack variables.

   Note that we must make sure to have the PD and PSD slack variables
   be placed lower in the variable ordering than the main variables
   appearing in the input constraint system.  To ensure this, we first
   do a linear pass over the entire (atom list) and convert it into a
   3-tuple (eq_polys, gt_polys, geq_polys), with each of these poly
   lists being Algebraic polynomials.  Then, we do a pass through
   gt_polys and geq_polys, introducing additional Algebraic
   indeterminates for each of them.  This process guarantees that
   these final indeterminates will have larger var-ID's than the
   main variables, and thus be smaller in the variable ordering.
  
   We return a 3-tuple: <eq_sys, pd_vs, psd_vs> equivalent to the
   original input system, with pd_vs and psd_vs being lists of
   integers corresponding to the var-ID's of the > and >= slack
   vars. *)

fun mk_eq_sys al vh =
    let val eq_polys = ref ([] : poly list)
	val gt_polys = ref ([] : poly list)
	val geq_polys = ref ([] : poly list)
	fun process_atom a =
	    let val p = poly_of_atom (vh, a) 
	    in case a of
		   ("=", _) => (eq_polys := p :: !eq_polys)
		 | (">", _) => (gt_polys := p :: !gt_polys)
		 | (">=", _) => (geq_polys := p :: !geq_polys)
		 | ("<=", _) => (geq_polys := (p_neg p) :: !geq_polys)
		 | ("<", _) => (gt_polys := (p_neg p) :: !gt_polys)
	    end
	val _ = map process_atom al
	val next_var_id = ref (Polyhash.numItems vh)
	val pd_vs = ref ([] : var_id list)
	val psd_vs = ref ([] : var_id list)
	val eq_sys = eq_polys
	fun process_poly v_lst p =
	    let val new_var_id = !next_var_id
		val _ = next_var_id := !next_var_id + 1
		val new_var_poly = [(Rat.one, [(new_var_id, 1)])] : poly
		val p' = p_sub (p, new_var_poly)
		val _ = (v_lst := new_var_id :: !v_lst;
			 eq_sys := p' :: !eq_sys)
	    in () end
	val _ = map (process_poly pd_vs) (!gt_polys)
	val _ = map (process_poly psd_vs) (!geq_polys)
    in (!eq_sys, !pd_vs, !psd_vs) end;

(* A hash table for converting Algebraic polynomials during Groebner
   basis construction (implicitly =0) to their Atom.atom
   counterparts. *)
(*** Skipping hash table for now... Must do this soon! ***)

(* Given an Nsatz search system (eq_sys, pd_vs, psd_vs),
   convert it to a list of Atom.atom's for ICP search. *)

fun atom_lst eq_sys pd_vs psd_vs =
    let fun v_str v = "x" ^ (Int.toString v)
	fun v_atom r v
	  = (r, [Term.Fn (v_str v, []), Term.Rat Rat.zero]) : Atom.atom
	fun tm_of_vp (vp : vp) =
	    case vp of (_, 0) => Term.Rat Rat.one
		     | (v, 1) => Term.Fn (v_str v, [])
		     | (v, n) => Term.Fn ("*", [Term.Fn (v_str v, []), 
						(tm_of_vp (v, n-1))])
	fun tm_of_pp (pp : pp) =
	    case pp of [] => Term.Rat Rat.one
		     | ((vid, pow) :: vps) =>
		       Term.Fn ("*", [(tm_of_vp (vid, pow)), tm_of_pp vps])
	fun tm_of_mono (m : mono) =
	    case m of (c, pp) => Term.Fn ("*", [Term.Rat c, tm_of_pp pp])
	fun tm_of_poly (p : poly) =
	    case p of
		[] => Term.Rat Rat.zero
	      | (m : mono) :: ms =>
		Term.Fn ("+", [tm_of_mono m, tm_of_poly ms])
	val pd_atoms = map (v_atom ">") pd_vs
	val psd_atoms = map (v_atom ">=") psd_vs
	val eq_atoms = map (fn p => ("=", [(tm_of_poly p), Term.Rat Rat.zero]))
			   eq_sys
    in pd_atoms @ psd_atoms @ eq_atoms end;

(* Sign colours: A poly will be mapped to a set (list) of these.  A
   `state witness' is a poly whose colours are in the set W s.t.

    W={{StrictNeg}, {StrictPos}, {Neg, StrictNeg}, {Pos, StrictPos}}.
*)

datatype sign_color = StrictNeg | Neg | Pos | StrictPos | Unknown;

(* Colour a monomial with its sign colours *)

fun vp_colour pd_vs psd_vs vp =
    case vp of
	(v, pow) => if (exists (fn i => v = i) pd_vs) then 
			StrictPos else
		    if (exists (fn i => v = i) psd_vs) 
		       orelse (pow mod 2 = 0) then
			Pos
		    else Unknown;
			
fun pp_colour pd_vs psd_vs pp = Useful.setify (map (vp_colour pd_vs psd_vs) pp)

fun mono_colour pd_vs psd_vs m = 
    case m of
	(c, pp) => let val pp_c = pp_colour pd_vs psd_vs pp in
		       if (pp_c = [StrictPos]) then
			   (if Rat.lt(Rat.zero, c) (* c > 0 *)
			    then StrictPos
			    else if Rat.lt(c, Rat.zero) (* c < 0 *)
			    then StrictNeg
			    else Unknown)
		       else 
			   if (pp_c = [Pos] orelse pp_c = [Pos, StrictPos]
			       orelse pp_c = [StrictPos, Pos])
			   then (if Rat.lt(Rat.zero, c) (* c > 0 *)
				 then Pos
				 else if Rat.lt(c, Rat.zero) (* c < 0 *)
				 then Neg
				 else Unknown)
			   else Unknown
		   end;

fun poly_colour pd_vs psd_vs p = Useful.setify (map (mono_colour pd_vs psd_vs) p);

fun poly_nsatz_witness pd_vs psd_vs p =
    let val p_colours = poly_colour pd_vs psd_vs p
    in (p_colours = [StrictNeg] orelse
	p_colours = [StrictPos] orelse
	p_colours = [Neg, StrictNeg] orelse
	p_colours = [StrictNeg, Neg] orelse
	p_colours = [Pos, StrictPos] orelse
	p_colours = [StrictPos, Pos]) end;

(* A bounded search for Real Nullstellensatz witnesses using Groebner
   basis construction and ICP (in the spirit of the Tiwari method). 

   [nsatz_search]
    al:      Atom.atom list of input constrants,
    limit:   Limit on number of S-polynomials to be derived.

   [nsatz_search']
    gs:      Input polynomials in Algebraic notation,
    s_pairs: Initial pairing of S-polys to be processed, 
    pd_vs:x   List of (string notation) ring vars assumed to be >0,
    psd_vs:  List of (string notation) ring vars assumed to be >=0,
    limit:   Limit on number of S-polynomials to be derived. 

  * Note on how to call ICP if we wish to use it to recognize witnesses:

      (case bap_on_al (atom_lst gs pd_vs psd_vs, 5, 2, 2) of
  		     BAP_EMPTY => true
		   | _ => false)
 *)
    
fun nsatz_search' gs s_pairs pd_vs psd_vs limit =
    if (limit <= 0) then 
	let val reduced_gs = gb_reduce gs in
	    List.exists (poly_nsatz_witness pd_vs psd_vs) 
			(map p_sum (Useful.cart reduced_gs reduced_gs)) end
    else
	case s_pairs of 
	    [] => let val reduced_gs = gb_reduce gs in
		      List.exists (poly_nsatz_witness pd_vs psd_vs) 
				  (map p_sum (Useful.cart reduced_gs reduced_gs)) end
	  | ((p, p') :: s_ps) =>
	    let val q = s_poly p p'
		val (_, q') = p_div q gs
		val (c, pp) = p_hm q'
		(* val _ = print ("Checking if new S-poly is Nsatz witness...\n") *)
	    in
		if not(Rat.eq(c, Rat.zero)) andalso pp = [] 
		then true
		else
		    if p_eq (q', p_zero)
		    then nsatz_search' gs s_ps pd_vs psd_vs (limit - 1) else
		    
		    (* Check to see if S-poly is an Nsatz witness *)
		    
		    if poly_nsatz_witness pd_vs psd_vs q' then true else
		    nsatz_search' (q' :: gs) ((map (fn x => (q', x)) gs) @ s_pairs) 
				  pd_vs psd_vs (limit - 1)
	    end;

fun nsatz_search al limit =
    let val vh = mk_vv_ht 10
	val (fs, pd_vs, psd_vs) = mk_eq_sys al vh
	(* val _ = map (fn a => print ("Atom: " ^ (Atom.toString a) ^ "\n")) al
	   val _ = print ("\n About to start Nsatz search. Length[fs]=" 
		       ^ (Int.toString (length fs)) ^ "\n") *)
	val result = 
	(* First, check if we already have a state witness *)
	    if List.exists (poly_nsatz_witness pd_vs psd_vs) fs 
	    then true 
	(* Otherwise, start the search for one! *)
	    else nsatz_search' fs (Groebner.uc_pairs fs) pd_vs psd_vs limit 
    in ((* if result then print "Nullsatz witness found!\n" else (); *)
	result)
    end;

(* Formula -> (atom list) list machinery *)

datatype fml_ns_fr = NSATZ_FRIENDLY of ((Atom.atom list) list) 
		   | NSATZ_UNFRIENDLY;

fun nsatz_friendly f = 
    case qfm f of
	SOME q => 
	let val ex = ref false
	    val qfm_dnf = dnf q
		handle DNF_TOO_LARGE => (ex := true; [])
	    val qfm_dnf_al = map (icp_atom_lst) qfm_dnf
	in if !ex then NSATZ_UNFRIENDLY else NSATZ_FRIENDLY qfm_dnf_al end
      | NONE => NSATZ_UNFRIENDLY;

(* Run branch and prune ICP on a list of conjunctive cases *)

fun nsatz_on_cases dnf_al limit =
    case dnf_al of
	[] => true
      | (al::als) => 
	case nsatz_search al limit of
	    true => nsatz_on_cases als limit
	  | _ => false;

(* Nullstellensatz search on a Formula.formula *)

fun nsatz_search_on_fml f limit =
    if (f = Formula.True) then false else
    if (f = Formula.False) then true else
    case nsatz_friendly f of
	NSATZ_FRIENDLY dnf_al => 
	 let val result = nsatz_on_cases dnf_al limit
	     (* val _ = if result then 
			 print ("\n---> Nsatz witness found!\n Thus, " 
				^ (Formula.toString f) 
				^ "\n   is UNSAT.\n\n") else () *)
	 in result end
      | NSATZ_UNFRIENDLY => false;

end;
