(* ======================================================================== *)
(*                     Partial CAD Projection Ordering                      *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure CADProjO :> CADProjO =
struct

open Algebra;   (* <- Sparse polynomial algebra (SPA), monomial orders, etc. *)
open MTAlgebra; (* <- Conversion between MT terms and SPA polynomials *) 

(* Type for var_id formula statistics -- We call arrays of these SA's *)

type vf_stats = {max_deg  : int,  (* max deg in which v appears *)
		 max_tdeg : int,  (* max total deg of mono in which v appears *)
		 num_tms  : int}; (* num monomials containing v *)

(* String of a vf_stats record  *)

fun vf_stats_toString {max_deg = m,
		       max_tdeg = m',
		       num_tms = m''} = 
    "{max_deg  = " ^ Int.toString(m) ^ ",\n" ^
    " max_tdeg = " ^ Int.toString(m') ^ ",\n" ^
    " num_tms  = " ^ Int.toString(m'') ^ "}.\n";

(* Given a power product in Q[x_0, ..., x_{n-1} and an SA update the
   given SA accordingly. *)

fun final_pp_update_sa (sa : vf_stats array, mtd : int, vs : var_id list) =
    case vs of
	[] => ()
      | (v :: s) =>
	let val {max_deg = cur_max_deg, 
		 max_tdeg = cur_max_tdeg, 
		 num_tms = cur_num_tms} = Array.sub(sa, v)
	    val _ = if mtd > cur_max_tdeg then
			Array.update(sa, v, {max_deg = cur_max_deg,
					     max_tdeg = mtd,
					     num_tms = cur_num_tms})
		    else () 
	in final_pp_update_sa(sa, mtd, s) end;

fun pp_update_sa' (pp : pp, sa : vf_stats array, mtd : int, vs : var_id list) =
    case pp of
	[] => final_pp_update_sa (sa, mtd, vs)
      | ((v, p) :: s) =>
	let val {max_deg = cur_max_deg,
		 max_tdeg = cur_max_tdeg,
		 num_tms = cur_num_tms} = Array.sub(sa, v)
	    val new_v_stats = {max_deg = Int.max(cur_max_deg, p),
			       max_tdeg = cur_max_tdeg,
			       num_tms = cur_num_tms + 1}
	    val _ = Array.update(sa, v, new_v_stats) 
	in
	    pp_update_sa' (s, sa, mtd + p, Useful.union [v] vs)
	end;

fun pp_update_sa (pp : pp, sa : vf_stats array) =
    pp_update_sa' (pp, sa, 0, []);

(* Given a monomial m in Q[x_0, ..., x_{n-1}] and an SA, 
    update SA based on m. *)    

fun m_update_sa (m : mono, sa : vf_stats array) =
    case m of (_, pp) => pp_update_sa(pp, sa);

(* Given a polynomial p in Q[x_0, ..., x_{n-1}], compute an
    SA for each variable x_i w.r.t. p *)

fun p_vf_stats (p : poly, sa : vf_stats array) =
    case p of
	[] => sa
      | (m :: s) => (m_update_sa(m, sa);
		     p_vf_stats(s, sa));

(* Given two vf_stats arrays, merge them, taking the max of the max_
   values and sum of the num_tms.  We assume sa and sa' are of the
   same length.  We update sa in place and return it. *)

fun merge_vf_stats' (sa, sa', count) =
    if (count < 0) then sa else
    let val {max_deg = md, max_tdeg = mt, num_tms = nt} 
	    = Array.sub(sa, count)
	val {max_deg = md', max_tdeg = mt', num_tms = nt'}
	    = Array.sub(sa', count)
	val new_v_stat =
	    {max_deg = Int.max(md, md'),
	     max_tdeg = Int.max(mt, mt'),
	     num_tms = nt + nt'}
	val _ = Array.update(sa, count, new_v_stat) 
    in merge_vf_stats' (sa, sa', count - 1) end;

fun merge_vf_stats (sa, sa' : vf_stats array) =
    merge_vf_stats' (sa, sa', Array.length(sa) - 1) : vf_stats array;

(* Given a vf_stats array, clear it. *)

fun clear_vf_stats (sa : vf_stats array) =
    Array.modify (fn _ => {max_deg = 0, max_tdeg = 0, num_tms = 0}) sa;

(* Given a lists of polynomials P in Q[x_0, ..., x_{n-1}], compute an
    array of vf_stats for each variable x_i w.r.t. P.  

   Var width is n when our polynomial ring is Q[x_0, ..., x_{n-1}].

   Note for ps_vf_stats' : The stats array computed is the one passed
    in as sa.  The stats array passed in as sa' is an auxiliary
    `scratch' buffer. *)

fun ps_vf_stats' (ps : poly list, sa, sa' : vf_stats array) =
    case ps of
	[] => sa : vf_stats array
      | (p :: s) => let val _ = clear_vf_stats(sa')
			val p_sa = p_vf_stats(p, sa') in
			ps_vf_stats' (s, merge_vf_stats(sa, p_sa), sa')
		    end;

fun ps_vf_stats (var_width : int, ps : poly list) =
    let val sa = Array.array(var_width, 
		       {max_deg = 0, max_tdeg = 0, num_tms = 0})
	val sa' = Array.array(var_width, 
		       {max_deg = 0, max_tdeg = 0, num_tms = 0}) 
    in ps_vf_stats' (ps, sa, sa') end;

(* Given a ground MT formula, construct a vf_stats array for its
   variables.  We return also the vh which was used to setup the
   MT<->SM var correspondence. *)

fun vf_stats_of_fm (fm : Formula.formula) =
    let val vh = mk_vv_ht 10
	val ps = polys_of_fm (vh, fm)
	val vf_stats = ps_vf_stats (Polyhash.numItems(vh), ps) in
	(vf_stats, vh)
    end;

(* Construct an ordering on var_id's using vf_stats.
   We order v_x < v_y if v_x should be projected away before v_y. *)

fun cmp_by_vf_stats vf_stats (x, y) =
    let val {max_deg = x_md, max_tdeg = x_mt, num_tms = x_nt} 
	    = Array.sub(vf_stats, x)
	val {max_deg = y_md, max_tdeg = y_mt, num_tms = y_nt}
	    = Array.sub(vf_stats, y)
	in
	if x_md < y_md then General.LESS else
	if x_md > y_md then General.GREATER else
	(if x_mt < y_mt then General.LESS else
	 if x_mt > y_mt then General.GREATER else
	 (if x_nt < y_nt then General.LESS else
	  if x_nt > y_nt then General.GREATER else
	  (if x < y then General.LESS else 
	   if x > y then General.GREATER else
	   General.EQUAL)))
    end;

(* Make a list consisting of the elements 0 to n-1 (order does not
   matter -- this function will make the list descend) *)

fun mk_var_id_lst 0 = []
  | mk_var_id_lst n = 
    let val n' = n-1 in n' :: mk_var_id_lst n' end;

(* Convert a var_id list to a string *)

fun vl_toString vs =
    case vs of [] => ""
	     | (v :: s) => Int.toString(v) ^
			   (if not(List.null(s)) then ", " else ".")
			   ^ vl_toString(s);

(* Given an ordered list L of var_id's and a vh, map L to
   a list of MT vars, preserving the order of L, via vh. 

   Should eventually redo this using two hash VAR<->VID hashes. *)

datatype po = VID of var_id | VSTR of string;

fun po_inject (ns : int list) =
    case ns of
	[] => []
      | (n :: s) => (VID n) :: po_inject s;

fun po_deject (pl : po list) =
    case pl of [] => []
	     | ((VSTR s) :: r) =>
	       s :: po_deject r
	     | _ => raise Useful.Error "po_deject failed.";

fun mt_replace (ns : po list, i : int, b : string) =
    case ns of [] => []
	    | ((VID n) :: s) => 
	      (if (n = i) then (VSTR b) else (VID n))
	      :: mt_replace (s, i, b)
	    | (x :: s) => x :: mt_replace(s, i, b);
	      
fun mt_proj_order' (vs, vh_lst) =
    case vh_lst of 
	[] => vs
      | ((v_str, v_id) :: vv) => 
	mt_proj_order' (mt_replace(vs, v_id, v_str), vv);

fun mt_proj_order (vs, vh) =
    let val vh_lst = Polyhash.listItems(vh)
    in po_deject (mt_proj_order' (po_inject vs, vh_lst)) end;

(* Given a list of var_ids and a vf_stats array, print the stats
   of each var_id in the order given. *)

fun print_vf_stats (vf_stats, vs) =
    case vs of [] => ()
	     | v :: s => (print (vf_stats_toString(Array.sub(vf_stats, v)));
			  print_vf_stats (vf_stats, s))

(* Construct projection ordering on variables based on vf_stats *)

fun proj_order_fm (fm : Formula.formula) =
    let val (vf_stats, vh) = vf_stats_of_fm fm
	val cmp_var_ids = cmp_by_vf_stats vf_stats
	val var_id_lst = mk_var_id_lst (Polyhash.numItems(vh))
	val sorted_var_ids = Useful.sort cmp_var_ids var_id_lst
	(* val _ = print_vf_stats (vf_stats, List.rev sorted_var_ids) *)
    in
	List.rev (mt_proj_order (sorted_var_ids, vh))
	(* We reverse this at the end as QepcadB expects variables
           to be ordered [x,y] if y should be projected before x. *)
    end;

end;
