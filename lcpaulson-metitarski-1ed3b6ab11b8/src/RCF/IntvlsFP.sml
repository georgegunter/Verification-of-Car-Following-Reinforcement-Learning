(* ======================================================================== *)
(*               Core Arithmetical and Narrowing Machinery for              *)
(*                  Generalised (Non-Compact) Real Intervals                *)
(*                             -including an-                               *)
(*  ICP-based technique for finding rational witnesses for SAT RCF formulas *)
(*                                                                          *)
(*    with interval endpoints taken over FP_ext = (FP union {-inf, +inf})   *)
(*       (our +-inf are distinct from the floating point infinities)        *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2012 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure IntvlsFP :> IntvlsFP =
struct

(* Open floating point control package *)

open Common;

(* Boundary type: Either left closed ('[') or right closed (']') *)

datatype bt = LEFT_CLOSED | RIGHT_CLOSED;

(* Infinity type *)

datatype infty = NEG_INFTY | POS_INFTY;

(* Endpoint type, Q_ext: Either an exact precision rational or +/- infty *)

datatype ep = Num of real | Infty of infty;

(* Generalised interval type: a left boundary type, left and right
   endpoints, and a right boundary type. *)

type intvl = bt * ep * ep * bt;

(* Some simple tracing *)

val trace_lvl = ref 0;

fun trace (i, s) =
    if (i <= !trace_lvl) then print(s ^ "\n") else ();

val traceb = ref (!trace_lvl > 0);

fun set_icp_trace(i) =
    (trace_lvl := i;
     traceb := i > 0);

(* Exception for bad endpoint arithmetic *)

exception EP_ARITH_UNDEF;

(* The zero endpoint *)

val ep_zero = Num(0.0);

(* Negation of infinities *)

fun inf_negate NEG_INFTY = POS_INFTY
  | inf_negate POS_INFTY = NEG_INFTY;

(* Negation of endpoints *)

fun ep_negate (e) =
    case e of Infty inf => Infty (inf_negate inf)
	    | Num q => Num (~ q);

(* Floating point rounding mode *)

datatype fp_rm = LO | HI | NM;

(* Set floating point rounding mode *)

fun set_rm (LO) = IEEEReal.setRoundingMode(IEEEReal.TO_NEGINF)
  | set_rm (HI) = IEEEReal.setRoundingMode(IEEEReal.TO_POSINF)
  | set_rm (NM) = IEEEReal.setRoundingMode(IEEEReal.TO_NEAREST);

(* Addition of interval endpoints *)

fun ep_add (e1, e2, m) =
    let val prevRM = IEEEReal.getRoundingMode() in
	(set_rm(m);
	 let val result =
		 case (e1, e2) of
		     ((Num a), (Num b)) => Num (a + b)
		   | ((Num _), (Infty b)) => Infty(b)
		   | ((Infty a), (Num _)) => Infty(a)
		   | ((Infty a), (Infty b)) =>
		     if a = b then (Infty a)
		     else raise EP_ARITH_UNDEF
	 in
	     (IEEEReal.setRoundingMode(prevRM);
	      result)
	 end)
    end;

(* Negation of interval boundary types *)

fun bt_neg LEFT_CLOSED = RIGHT_CLOSED
  | bt_neg RIGHT_CLOSED = LEFT_CLOSED;

(* Subtraction of interval endpoints *)

fun ep_sub (e1, e2, m) =
    let val prevRM = IEEEReal.getRoundingMode() in
	(set_rm(m);
	 let val result =
		 case (e1, e2) of
		     ((Num a), (Num b)) => Num(a - b)
		   | ((Num _), (Infty b)) => Infty(inf_negate(b))
		   | ((Infty a), (Num _)) => Infty(a)
		   | ((Infty NEG_INFTY), (Infty POS_INFTY)) => Infty(NEG_INFTY)
		   | ((Infty POS_INFTY), (Infty NEG_INFTY)) => Infty(POS_INFTY)
		   | _ => raise EP_ARITH_UNDEF
	 in
	     (IEEEReal.setRoundingMode(prevRM);
	      result)
	 end)
    end;

(* Multiplication of interval endpoints *)

fun ep_mult (e1, e2, m) =
    let val prevRM = IEEEReal.getRoundingMode() in
	(set_rm(m);
	 let val result =
		 case (e1, e2) of
		     ((Num a), (Num b)) => Num(a * b)
		   | ((Infty a), (Num b)) =>
		     if (b > 0.0) then Infty(a)
		     else if (b < 0.0) then Infty(inf_negate(a))
		     else raise EP_ARITH_UNDEF
		   | ((Num a), (Infty b)) =>
		     if (a > 0.0) then Infty(b)
		     else if (a < 0.0) then Infty(inf_negate(b))
		     else raise EP_ARITH_UNDEF
		   | ((Infty a), (Infty b)) =>
		     if a = b then Infty(POS_INFTY) else Infty(NEG_INFTY)
	 in
	     (IEEEReal.setRoundingMode(prevRM);
	      result)
	 end)
    end;

(* Division of interval endpoints *)

fun ep_div (e1, e2, m) =
    let val prevRM = IEEEReal.getRoundingMode() in
	(set_rm(m);
	 let val result =
		 case (e1, e2) of
		     ((Num a), (Num b)) =>
		     if Real.==(b, 0.0) then raise EP_ARITH_UNDEF
		     else Num(a / b)
		   | ((Infty _), (Infty _)) => raise EP_ARITH_UNDEF
		   | ((Infty NEG_INFTY), (Num b)) =>
		     if Real.==(b, 0.0) then raise EP_ARITH_UNDEF
		     else if (b > 0.0) then (Infty NEG_INFTY)
		     else (Infty POS_INFTY) (* b < 0 *)
		   | ((Infty POS_INFTY), (Num b)) =>
		     if Real.==(b, 0.0) then raise EP_ARITH_UNDEF
		     else if (b > 0.0) then (Infty POS_INFTY)
		     else (Infty NEG_INFTY)
		   | ((Num _), (Infty _)) => ep_zero
	 in
	     (IEEEReal.setRoundingMode(prevRM);
	      result)
	 end)
    end;

(* Comparision relations {<=, <, =, >, >=} on interval endpoints *)

fun ep_leq ((Num e1), (Num e2)) = e1 <= e2
  | ep_leq ((Infty NEG_INFTY), _) = true
  | ep_leq (_, (Infty POS_INFTY)) = true
  | ep_leq _ = false;

fun ep_eq ((Num e1), (Num e2)) = Real.==(e1, e2)
  | ep_eq ((Infty e1), (Infty e2)) = e1 = e2
  | ep_eq _ = false;

fun ep_lt (e1, e2) = ep_leq(e1, e2) andalso not(ep_eq(e1, e2));

fun ep_gt (e1, e2) = ep_lt(e2, e1);

fun ep_geq (e1, e2) = ep_leq(e2, e1);

(* Minimum and Maximum of two endpoints *)

fun ep_min (e1, e2) = if ep_leq(e1, e2) then e1 else e2;

fun ep_max (e1, e2) = if ep_geq(e1, e2) then e1 else e2;

(* Interval equality predicate *)

fun eq (((bl1, l1, r1, br1), (bl2, l2, r2, br2)) : intvl * intvl) =
    bl1 = bl2 andalso ep_eq(l1, l2) andalso ep_eq(r1, r2) andalso br1 = br2;

(* Interval emptiness predicate *)

fun isEmpty (LEFT_CLOSED, el, er, RIGHT_CLOSED) =
    if (ep_gt(el, er) orelse ep_eq(el, Infty(POS_INFTY))
	orelse ep_eq(er, Infty(NEG_INFTY)))
    then true else false
  | isEmpty (_, el, er, _) =
    if (ep_geq(el, er) orelse ep_eq(el, Infty(POS_INFTY))
	orelse ep_eq(er, Infty(NEG_INFTY)))
       then true else false;

(* Make an interval *)

fun mk_intvl (bt1, l, r, bt2) =  (bt1, l, r, bt2) : intvl;

(* A canonical empty interval: We use [1, 0]. *)

val EMPTY_INTVL =
    mk_intvl (LEFT_CLOSED,
	      Num 1.0,
	      Num 0.0,
	      RIGHT_CLOSED);

(* Convert an interval to a string *)

fun bt_str LEFT_CLOSED = "["
  | bt_str RIGHT_CLOSED = "]";

(* Print a floating point to full precision *)

fun real_to_string (r) =
    IEEEReal.toString(Real.toDecimal(r));

fun ep_str (Infty POS_INFTY) = "+inf"
  | ep_str (Infty NEG_INFTY) = "-inf"
  | ep_str (Num q) = real_to_string q;

fun intvl_toString (i : intvl) =
    if isEmpty(i) then "empty" else
    case i of
	(bl, el, er, br) =>
	bt_str(bl) ^ ep_str(el) ^ ", " ^ ep_str(er) ^ bt_str(br);

(* Selector functions for boundary types *)

fun sel_bt_l true = LEFT_CLOSED
  | sel_bt_l false = RIGHT_CLOSED;

fun sel_bt_r true = RIGHT_CLOSED
  | sel_bt_r false = LEFT_CLOSED;

(* Interval addition *)

fun add ((i1, i2) : intvl * intvl) =
    if (isEmpty(i1) orelse isEmpty(i2)) then EMPTY_INTVL else
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	let val bl = sel_bt_l(b1l = LEFT_CLOSED andalso b2l = LEFT_CLOSED)
	    val br = sel_bt_r(b1r = RIGHT_CLOSED andalso b2r = RIGHT_CLOSED)
	in
	    mk_intvl (bl, ep_add(l1, l2, LO), ep_add(r1, r2, HI), br)
	end;

(* Interval subtraction *)

fun sub ((i1, i2) : intvl * intvl) =
    if (isEmpty(i1) orelse isEmpty(i2)) then EMPTY_INTVL else
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	let val bl = sel_bt_l(b1l = LEFT_CLOSED andalso b2r = RIGHT_CLOSED)
	    val br = sel_bt_r(b1r = RIGHT_CLOSED andalso b2l = LEFT_CLOSED)
	    val l = case ep_sub(l1, r2, LO) of
			(Num x) => (Num x)
		      | _ => (Infty NEG_INFTY)
	    val r = case ep_sub(r1, l2, HI) of
			(Num x) => (Num x)
		      | _ => (Infty POS_INFTY)
	in
	    mk_intvl (bl, l, r, br)
	end;

(* Interval multiplication:

   This is a rather technically involved arithmetical operation, due
   to a combination of (i) the undefinedness of ((+/- inf) * 0), which
   we avoid using interval closure classification, (ii) the difficulty
   in classifying product boundary types.  (If we were dealing only
   with compact intervals then this would be easy; but, the technical
   maneuvering required for our handling of generalised intervals will
   pay off in due course!)

   We begin with machinery for interval closure classification. *)

datatype m_intvl_class = M | Z | P | N;

(* Exception for unclassifiable interval *)

exception CLASSLESS_INTVL;

(* Classify the closure of an interval realisation.  This is used for
   interval multiplication.  We will refine it further for use with
   interval division below. *)

fun m_classify (bl, l, r, br) : m_intvl_class =
    if (ep_lt(l, ep_zero) andalso ep_lt(ep_zero, r)) then M
    else if (ep_eq(l, ep_zero) andalso ep_eq(r, ep_zero)) then Z
    else if (ep_leq(ep_zero, l) andalso ep_leq(l, r)
	     andalso ep_gt(r, ep_zero)) then P
    else if (ep_leq(l, r) andalso ep_leq(r, ep_zero)
	     andalso ep_lt(l, ep_zero)) then N
    else raise CLASSLESS_INTVL;

(* Determine left endpoint value of an interval product *)

fun mult_left_ep ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), m_classify(i2)) of
	    (P, P) => ep_mult(l1, l2, LO)
	  | (P, M) => ep_mult(r1, l2, LO)
	  | (P, N) => ep_mult(r1, l2, LO)
	  | (M, P) => ep_mult(l1, r2, LO)
	  | (M, M) => ep_min(ep_mult(l1, r2, LO), ep_mult(r1, l2, LO))
	  | (M, N) => ep_mult(r1, l2, LO)
	  | (N, P) => ep_mult(l1, r2, LO)
	  | (N, M) => ep_mult(l1, r2, LO)
	  | (N, N) => ep_mult(r1, r2, LO)
	  | _ => ep_zero;

(* Determine right endpoint value of interval product *)

fun mult_right_ep ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), m_classify(i2)) of
	    (P, P) => ep_mult(r1, r2, HI)
	  | (P, M) => ep_mult(r1, r2, HI)
	  | (P, N) => ep_mult(l1, r2, HI)
	  | (M, P) => ep_mult(r1, r2, HI)
	  | (M, M) => ep_max(ep_mult(l1, l2, HI), ep_mult(r1, r2, HI))
	  | (M, N) => ep_mult(l1, l2, HI)
	  | (N, P) => ep_mult(r1, l2, HI)
	  | (N, M) => ep_mult(l1, l2, HI)
	  | (N, N) => ep_mult(l1, l2, HI)
	  | _ => ep_zero;

(* Omega judgment for determing product closure *)

fun omega ((el, er, alpha, gamma) : ep * ep * bool * bool) =
    (alpha andalso gamma) orelse
    (alpha andalso ep_eq(el, ep_zero)) orelse
    (gamma andalso ep_eq(er, ep_zero));

(* Inverses of sel_bt_l and sel_bt_r *)

fun is_bt_cl (bt) = (bt = LEFT_CLOSED);

fun is_bt_cr (bt) = (bt = RIGHT_CLOSED);

(* Determine if interval product should be left closed *)

fun mult_left_closed ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), m_classify(i2)) of
	    (P, P) => omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l))
	  | (P, M) => omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l))
	  | (P, N) => omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l))
	  | (M, P) => omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
	  | (M, M) => let val prod_l1_r2 = ep_mult(l1, r2, LO)
			  val prod_r1_l2 = ep_mult(r1, l2, LO)
		      in
			  if ep_lt(prod_l1_r2, prod_r1_l2) then
			      omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
			  else if ep_eq(prod_l1_r2, prod_r1_l2) then
			      (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
			       orelse
			       omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l)))
			  else omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l))
		      end
	  | (M, N) => omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l))
	  | (N, P) => omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
	  | (N, M) => omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
	  | (N, N) => omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
	  | _ => true;

(* Determine if interval product should be right closed *)

fun mult_right_closed ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), m_classify(i2)) of
	    (P, P) => omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
	  | (P, M) => omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
	  | (P, N) => omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
	  | (M, P) => omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
	  | (M, M) => let val prod_l1_l2 = ep_mult(l1, l2, HI)
			  val prod_r1_r2 = ep_mult(r1, r2, HI)
		      in
			  if ep_lt(prod_l1_l2, prod_r1_r2) then
			      omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
			  else if ep_eq(prod_l1_l2, prod_r1_r2) then
			      (omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
			       orelse
			       omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
			  else omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l))
		      end
	  | (M, N) => omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l))
	  | (N, P) => omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l))
	  | (N, M) => omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l))
	  | (N, N) => omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l))
	  | _ => true;

(* The culmination of our above hard work: Interval multiplication. *)

fun mult ((i1, i2) : intvl * intvl) : intvl =
    if (isEmpty(i1) orelse isEmpty(i2)) then EMPTY_INTVL else
    mk_intvl (sel_bt_l(mult_left_closed(i1, i2)),
	      mult_left_ep(i1, i2),
	      mult_right_ep(i1, i2),
	      sel_bt_r(mult_right_closed(i1, i2)));

(* Interval closure classification for interval division.  This
   classification is finer than that required for multiplication. *)

datatype d_intvl_class = DM | DZ | DP0 | DP1 | DN0 | DN1;

fun d_classify (i as (bl, l, r, br)) : d_intvl_class =
    if isEmpty(i) then raise CLASSLESS_INTVL
    else if (ep_lt(l, ep_zero) andalso ep_lt(ep_zero, r)) then DM
    else if (ep_eq(l, ep_zero) andalso ep_eq(r, ep_zero)) then DZ
    else if (ep_eq(l, ep_zero) andalso ep_gt(r, ep_zero)) then DP0
    else if (ep_gt(l, ep_zero) andalso ep_gt(r, ep_zero)) then DP1
    else if (ep_lt(l, ep_zero) andalso ep_eq(r, ep_zero)) then DN0
    else if (ep_lt(l, ep_zero) andalso ep_lt(l, ep_zero)) then DN1
    else raise CLASSLESS_INTVL;

(* Determine if interval division should be left closed.  This becomes
   even more involved than the corresponding functions for interval
   multiplication, as there are two cases in our classification in
   which the division of intervals can result in a union of two
   disjoint connected components.  These special cases are (P, DM) and
   (N, DM) in the (m_classify(i), d_classify(i)) classification.
   Because of this, this function will return a tagged boolean of the
   form: SINGLETON bool | DOUBLETON bool * bool, with the DOUBLETON
   case being used to determine the boundary types of the resulting
   two intervals for (P, DM) and (N, DM) divisions. *)

datatype d_lrc = CLSNG of bool | CLDBL of bool * bool;

fun div_left_closed ((i1, i2) : intvl * intvl) : d_lrc =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (P, DP0) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (P, DM) => CLDBL (false,
			      omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (P, DN0) => CLSNG (false)
	  | (P, DN1) => CLSNG (omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r)))
	  | (M, DP1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (M, DN1) => CLSNG (omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r)))
	  | (M, _) => CLSNG (false)
	  | (N, DP1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (N, DP0) => CLSNG (false)
	  | (N, DM) => CLDBL (false,
			      omega(r1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (N, DN0) => CLSNG (omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l)))
	  | (N, DN1) => CLSNG (omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l)))
	  | (Z, _) => CLSNG (true)
	  | _ => CLSNG (true) (* This will be ultimately ignored in division,
			         as quotients of this class will be empty. *);

(* Determine if interval division should be right closed *)

fun div_right_closed ((i1, i2) : intvl * intvl) : d_lrc =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => CLSNG (omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l)))
	  | (P, DP0) => CLSNG (false)
	  | (P, DM) => CLDBL (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)),
			      false)
	  | (P, DN0) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (P, DN1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (M, DP1) => CLSNG (omega(r1, l2, is_bt_cr(b1r), is_bt_cl(b2l)))
	  | (M, DN1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (M, _) => CLSNG (false)
	  | (N, DP1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (N, DP0) => CLSNG (omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r)))
	  | (N, DM) => CLDBL (omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r)),
			      false)
	  | (N, DN0) => CLSNG (false)
	  | (N, DN1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r)))
	  | (Z, _) => CLSNG (true)
	  | _ => CLSNG (true) (* This will be ultimately ignored in division,
			         as quotients of this class will be empty. *);

(* Type for interval endpoints resulting from interval divisions.
   As with the division boundary types, we need to allow for division
   results consisting of a pair of disjoint connected components. *)

datatype d_ep = EPSNG of ep | EPDBL of ep * ep;

(* Determine left endpoint value of an interval quotient.  Note that
   the result may include two left endpoints, via EPDBL. *)

fun div_left_ep ((i1, i2) : intvl * intvl) : d_ep =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => EPSNG (ep_div(l1, r2, LO))
	  | (P, DP0) => EPSNG (ep_div(l1, r2, LO))
	  | (P, DM) => EPDBL ((Infty NEG_INFTY), (ep_div(l1, r2, LO)))
	  | (P, DN0) => EPSNG (Infty NEG_INFTY)
	  | (P, DN1) => EPSNG (ep_div(r1, r2, LO))
	  | (M, DP1) => EPSNG (ep_div(l1, l2, LO))
	  | (M, DN1) => EPSNG (ep_div(r1, r2, LO))
	  | (M, _) => EPSNG (Infty NEG_INFTY)
	  | (N, DP1) => EPSNG (ep_div(l1, l2, LO))
	  | (N, DP0) => EPSNG (Infty NEG_INFTY)
	  | (N, DM) => EPDBL ((Infty NEG_INFTY), ep_div(r1, l2, LO))
	  | (N, DN0) => EPSNG (ep_div(r1, l2, LO))
	  | (N, DN1) => EPSNG (ep_div(r1, l2, LO))
	  | (Z, _) => EPSNG ep_zero
	  (* Final case below will lead to [1,0] - i.e., empty *)
	  | _ => EPSNG (Num 1.0);

(* Determine right endpoint value of an interval quotient. Note that
   the result may include two left endpoints, via EPDBL. *)

fun div_right_ep ((i1, i2) : intvl * intvl) : d_ep =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => EPSNG (ep_div(r1, l2, HI))
	  | (P, DP0) => EPSNG (Infty POS_INFTY)
	  | (P, DM) => EPDBL ((ep_div(l1, l2, HI)), (Infty POS_INFTY))
	  | (P, DN0) => EPSNG (ep_div(l1, l2, HI))
	  | (P, DN1) => EPSNG (ep_div(l1, l2, HI))
	  | (M, DP1) => EPSNG (ep_div(r1, l2, HI))
	  | (M, DN1) => EPSNG (ep_div(l1, r2, HI))
	  | (M, _) => EPSNG (Infty POS_INFTY)
	  | (N, DP1) => EPSNG (ep_div(r1, r2, HI))
	  | (N, DP0) => EPSNG (ep_div(r1, r2, HI))
	  | (N, DM) => EPDBL ((ep_div(r1, r2, HI)), (Infty POS_INFTY))
	  | (N, DN0) => EPSNG (Infty POS_INFTY)
	  | (N, DN1) => EPSNG (ep_div(l1, r2, HI))
	  | (Z, _) => EPSNG ep_zero
	  (* Final case below will lead to [1,0] - i.e., empty *)
	  | _ => EPSNG ep_zero;

(* At last, interval division.  Note, we may return either a single
   interval or a pair of disjoint intervals.  In the latter case, the
   result of the division is the union of the two disjoint connected
   components. *)

datatype i_sd = ISNG of intvl | IDBL of intvl * intvl;

(* Exception for cardinality mismatch on interval division *)

exception I_DIV_CARD_MISMATCH;

fun divide ((i1, i2) : intvl * intvl) : i_sd =
    if (isEmpty(i1) orelse isEmpty(i2)) then ISNG EMPTY_INTVL else
    case (div_left_closed(i1, i2),
	  div_left_ep(i1, i2),
	  div_right_ep(i1, i2),
	  div_right_closed(i1, i2)) of
	(CLSNG lc, EPSNG l, EPSNG r, CLSNG rc) =>
	ISNG (mk_intvl (sel_bt_l(lc),
			l,
			r,
			sel_bt_r(rc)))
      | (CLDBL (lc1, lc2), EPDBL (l1, l2), EPDBL (r1, r2), CLDBL (rc1, rc2)) =>
      IDBL (mk_intvl (sel_bt_l(lc1),
		      l1,
		      r1,
		      sel_bt_r(rc1)),
	    mk_intvl (sel_bt_l(lc2),
		      l2,
		      r2,
		      sel_bt_r(rc2)))
      | _ => raise I_DIV_CARD_MISMATCH;

(* Determine if interval intersection should be left closed *)

fun intsct_left_closed ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	if ep_gt(l1, l2) then is_bt_cl(b1l) else
	if ep_lt(l1, l2) then is_bt_cl(b2l) else
	(is_bt_cl(b1l) andalso is_bt_cl(b2l));

(* Determine if interval intersection should be right closed *)

fun intsct_right_closed ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	if ep_lt(r1, r2) then is_bt_cr(b1r) else
	if ep_gt(r1, r2) then is_bt_cr(b2r) else
	(is_bt_cr(b1r) andalso is_bt_cr(b2r));

(* The entire real line: ]-inf, +inf[ *)

val REAL_LINE_INTVL =
    mk_intvl (RIGHT_CLOSED,
	      Infty(NEG_INFTY),
	      Infty(POS_INFTY),
	      LEFT_CLOSED);

(* Interval intersection *)

fun intsct ((i1, i2) : intvl * intvl) =
(*    if (i1 = REAL_LINE_INTVL) then i2
    else if (i2 = REAL_LINE_INTVL) then i1 else *)
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	if (isEmpty(i1) orelse isEmpty(i2)) then EMPTY_INTVL else
	if (not(ep_leq(l1, l2) andalso ep_leq(l2, r1))
	    andalso
	    not(ep_leq(l2, l1) andalso ep_leq(l1, r2)))
	then EMPTY_INTVL else
	mk_intvl (sel_bt_l(intsct_left_closed(i1, i2)),
		  ep_max(l1, l2),
		  ep_min(r1, r2),
		  sel_bt_r(intsct_right_closed(i1, i2)));

(* Interval union *)

fun union ((i1, i2) : intvl * intvl) =
(*    if (i1 = REAL_LINE_INTVL orelse i2 = REAL_LINE_INTVL) then
	REAL_LINE_INTVL else *)
    if isEmpty(i1) then i2
    else if isEmpty(i2) then i1 else
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (* left data *)
	    (if ep_lt(l1, l2) then (b1l, l1) else
	     if ep_gt(l1, l2) then (b2l, l2) else
	     (sel_bt_l(is_bt_cl(b1l) orelse is_bt_cl(b2l)), l1),
	     (* right data *)
	     if ep_gt(r1, r2) then (b1r, r1) else
	     if ep_lt(r1, r2) then (b2r, r2) else
	     (sel_bt_r(is_bt_cr(b1r) orelse is_bt_cr(b2r)), r1))
	 of ((btl, l), (btr, r)) => mk_intvl(btl, l, r, btr);

(* Division of intervals with unioned (single interval) result *)

fun u_div (i1, i2) =
    case divide(i1, i2) of
	ISNG i => i
      | IDBL (i, j) => union(i, j);

(* Negate an interval *)

fun neg (i as (bl, l, r, br) : intvl) =
    mk_intvl (bt_neg br,
	      ep_negate r,
	      ep_negate l,
	      bt_neg bl);

(* Construct a closed interval [a, b] from (a, b, c, d) *)

fun mk_closed_intvl (a, b) : intvl =
    mk_intvl (LEFT_CLOSED,
	      (Num a),
	      (Num b),
	      RIGHT_CLOSED);

(* Type of primitive constraints of the form
    ((V_1 op V_2) rl V_3)     -or-
     (V_1 rl V2). *)

datatype prim_rl = LT | LEQ | EQ | GEQ | GT;

type var_id = int;

type prim_2con_const_sh = var_id * prim_rl * Rat.rat;

type prim_2con_sh = var_id * prim_rl * var_id;

type prim_3con_sh = var_id * var_id * prim_rl * var_id;

datatype prim_con = Sum of prim_3con_sh
		  | Diff of prim_3con_sh
		  | Prod of prim_3con_sh
                  | Bin of prim_2con_sh
		  | BinConst of prim_2con_const_sh;

(* Convert primitive relation to a string *)

fun pr_to_string (pr) =
  case pr of EQ => "="
	   | GEQ => ">="
	   | GT => ">"
	   | LEQ => "<="
	   | LT => "<";

(* Convert a PC to a string *)

fun pc_to_string (pc) =
    case pc of
	Sum (v1, v2, r, v3) =>
	"v" ^ Int.toString(v1) ^ " + v" ^ Int.toString(v2) ^ " "
	^ pr_to_string(r) ^ " v" ^ Int.toString(v3)
      | Diff (v1, v2, r, v3) =>
	"v" ^ Int.toString(v1) ^ " - v" ^ Int.toString(v2) ^ " "
	^ pr_to_string(r) ^ " v" ^ Int.toString(v3)
      | Prod (v1, v2, r, v3) =>
	"v" ^ Int.toString(v1) ^ " * v" ^ Int.toString(v2) ^ " "
	^ pr_to_string(r) ^ " v" ^ Int.toString(v3)
      | Bin (v1, r, v2) =>
	"v" ^ Int.toString(v1) ^ " " ^ pr_to_string(r) ^ " v"
	^ Int.toString(v2)
      | BinConst(v1, r, q) =>
	"v" ^ Int.toString(v1) ^ " " ^ pr_to_string(r) ^ " "
	^ Rat.toString(q);

(* Exception for var_id |-> intvl Interval context hash table,
   raised by Polyhash.find if var_id is not found in the context.
   As it turns out, this exception will not be raised, as we use
   Polyhash.peek instead of Polyhash.find.  Still, it is required
   when constructing the hash table. *)

exception IC_VAR_NOT_FOUND;

(* Interval context type *)

type intvl_ctxt = (var_id, intvl) Polyhash.hash_table;

(* Make an interval context hash table of size n (can grow later) *)

fun mk_intvl_ctxt n : intvl_ctxt =
    Polyhash.mkTable (fn x : var_id => x, fn (x : var_id, y : var_id) => x = y)
		     (n, IC_VAR_NOT_FOUND);

(* Given an IC and a variable id v, get v's bound from IC, returning
   ]-inf, +inf[ if no constraints upon it are known. *)

fun get_i_from_ic (ic : intvl_ctxt, v : var_id) =
    case Polyhash.peek ic v of
	SOME b => b
      | NONE => REAL_LINE_INTVL;

(* Exception signaling if the IC contains an empty interval *)

exception EMPTY_INTVL_IN_IC;

(* Printing functions for ICs, TCs and PCs,
   beginning with conversion of IC to a list *)

fun ic_lst (ic : intvl_ctxt) = Polyhash.listItems(ic);

(* Print the contents of an IC *)

fun print_ic (ic : intvl_ctxt) =
    (app (fn (v, i) =>
	     (if !traceb then trace(1, "\n v" ^ Int.toString(v) ^ " in " ^ intvl_toString(i) ^ ".")
	      else ()))
	 (ic_lst(ic));
     if !traceb then trace(1,"\n") else ());

(* Given an IC, a variable id v and an interval I containing v,
   update v's bound in IC with the intersection of IC(v) and I.
   Note that we return true iff the IC was modified, i.e., the
   interval for v was narrowed. *)

fun update_ic (ic : intvl_ctxt, v : var_id, i : intvl) =
    let val old_i = get_i_from_ic(ic, v) in
	if not(eq(old_i, i)) then
	    let val new_i = intsct(old_i, i) in
		if not(eq(old_i, new_i)) then
		    (Polyhash.insert ic (v, new_i);
		     if !traceb then trace(2, "\n IC(v" ^ Int.toString(v) ^ ") := " ^ intvl_toString(new_i) ^ ".")
		     else ();
		     if isEmpty(new_i) then raise EMPTY_INTVL_IN_IC else true)
		else false
	    end
	else false
    end;

(* Reset interval binding for a given var_id *)

fun reset_ic (ic : intvl_ctxt, v : var_id) =
    Polyhash.insert ic (v, REAL_LINE_INTVL);

(* Narrow IC(V) given V = X s.t. X in I.
   Note that the intersection of old and new bounds is implicit,
   as update_ic takes care of this automatically. *)

fun narrow_eq (ic, v, i) = update_ic(ic, v, i);

(* Narrow IC(V) given V >= X s.t. X in I;
   Effectively rule GE-1 in my thesis. *)

fun narrow_geq (ic, v, i as (b1q, lq, rq, b2q) : intvl) =
    update_ic(ic, v, mk_intvl(b1q,
			      lq,
			      Infty POS_INFTY,
			      LEFT_CLOSED));

(* Narrow IC given V_1 > X s.t. X in I;
   Effectively rule G-1 in my thesis. *)

fun narrow_gt (ic, v, i as (b1q, lq, rq, b2q) : intvl) =
    update_ic(ic, v, mk_intvl(RIGHT_CLOSED,
			      lq,
			      Infty POS_INFTY,
			      LEFT_CLOSED));

(* Narrow IC given V_1 < X s.t. X in I;
   Effectively rule G-2 in my thesis. *)

fun narrow_lt (ic, v, i as (b1p, lp, rp, b2p) : intvl) =
    update_ic(ic, v, mk_intvl(RIGHT_CLOSED,
			      Infty NEG_INFTY,
			      rp,
			      LEFT_CLOSED));

(* Narrow IC given V_1 <= X s.t. X in I;
   Effectively rule GE-2 in my thesis. *)

fun narrow_leq (ic, v, i as (b1p, lp, rp, b2p) : intvl) =
    update_ic(ic, v, mk_intvl(RIGHT_CLOSED,
			      Infty NEG_INFTY,
			      rp,
			      b2p));

(* Generic Sum narrowing functional.
   Example: v1 + v2 >= v3, then

    v1 >= v3 - v2,
    v2 >= v3 - v1,
    v3 <= v1 + v2.

   In this case, >= corresponds to the narrowing required
   for the main relation (narrow_fun0), and <= corresponds
   to the narrowing required for its opposite (narrow_fun1). *)

type nf = intvl_ctxt * var_id * intvl -> bool;

fun narrow_sum_generic (ic, pc, narrow_fun0 : nf, narrow_fun1 : nf) =
    case pc of
	Sum (v1, v2, _, v3) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	    val old_i_v2 = get_i_from_ic(ic, v2)
	    val old_i_v3 = get_i_from_ic(ic, v3)
	in let val progress0 = narrow_fun0(ic, v1, sub(old_i_v3, old_i_v2))
	       val progress1 = narrow_fun0(ic, v2, sub(old_i_v3, old_i_v1))
	       val progress2 = narrow_fun1(ic, v3, add(old_i_v1, old_i_v2))
	   in progress0 orelse progress1 orelse progress2
	   end
	end
      | _ => false;

(* Select NF narrow function pair from relation *)

fun sel_nf(r : prim_rl) =
    case r of EQ => (narrow_eq, narrow_eq)
	    | GEQ => (narrow_geq, narrow_leq)
	    | GT => (narrow_gt, narrow_lt)
	    | LT => (narrow_lt, narrow_gt)
	    | LEQ => (narrow_leq, narrow_geq);

(* Narrow IC given a Sum primitive constraint *)

fun narrow_sum (ic, pc) =
    case pc of
	Sum (_, _, r, _) =>
	let val (narrow_fun0, narrow_fun1) = sel_nf(r)
	in narrow_sum_generic(ic, pc, narrow_fun0, narrow_fun1)
	end
      | _ => false;

(* Generic Diff narrowing functional.
   Example: v1 - v2 >= v3, then

    v1 >= v3 + v2,
    v2 >= v3 + v1,
    v3 <= v1 - v2.

   In this case, >= corresponds to the narrowing required
   for the main relation (narrow_fun0), and <= corresponds
   to the narrowing required for its opposite (narrow_fun1). *)

fun narrow_diff_generic (ic, pc, narrow_fun0 : nf, narrow_fun1 : nf) =
    case pc of
	Diff (v1, v2, _, v3) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	    val old_i_v2 = get_i_from_ic(ic, v2)
	    val old_i_v3 = get_i_from_ic(ic, v3)
	in let val progress0 = narrow_fun0(ic, v1, add(old_i_v3, old_i_v2))
	       val progress1 = narrow_fun0(ic, v2, neg(sub(old_i_v3, old_i_v1)))
	       val progress2 = narrow_fun1(ic, v3, sub(old_i_v1, old_i_v2))
	   in progress0 orelse progress1 orelse progress2
	   end
	end
      | _ => false;

(* Narrow IC given a Diff primitive constraint *)

fun narrow_diff (ic, pc) =
    case pc of
	Diff (_, _, r, _) =>
	let val (narrow_fun0, narrow_fun1) = sel_nf(r)
	in narrow_diff_generic(ic, pc, narrow_fun0, narrow_fun1)
	end
      | _ => false;

(* PSD interval *)

val PSD_INTVL = mk_intvl(LEFT_CLOSED,
			 Num 0.0,
			 Infty POS_INFTY,
			 LEFT_CLOSED);

val NSD_INTVL = mk_intvl(RIGHT_CLOSED,
			 Infty NEG_INFTY,
			 Num 0.0,
			 RIGHT_CLOSED);

(* Compute interval sqrt.  We compute the sqrt of the interval i, but
   we use the second interval b to determine whether or not we can
   narrow the result to be around one of the roots (either NEG or POS).

   For example, if b is [0, +inf[ and i is [-1, 2], then we can return
    [outward<round(sqrt 2), outward>round(sqrt 2)],

   while if b is ]-inf, 0] then we can return
    [-outward>round(sqrt 2), -outward<round(sqrt 2)].

   But, if b is ]-inf, +inf[, then we will have to return an interval
   containing both the positive and negative sqrts of 2, i.e.,
    [-outward>round(sqrt 2), outward>round(sqrt 2)]. *)

fun sqrt(i : intvl, b : intvl) =
    let val i' = intsct(i, PSD_INTVL) in
	if isEmpty(i') then EMPTY_INTVL else
	let val prevRM = IEEEReal.getRoundingMode()
	in
	    case i' of
		(_, Num l, Num r, _) =>
		let val sqrt_l = (set_rm(LO);
				  Math.sqrt(l))
		    val sqrt_r = (set_rm(HI);
				  Math.sqrt(r))
		in
		    (IEEEReal.setRoundingMode(prevRM);
		     case m_classify(b) of
			 P => mk_closed_intvl(sqrt_l, sqrt_r)
		       | N => mk_closed_intvl(~(sqrt_r), ~(sqrt_l))
		       | _ => mk_closed_intvl(~(sqrt_r), sqrt_r))
		end
	      | (lbt, Num l, Infty POS_INFTY, _) =>
		let val sqrt_l = (set_rm(LO);
				  Math.sqrt(l))
		in
		    (IEEEReal.setRoundingMode(prevRM);
		     case m_classify(b) of
			 P => mk_intvl(lbt,
				       Num sqrt_l,
				       Infty POS_INFTY,
				       LEFT_CLOSED)
		       | N => mk_intvl(RIGHT_CLOSED,
				       Infty NEG_INFTY,
				       Num (~sqrt_l),
				       if lbt = LEFT_CLOSED then
					   RIGHT_CLOSED else
				       LEFT_CLOSED)
		       | _ => REAL_LINE_INTVL)
		end
	      | _ => REAL_LINE_INTVL
	end
    end;

(* Generic Prod narrowing functional.

   Example: v1 * v2 >= v3, then, if v1 and v2 are PSD, we have

   v1 >= v3/v2,
   v2 >= v3/v1
   v3 <= v1*v2.

   with >=, <= corresponding to narrow_fun0, narrow_fun1.

   If v2 was NSD but v1 was PSD, then we would have

   v1 <= v2/v2,
   v2 >= v3/v1
   v3 <= v1*v2

  * We add a simple optimisation for when the constraint
    is of the form Prod(v1, v1 , _ , _).  In this case, we
    can intersect mult(IC(v1), IC(v1)) with [0, +inf[.

  If we have v1 * v2 = v3 and v1 = v2, then we can also compute (to
   intersect with I(v1) the interval sqrt of v3.  We do this.  We also
   optimise it to be an interval containing only a single sqrt if the
   current sign assumptions warrant this.

  We also include now the following rules (11-July-2011):

   * Note that sqrt(x) returns an interval containing *both* positive
     and negative square-roots of x, unless it can prove that only one
     of them is required.

   New rules:

    v1*v2 >= v3,   v1 = v2,   v1 >= 0
    ---------------------------------
    v1 >= sqrt(v3)

    v1*v2 >= v3,   v1 = v2,   v1 <= 0
    ---------------------------------
    v1 <= sqrt(v3)
*)

fun narrow_prod_generic (ic, pc, narrow_fun0 : nf, narrow_fun1 : nf) =
    case pc of
	Prod (v1, v2, _, v3) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	    val old_i_v2 = get_i_from_ic(ic, v2)
	    val old_i_v3 = get_i_from_ic(ic, v3)
	    val progress0 = ref false
	    val progress1 = ref false
	    val progress2 = ref false
	    val progress3 = ref false
	    val progress4 = ref false
	in
	    (case (m_classify(old_i_v1), m_classify(old_i_v2)) of
		 (P, P) => (progress0 := narrow_fun0(ic, v1, u_div(old_i_v3, old_i_v2));
			    progress1 := narrow_fun0(ic, v2, u_div(old_i_v3, old_i_v1)))
	       | (N, N) => (progress0 := narrow_fun1(ic, v1, u_div(old_i_v3, old_i_v2));
			    progress1 := narrow_fun1(ic, v2, u_div(old_i_v3, old_i_v1)))
	       | (P, N) => (progress0 := narrow_fun1(ic, v1, u_div(old_i_v3, old_i_v2));
			    progress1 := narrow_fun0(ic, v2, u_div(old_i_v3, old_i_v1)))
	       | (N, P) => (progress0 := narrow_fun0(ic, v1, u_div(old_i_v3, old_i_v2));
			    progress1 := narrow_fun1(ic, v2, u_div(old_i_v3, old_i_v1)))
	       | _ => ();
	     (* Now, narrow v3 (we've only narrowed v1, v2 above). *)
	     case (v1 = v2) of
		 true =>
		 (progress2 := narrow_fun1(ic, v3, intsct(mult(old_i_v1, old_i_v1),
							  mk_intvl(LEFT_CLOSED,
								   ep_zero,
								   Infty POS_INFTY,
								   LEFT_CLOSED)));
		  case pc of Prod (_, _, EQ, _) =>
			     let val new_i_v3 = get_i_from_ic(ic, v3)
				 val new_i_v1 = get_i_from_ic(ic, v1) in
				 case new_i_v3 of
				     (_, Num _, _, _) =>
				     progress3 := narrow_fun0(ic, v1, sqrt(new_i_v3, new_i_v1))
				   | (_, _, Num _, _) =>
				     progress3 := narrow_fun0(ic, v1, sqrt(new_i_v3, new_i_v1))
				   | _ => ()
			     end
			   | Prod (_, _, GEQ, _) =>
			     let val new_i_v3 = get_i_from_ic(ic, v3)
				 val new_i_v1 = get_i_from_ic(ic, v1) in
				 case (new_i_v3, m_classify(new_i_v1)) of
				     ((_, Num _, _, _), P) =>
				     progress4 := narrow_fun0(ic, v1, sqrt(new_i_v3, new_i_v1))
				   | ((_, Num _, _, _), Z) =>
				     progress4 := narrow_fun0(ic, v1, sqrt(new_i_v3, new_i_v1))
				   | _ => ()
			     end
			   | _ => ())
	       | false => progress2 := narrow_fun1(ic, v3, mult(old_i_v1, old_i_v2));
	     (* Now, return boolean specifying whether or not an interval was narrowed. *)
	     !progress0 orelse !progress1 orelse !progress2 orelse !progress3 orelse !progress4)
	end
      | _ => false;

(* Narrow IC given a Prod primitive constraint *)

fun narrow_prod (ic, pc) =
    case pc of
	Prod (_, _, r, _) =>
	let val (narrow_fun0, narrow_fun1) = sel_nf(r)
	in narrow_prod_generic(ic, pc, narrow_fun0, narrow_fun1)
	end
      | _ => false;

(* Make an interval containing a rational constant.  Note that as our
   endpoints are floating points, we need to deal properly with
   rounding here. *)

exception BAD_FP_ROUNDING_MODE of string;

fun min_lst([], c : real) = c
  | min_lst(r :: rs, c) =
    if (r < c) then min_lst(rs, r) else
    min_lst(rs, c);

fun min (r :: rs) = min_lst (rs, r);

fun max_lst([], c : real) = c
  | max_lst(r :: rs, c) =
    if (r > c) then max_lst(rs, r) else
    max_lst(rs, c);

fun max (r :: rs) = max_lst (rs, r);

(* Convert exact rational to floating point lowerbound.  Note that an
   exact rational is negative iff its denominator is negative. *)

fun rat_to_fp_lo (q) =
  let val (num, den) = Rat.quotient_of_rat(q)
  in
    case IntInf.compare(num,0) of
	EQUAL => 0.0
      | GREATER =>
	    let val num_lo = (set_rm(LO); Real.fromLargeInt(num))
		val den_hi = (set_rm(HI); Real.fromLargeInt(den))
	    in
		(set_rm(LO); (num_lo / den_hi))
	    end
      | LESS =>
	  let val num_hi = (set_rm(HI); Real.fromLargeInt(~num))
	      val den_lo = (set_rm(LO); Real.fromLargeInt(den))
	  in
	      (set_rm(HI);
	       let val quot = (num_hi / den_lo) in
		   (set_rm(LO); ~quot)
	       end)
	  end
  end;

fun rat_to_fp_hi (q) =
  let val (num, den) = Rat.quotient_of_rat(q)
  in
    case IntInf.compare(num,0) of
	EQUAL => 0.0
      | GREATER =>
	    let val num_hi = (set_rm(HI); Real.fromLargeInt(num))
		val den_lo = (set_rm(LO); Real.fromLargeInt(den))
	    in
		(set_rm(HI); (num_hi / den_lo))
	    end
      | LESS =>
	  let val num_lo = (set_rm(LO); Real.fromLargeInt(~num))
	      val den_hi = (set_rm(HI); Real.fromLargeInt(den))
	  in
	      (set_rm(LO);
	       let val quot = (num_lo / den_hi) in
		   (set_rm(HI); ~quot)
	       end)
	  end
  end;


(* local open FPBound in *)

fun mk_intvl_for_rat_const (q : Rat.rat) =
    (let val prevRM = IEEEReal.getRoundingMode()
     in
	 let val (q_lo, q_hi) = (rat_to_fp_lo q,
				 rat_to_fp_hi q)
	 in
	     let val result =
		     if (Real.==(q_lo, q_hi)) then
			 mk_closed_intvl(q_lo, q_hi)
		     else if (q_lo < q_hi) then
			 (* Still, we may have q = Q(q_lo) or q = Q(q_hi),
			    so we use a closed interval for now to be safe. *)
			 mk_closed_intvl(q_lo, q_hi)
		     else if (q_lo > q_hi) then
			 raise BAD_FP_ROUNDING_MODE
				   ("Bit-large rational: " ^ Rat.toString(q))
		     else raise BAD_FP_ROUNDING_MODE "Incomparable?"
	     in (IEEEReal.setRoundingMode(prevRM);
		 result)
	     end
	 end
     end);

(* Generic Bin narrowing functional.

   Example: v1 >= v2.
   Then, we narrow via:
     v1 >= v2,
     v2 <= v1.

   In this case, narrow_fun0 corresponds to >= and narrow_fun1 to <=. *)

fun narrow_bin_generic (ic, pc, narrow_fun0 : nf, narrow_fun1 : nf) =
    case pc of
	Bin (v1, _, v2) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	    val old_i_v2 = get_i_from_ic(ic, v2)
	in let val progress0 = narrow_fun0(ic, v1, old_i_v2)
	       val progress1 = narrow_fun1(ic, v2, old_i_v1)
	   in progress0 orelse progress1
	   end
	end
      | BinConst(v1, _, q) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	in narrow_fun0(ic, v1, mk_intvl_for_rat_const(q))
	end
      | _ => false;

(* Narrow IC given a Bin primitive constraint *)

fun narrow_bin (ic, pc) =
    case pc of
	Bin (_, r, _) =>
	let val (narrow_fun0, narrow_fun1) = sel_nf(r)
	in narrow_bin_generic(ic, pc, narrow_fun0, narrow_fun1)
	end
      | BinConst (_, r, _) =>
	let val (narrow_fun0, narrow_fun1) = sel_nf(r)
	in narrow_bin_generic(ic, pc, narrow_fun0, narrow_fun1)
	end
      | _ => false;

(* Auxiliary function for icp_pcl below *)

fun icp_pcl_prog(ic, pcl, as_only, progress_made) =
    case pcl of [] => progress_made
	      | (pc::pcs) =>
		let val progress =
			(case pc of
			     Sum _ => narrow_sum(ic, pc)
			   | Diff _ => narrow_diff(ic, pc)
			   | Prod _ => if not as_only then narrow_prod(ic, pc) else false
			   | Bin _ => narrow_bin(ic, pc)
			   | BinConst _ => narrow_bin(ic, pc))
			handle EMPTY_INTVL_IN_IC =>
			       (if !traceb then trace(2, "-- IC narrowed via " ^ pc_to_string(pc) ^ ".")
				else ();
				raise EMPTY_INTVL_IN_IC)
		in (if progress then
			(if !traceb then trace(2, "-- IC narrowed via " ^ pc_to_string(pc) ^ ".")
			 else ();
			 ())
		    else ();
		    icp_pcl_prog(ic, pcs, as_only, progress_made orelse progress))
		end;

(* Perform interval constraint propagation upon an IC w.r.t.
   a list of primitive constraints.

   This is a ``single pass'' which returns true iff the pass
   narrowed an interval in IC.  We will later iterate icp_pcl
   until a fixed point is reach, i.e., until the return value
   of icp_pcl is false.

   The parameter as_only is used to determine if we should
   only contract on addition and substraction constraints. *)

fun icp_pcl(ic, pcl : prim_con list, as_only) =
    icp_pcl_prog(ic, pcl, as_only, false);

(* Auxiliary function for fixed_pt_icp_pcl below *)

fun fixed_pt_icp_pcl_prog(ic, pcl, clim, aslim, count, progress_made) =
    let val as_only = (count >= aslim)
	val progress = icp_pcl(ic, pcl, as_only)
    in
	if (progress andalso (count <= clim)) then
	    (if !traceb then print_ic(ic) else ();
	     fixed_pt_icp_pcl_prog(ic, pcl, clim, aslim, count+1, true))
	else progress_made
    end;

(* Given an IC and PCL, keep narrowing IC w.r.t. PCL until a
   fixed point is reached, or a contraction limit is reached.

   We return true iff any pass made progress. *)

fun fixed_pt_icp_pcl(ic, pcl, clim, aslim) =
    fixed_pt_icp_pcl_prog(ic, pcl, clim, aslim, 0, false);

(* Given an IC and a list of variable IDs SVS, return the member
   of SVS whose width is the widest.  If there is a tie, we just
   pick one based upon the order in SVS. *)

exception BAD_VAR_SPLIT_LIST of string;

fun sel_widest' (ic : intvl_ctxt, [], (c, d)) = c
  | sel_widest' (ic, s :: rst, (c, d)) =
    let val diff = case Polyhash.peek ic s of
		       SOME (btl, l, r, btr) => ep_sub(r, l, HI)
		     | NONE => Infty POS_INFTY
    in
	if (ep_gt(diff, d)) then sel_widest'(ic, rst, (s, diff))
	else sel_widest'(ic, rst, (c, d))
    end;

fun sel_widest (ic, []) = NONE
  | sel_widest (ic, s :: rst) =
    case Polyhash.peek ic s of
	SOME (btl, l, r, btr) =>
	SOME (sel_widest' (ic, rst, (s, (ep_sub(r, l, HI)))))
      | NONE => SOME (sel_widest' (ic, rst, (s, Infty POS_INFTY)));

(* Given an IC and a list of variable IDs SVS, return the member
   of SVS whose width is the smallest (non-zero).  If there is a tie,
   we just pick one based upon the order in SVS. *)

fun sel_smallest' (ic : intvl_ctxt, [], (c, d)) = c
  | sel_smallest' (ic, s :: rst, (c, d)) =
    let val diff = case Polyhash.peek ic s of
		       SOME (btl, l, r, btr) => ep_sub(r, l, HI)
		     | NONE => Infty POS_INFTY
    in
	if (not(ep_eq(diff, ep_zero)) andalso
	    (ep_lt(diff, d) orelse (ep_eq(d, ep_zero))))
	then sel_smallest'(ic, rst, (s, diff))
	else sel_smallest'(ic, rst, (c, d))
    end;

fun sel_smallest (ic, []) = NONE
  | sel_smallest (ic, s :: rst) =
    case Polyhash.peek ic s of
	SOME (btl, l, r, btr) =>
	SOME (sel_smallest' (ic, rst, (s, (ep_sub(r, l, HI)))))
      | NONE => SOME (sel_smallest' (ic, rst, (s, Infty POS_INFTY)));

(* Given an IC and a var_id for splitting, return two new ICs obtained
    by splitting IC at IC(var_id)'s midpoint.

   Note that it may happen that in the process of setting up the new
    interval contexts arising through splitting, these new ICs may be
    recognised to contain empty intervals.  If that's the case, then
    we can throw them away a priori.  We use the split_att datatype
    below to handle this. *)

datatype split_att = S_TWO of intvl_ctxt * intvl_ctxt
		   | S_ONE of intvl_ctxt
		   | S_NONE;

(* Exception to be raised if a variable cannot be split because
   it is bound within an interval of the form [Num a, Num a], i.e.,
   an interval with only one point. *)

exception ONE_PT_NO_SPLIT;

fun split_ic (ic, split_vid) =
    let val ic_1 = Polyhash.copy ic
	val ic_2 = Polyhash.copy ic
	val split_intvl = case Polyhash.peek ic split_vid of
			      SOME i => i
			    | NONE => REAL_LINE_INTVL
	val ic_1_empty = ref false
	val ic_2_empty = ref false
    in let val split_pt =
	       case split_intvl of
		   (btl, Num l, Num r, btr) =>
		   if (r>l) then ((l + r) / 2.0) else raise ONE_PT_NO_SPLIT
		 | (btl, Infty NEG_INFTY, Num r, btr) => r - 1.0
		 | (btl, Num l, Infty POS_INFTY, btr) => l + 1.0
		 | (btl, Infty NEG_INFTY, Infty POS_INFTY, btr) => 0.0
	     in (if !traceb then trace(1, " *** Splitting point(var_id=" ^ Int.toString(split_vid) ^ "): "
					  ^ real_to_string(split_pt) ^ "  .\n")
		 else ();
		 update_ic(ic_1, split_vid, mk_intvl(RIGHT_CLOSED,
						     Infty NEG_INFTY,
						     Num split_pt,
						     RIGHT_CLOSED))
		 handle EMPTY_INTVL_IN_IC => ((ic_1_empty := true); true);
		 update_ic(ic_2, split_vid, mk_intvl(LEFT_CLOSED,
						     Num split_pt,
						     Infty POS_INFTY,
						     LEFT_CLOSED))
		 handle EMPTY_INTVL_IN_IC => ((ic_2_empty := true); true);
		 if not(!ic_1_empty orelse !ic_2_empty) then S_TWO (ic_1, ic_2)
		 else if (!ic_1_empty andalso !ic_2_empty) then S_NONE
		 else if !ic_1_empty then S_ONE ic_2
		 else S_ONE ic_1)
       end
    end;

(* Rotate a list -- Used to do round-robin variable splitting *)

fun rotate [] = []
  | rotate (h :: t) = t @ [h];

(* Given an IC and PCL, a limit and a list of variable ids for branch
    and prune splitting, perform branch and prune ICP search.

    CLimit: contract limit,
    SLimit: interval splitting limit,
    ASLimit: restriction to addition and subtraction narrowing limit.

   We only do binary splits at the moment. It'd be interesting
    to non-binary splits in the future! *)

fun branch_and_prune(ic, pcl, svs, clim, slim, aslim) =
    let val prune = ref false
	val result = (fixed_pt_icp_pcl(ic, pcl, clim, aslim)
		      handle EMPTY_INTVL_IN_IC => (prune := true; true));
    in
	if !prune then [] else
	if (slim <= 0) then [ic] else
	(* Can either select widest or smallest interval for splitting *)
	let val split_vid = case sel_smallest(ic, svs) of
				SOME vid => vid
			      | _ => raise BAD_VAR_SPLIT_LIST "in branch_and_prune"
	    val _ = if !traceb then trace(1, "\n *** Splitting on v" ^ Int.toString(split_vid)
					     ^ " -- cur_slim = " ^ Int.toString(slim) ^ ".\n")
		    else ();
	    val svs' = rotate svs
	    val split_result = split_ic(ic, split_vid)
		handle ONE_PT_NO_SPLIT => S_ONE ic
	in case split_result of
	       S_TWO (new_ic_1, new_ic_2) =>
	       (branch_and_prune(new_ic_1, pcl, svs', clim, slim - 1, aslim)
		@ branch_and_prune(new_ic_2, pcl, svs', clim, slim - 1, aslim))
	     | S_ONE new_ic => branch_and_prune(new_ic, pcl, svs', clim, slim - 1, aslim)
	     | S_NONE => []
	end
    end;

(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)
(*             Begin RCF formula -> Interval techniques machinery            *)
(* ::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::: *)

(* Context type for storing mappings from rcf_tm to IC var_ids. The
    number of items in the hash table is used to determine the next
    free var_id for assignment. *)

type tmv_ctxt = (Term.term, var_id) Polyhash.hash_table;

(* Exception for term not found in tmv_ctxt *)

exception TM_NOT_FOUND_IN_TC;

(* Make a tmv_ctxt hash table *)

fun mk_tmv_ctxt n = Polyhash.mkTable(Word.toIntX o (fn x => Term.hashw(x, 0w0)),
				     (Useful.uncurry Term.equal))
				    (n, TM_NOT_FOUND_IN_TC) : tmv_ctxt;

(* Given an RCF term tm, associate tm with a var_id in tmv_ht, deriving
   additional primitive constraints between introduced new variables if
   necessary.

   If tm is already in tmv_ht, we return its associated var_id and an
   empty list of additional primitive constraints.  If tm is not in
   tmv_ht, then we recursively add it to tmv_ht, update the max var_id
   of the tmv_ctxt, and return also a list of additional primitive
   constraints derived from the new association. *)

exception BAD_TERM of string;

fun tm_var_id_and_pcs(tc : tmv_ctxt, tm : Term.term) : var_id * prim_con list =
    case (Polyhash.peek tc tm) of
	NONE =>
	(case tm of
	     (* Note that our ``variables'' for ICP are Skolem constants *)
	     (Term.Fn (f, [])) => let val new_var_id = Polyhash.numItems tc
				  in (Polyhash.insert tc (tm, new_var_id);
				      (new_var_id, []))
				  end
	   | (Term.Rat q) => let val new_var_id = Polyhash.numItems tc
			     in (Polyhash.insert tc (tm, new_var_id);
				 (new_var_id, [BinConst (new_var_id, EQ, q)]))
			     end
	   | (Term.Fn (f, [p1, p2])) =>
	     (case (tm_var_id_and_pcs(tc, p1), tm_var_id_and_pcs(tc, p2)) of
	   	  ((p1_var_id, p1_new_pcs), (p2_var_id, p2_new_pcs))
	   	  =>
	   	  let val new_var_id = Polyhash.numItems tc
	   	  in (case f of
	   		  "+" => (Polyhash.insert tc (tm, new_var_id);
	   			  (new_var_id,
	   			   List.concat
	   			       [p1_new_pcs, p2_new_pcs,
	   				[Sum (p1_var_id,
	   				      p2_var_id,
	   				      EQ,
	   				      new_var_id)]]))
	   		| "-" => (Polyhash.insert tc (tm, new_var_id);
	   			  (new_var_id,
	   			   List.concat
	   			       [p1_new_pcs, p2_new_pcs,
	   				[Diff (p1_var_id,
	   				       p2_var_id,
	   				       EQ,
	   				       new_var_id)]]))
			| "*" => (Polyhash.insert tc (tm, new_var_id);
				  (new_var_id,
				   List.concat
				       [p1_new_pcs, p2_new_pcs,
					[Prod (p1_var_id,
					       p2_var_id,
					       EQ,
					       new_var_id)]]))
			| _ => raise BAD_TERM (Term.toString tm))
		  end)
	   | (Term.Fn ("-", [p])) =>
	     let val (z_vid, z_pc) =
		     tm_var_id_and_pcs(tc, Term.Rat (Rat.rat_of_int 0))
		 val (p_vid, p_pc) =
		     tm_var_id_and_pcs(tc, p)
		 val new_var_id = Polyhash.numItems tc in
		 (Polyhash.insert tc (tm, new_var_id);
		  (new_var_id,
		   List.concat
		   [z_pc, p_pc,
		    [Diff(z_vid, p_vid, EQ, new_var_id)]]))
	     end
	   | _ => raise BAD_TERM (Term.toString tm))
      | SOME v => (v, []);

(* Convert an RCF atom into a list of primitive interval constraints.
   We also update the given tmv_ctxt, tc, in place.  This is so that
   it can be re-used later, when we are processing a list of atoms. *)

fun atom_to_pcl(tc : tmv_ctxt, a : Atom.atom) =
    case a of
	(r, [p1, p2]) =>
	(case (tm_var_id_and_pcs(tc, p1), (tm_var_id_and_pcs(tc, p2))) of
	     ((p1_var_id, p1_new_pcs), (p2_var_id, p2_new_pcs))
	     => let val new_a_pc =
			(case r of
			     "=" => Bin (p1_var_id, EQ, p2_var_id)
			   | ">=" => Bin (p1_var_id, GEQ, p2_var_id)
			   | "<=" => Bin (p1_var_id, LEQ, p2_var_id)
			   | ">" => Bin (p1_var_id, GT, p2_var_id)
			   | "<" => Bin (p1_var_id, LT, p2_var_id))
		in List.concat [p1_new_pcs, p2_new_pcs, [new_a_pc]]
		end);

(* Convert TC to a list *)

fun tc_lst (tc : tmv_ctxt) = Polyhash.listItems(tc);

(* Given a TC, extract the vid's of the RCF variables from it *)

fun tc_rcf_vids' ([] : (Term.term * var_id) list) = []
  | tc_rcf_vids' ((Term.Fn(str, []), vid) :: rst) = vid :: tc_rcf_vids'(rst)
  | tc_rcf_vids' (_ :: rst) = tc_rcf_vids'(rst);

fun tc_rcf_vids (tc : tmv_ctxt) = tc_rcf_vids'(tc_lst tc);

(* Given a TC, extract the (str . var_id) pairs for RCF variables *)

fun tc_rcf_svid_pairs' ([] : (Term.term * var_id) list) = []
  | tc_rcf_svid_pairs' ((Term.Fn(str, []), vid) :: rst) = (str, vid) :: tc_rcf_svid_pairs'(rst)
  | tc_rcf_svid_pairs' (_ :: rst) = tc_rcf_svid_pairs'(rst);

fun tc_rcf_svid_pairs (tc : tmv_ctxt) = tc_rcf_svid_pairs'(tc_lst tc);


(* Print the contents of a TC *)

fun print_tc (tc : tmv_ctxt) =
    (trace(1,"Term hashing:");
     app (fn (t, v) =>
	     (trace(1, "\n " ^ Term.toString(t) ^ " |-> v" ^ Int.toString(v) ^ ".")))
	 (tc_lst(tc));
     trace(1,"\n");
     trace(1, "\nRCF var-ids:");
     app (fn (v) => trace(1, " v" ^ Int.toString(v) ^ " "))
	 (tc_rcf_vids(tc)));

(* Convert a list of RCF atoms into a list of primitive interval constraints *)

fun al_to_pcl(al : Atom.atom list) =
    let val tc = mk_tmv_ctxt(List.length(al) * 100) (* Size can grow as needed *)
    in let val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
       in (if !traceb then print_tc(tc) else (); pcl)
       end
    end;

(* Type for ICP return values *)

datatype icp_r = ICP_NO_PROGRESS | ICP_PROGRESS | ICP_EMPTY;

(*
(* Given a list of primitive constraints, run ICP upon them *)

fun icp_on_pcl(pcl, limit) =
    let val ic = mk_intvl_ctxt 7000 in
	(if fixed_pt_icp_pcl(ic, pcl, limit)
	 then ICP_PROGRESS else ICP_NO_PROGRESS)
	handle EMPTY_INTVL_IN_IC =>
	       (if !traceb then
		    trace(1, "\n .:. Empty interval found. \n\n ICP result:\n")
		else ();
		print_ic(ic);
		ICP_EMPTY)
    end;

(* Given a list of atoms, run ICP upon them *)

fun icp_on_al(al, limit) =
    let val pcl = al_to_pcl(al) in
	(if !traceb then trace(1, "\nAtoms:") else ();
	 app (fn x => trace(1, " " ^ Atom.toString(x))) al;
	 if !traceb then trace(1, "\n\nPrimitive constraints:") else ();
	 app (fn x => trace(1, " " ^ pc_to_string(x) ^ "\n")) pcl;
	 icp_on_pcl(pcl, limit))
    end;

*)

(* Branch and prune on AL *)

datatype bap_r = BAP_EMPTY | BAP_RESULT of intvl_ctxt list | BAP_NO_PROGRESS;

fun bap_on_al(al, clim, slim, aslim) =
    let val ic = mk_intvl_ctxt 7000
	val tc = mk_tmv_ctxt(List.length(al) * 100)
	val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
    in (if !traceb then print_tc(tc) else ();
	let val result = branch_and_prune(ic, pcl, tc_rcf_vids(tc), clim, slim, aslim)
	in if List.null(result) then
	       BAP_EMPTY else
	   BAP_RESULT result end)
    end;

(* Given an RCF atom and a mapping of Skolem constants to rationals,
   evaluate the truth of the atom under the substitution mapping.
   Note that we can use floating point numbers here, as a judgment
   of SAT will only cause MetiTarski to skip some inferences, and
   even if rounding caused an incorrect SAT judgment, no unsoundness
   would result. *)

type vr_map = (string * Rat.rat) list;

fun get_vr v vrs =
    case List.find (fn (v', _) => v' = v) vrs of
	SOME (_, q) => q
      | NONE => raise Useful.Error ("var " ^ v ^ " not bound to rational; Binding list = "
				    ^ (String.concatWith
					   "\n"
					   (map (fn (v, q) => (v ^ " => " ^ (Rat.toString q))) vrs)));

fun eval_term (tm : Term.term) (vrs : vr_map) =
     case tm of
	 Term.Rat q => q
       | Term.Fn (v, []) => get_vr v vrs
       | Term.Fn ("+", [tm1, tm2]) => Rat.add (eval_term tm1 vrs, eval_term tm2 vrs)
       | Term.Fn ("-", [tm1, tm2]) => Rat.add (eval_term tm1 vrs, Rat.neg(eval_term tm2 vrs))
       | Term.Fn ("-", [tm]) => Rat.neg (eval_term tm vrs)
       | Term.Fn ("*", [tm1, tm2]) => Rat.mult (eval_term tm1 vrs, eval_term tm2 vrs)
       | Term.Fn ("^", [tm1, tm2]) => Rat.exp (eval_term tm1 vrs, eval_term tm2 vrs) (* addition by JPB *)
       | Term.Fn (name,_) => raise Useful.Error ("The function " ^ name ^ " is unsupported in eval_term in IntvlsFP.sml")
       | Term.Var (name) => raise Useful.Error ("Variables are unsupported in eval_term in IntvlsFP.sml, name of variable : "^name^" .")
       | _ => raise Useful.Error "Unsupported term evaluation.";

fun eval_atom (a : Atom.atom) (vrs : vr_map) =
    case a of
	(reln, [tm1, tm2]) =>
	let val e_tm1 = eval_term tm1 vrs
	    val e_tm2 = eval_term tm2 vrs
	in (case reln of
		"=" => Rat.eq (e_tm1, e_tm2)
	      | ">=" => Rat.le (e_tm2, e_tm1)
	      | ">" => Rat.lt (e_tm2, e_tm1)
	      | "<" => Rat.lt (e_tm1, e_tm2)
	      | "<=" => Rat.le (e_tm1, e_tm2)
	      | _ => raise Useful.Error "eval_atom: unsupported reln")
	end
      | _ => raise Useful.Error "eval_atom: unsupported atom";

fun eval_qf_fml (fm : Formula.formula) (vrs : vr_map) =
    case fm of
	Formula.True => true
      | Formula.False => false
      | (Formula.Atom a) => eval_atom a vrs
      | (Formula.And (fm1, fm2)) =>
	(eval_qf_fml fm1 vrs) andalso (eval_qf_fml fm2 vrs)
      | (Formula.Or (fm1, fm2)) =>
	(eval_qf_fml fm1 vrs) orelse (eval_qf_fml fm2 vrs)
      | (Formula.Not fm1) =>
	not (eval_qf_fml fm1 vrs)
      | _ => raise Useful.Error ("eval_qf_fml: Cannot evaluate formula: "
				 ^ Formula.toString fm);

(* Given a floating point interval, return a list of rational points
   inside of it. *)

local open Real in
fun pts_in_intvl (i as (bl, l, r, br) : intvl) =
    if isEmpty i then [] else
    let val prepend_zero = case (l, r) of
			       (Num i, Num j) => i < 0.0 andalso 0.0 < j
			     | (Infty NEG_INFTY, Num j) => j > 0.0
			     | (Num i, Infty POS_INFTY) => i < 0.0
			     | _ => false
	val pts =
	    case (bl, l, r, br) of
		(RIGHT_CLOSED, Infty NEG_INFTY, Infty POS_INFTY, LEFT_CLOSED)
		=> map Rat.rat_of_int [0, 1, ~1, 10, ~10, 100, ~100]
	      | (LEFT_CLOSED, Num l, Num r, RIGHT_CLOSED)
		=> if Real.==(l, r) then [rat_of_float l]
		   else [rat_of_float l, rat_of_float ((l + r)  / 2.0),
			 rat_of_float r]
	      | (_, Infty NEG_INFTY, Num r, RIGHT_CLOSED)
		=> [rat_of_float (r - 10.0), rat_of_float (r - 1.0),
		    rat_of_float (r - 0.5), rat_of_float r]
	      | (_, Infty NEG_INFTY, Num r, LEFT_CLOSED)
		=> [rat_of_float (r - 10.0), rat_of_float (r - 1.0),
		    rat_of_float (r - 0.5)]
	      | (LEFT_CLOSED, Num l, Infty POS_INFTY, _)
		=> [rat_of_float l, rat_of_float (l + 0.5),
		    rat_of_float (l + 10.0)]
	      | (LEFT_CLOSED, Num l, Num r, LEFT_CLOSED)
		=> [rat_of_float l, rat_of_float ((l + r) / 2.0)]
	      | (RIGHT_CLOSED, Num l, Num r, RIGHT_CLOSED)
		=> [rat_of_float ((l + r) / 2.0), rat_of_float r]
	      | (RIGHT_CLOSED, Num l, Num r, LEFT_CLOSED)
		=> [rat_of_float ((l + r) / 2.0)]
	      | _ => [Rat.zero, Rat.neg Rat.one, Rat.one]
    in if prepend_zero andalso not(List.exists (fn x => Rat.eq(x, Rat.zero)) pts)
       then Rat.zero :: pts else pts
    end
end;

(* Given an IC and a term context, extract a list of the form
    [(RCF-var-str, rational-sample-pts-in-IC[RCF-var-str]), ...]. *)

fun rcf_var_sample_pts ic tc =
    let val rcf_svid_pairs = tc_rcf_svid_pairs tc
	fun make_str_i_pair (str, vid) = (str, get_i_from_ic (ic, vid))
	val str_i_pairs = map make_str_i_pair rcf_svid_pairs
	fun make_str_spts_pair (str, i) = (str, pts_in_intvl i)
    in
	map make_str_spts_pair str_i_pairs
    end;

(* ICP SAT-search judgment datatype *)

datatype icp_sat_j = J_Unsat | J_Sat of vr_map | J_Unknown;

(* Given a list of the form
     [(RCF-var-str, rational-sample-pts-in-IC[RCF-var-str]), ...],
   check to see if any combination of the induced bindings
   results in a SATisfying assignment for our atom list. *)

exception Q_Judgment of icp_sat_j;

fun rcf_check_sat l bindings al =
    case l of
	[] => if List.all (fn a => eval_atom a bindings) al
	      then raise Q_Judgment (J_Sat bindings) else J_Unknown
      | ((str, pts) :: ls) =>
	((map (fn p =>
		  let val new_bindings = ((str, p) :: bindings)
		  in rcf_check_sat ls new_bindings al end)
	      pts);
	 J_Unknown);

(* ICP-SAT: Variant of BAP on AL for finding rational witnesses. *)

fun icp_sat al =
    let val ic = mk_intvl_ctxt 200
	val tc = mk_tmv_ctxt(List.length(al) * 10)
	val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
	val al_proved_unsat = ref false
	val _ = fixed_pt_icp_pcl(ic, pcl, 5, 0)
	    handle EMPTY_INTVL_IN_IC => (al_proved_unsat := true; false)
	val result = ref J_Unknown
    in ( (* print("------------------------------------------------\n"); *)
	 (* print ("Atoms: \n"); *)
	 (* List.app (fn x => print ("  " ^ (Atom.toString x) ^ "\n")) al; *)

	 if !al_proved_unsat then
	     ((* print "ICP_Sat refuted AL, so no witness search\n"; *)
	      (* print "------------------------------------------------\n"; *)
	      J_Unsat)
	 else
	     ((* print(":: Looking for SAT witness in contracted intervals ::\n"); *)
	      let val str_pts_pairs = rcf_var_sample_pts ic tc
	      in
		  ((* print("Computed sample points:\n"); *)
		   (* map (fn (s, l) => print (" " ^ s ^ ": [" ^  *)
		   (* 			   (String.concatWith ", " (map Rat.toString l))  *)
		   (* 			   ^ "]\n")) *)
		   (*     str_pts_pairs; *)
		   (* print("Checking for satisfying vector...\n"); *)
		   result := (rcf_check_sat str_pts_pairs [] al
			      handle Q_Judgment (J_Sat b) =>
				     (* let val _ = print "--->Satisfying vector found!\n" *)
				     (*     val _ = print "------------------------------------------------\n" *)
				     (* in *) (J_Sat b) (* end *) ))
	      end;
	      !result)
       )
    end;

(* Variant of ICP-SAT for integration with Z3.
   This either returns NONE if a formula was recognised to be UNSAT,
   else it returns a list of variable's and intervals containing them. *)

fun var_intervals_from_al al =
    let val ic = mk_intvl_ctxt 200
	val tc = mk_tmv_ctxt(List.length(al) * 10)
	val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
	val al_proved_unsat = ref false
	val _ = fixed_pt_icp_pcl(ic, pcl, 5, 0)
	    handle EMPTY_INTVL_IN_IC => (al_proved_unsat := true; false)
	val result = ref J_Unknown
    in if !al_proved_unsat then
	   NONE
       else
           let val rcf_svid_pairs = tc_rcf_svid_pairs tc
	       fun make_str_i_pair (str, vid) = (str, get_i_from_ic (ic, vid))
	       val str_i_pairs = map make_str_i_pair rcf_svid_pairs
	   in
	       SOME str_i_pairs
	   end
    end;

(* Variant of ICP-SAT utilising SMT for real algebraic witnesses. *)

fun smt_rag_sat al =
    let val ic = mk_intvl_ctxt 200
	val tc = mk_tmv_ctxt(List.length(al) * 10)
	val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
	val al_proved_unsat = ref false
	val _ = fixed_pt_icp_pcl(ic, pcl, 5, 0)
	    handle EMPTY_INTVL_IN_IC => (al_proved_unsat := true; false)
    in if !al_proved_unsat then
	   J_Unsat
       else
	   let val rcf_svid_pairs = tc_rcf_svid_pairs tc
	       fun make_str_i_pair (str, vid) = (str, get_i_from_ic (ic, vid))
	       val str_i_pairs = map make_str_i_pair rcf_svid_pairs
	       val vars = map (fn (x, y) => x) str_i_pairs
	       fun make_fm_from_i_pair vstr i =
		   let val atom_1 = ref NONE
		       val atom_2 = ref NONE
		   in
		       case i of
			   (bl, l, r, br) =>
			   (case (bl, l) of
				(LEFT_CLOSED, Num q)
				=> atom_1 := SOME (">=", [Term.Fn (vstr, []), Term.Rat (rat_of_float q)])
			      | (RIGHT_CLOSED, Num q)
				=> atom_1 := SOME (">", [Term.Fn (vstr, []), Term.Rat (rat_of_float q)])
			      | _ => ();
			    (case (r, br) of
				 (Num q, RIGHT_CLOSED)
				 => atom_2 := SOME ("<=", [Term.Fn (vstr, []), Term.Rat (rat_of_float q)])
			       | (Num q, LEFT_CLOSED)
				 => atom_2 := SOME ("<", [Term.Fn (vstr, []), Term.Rat (rat_of_float q)])
			       | _ => ());
			    case (!atom_1, !atom_2) of
				(SOME a, SOME a')
				=> SOME (Formula.And (Formula.Atom a, Formula.Atom a'))
			      | (SOME a, NONE)
				=> SOME (Formula.Atom a)
			      | (NONE, SOME a')
				=> SOME (Formula.Atom a')
			      | _ => NONE)
		   end
	       val bounding_fm = ref Formula.True
	       fun conjoin_b_fm b_fm =
		   if (!bounding_fm) = Formula.True
		   then bounding_fm := b_fm
		   else bounding_fm := Formula.And (!bounding_fm, b_fm)
	       val _ = map (fn (str, i) =>
			       let val b_fm = make_fm_from_i_pair str i
			       in case b_fm of
				      SOME fm => conjoin_b_fm fm
				    | NONE => ()
			       end)
			   str_i_pairs
	       val al_as_fml = map (fn a => Formula.Atom a) al
	       val final_fm = if (!bounding_fm) = Formula.True then Formula.listMkConj al_as_fml
			      else Formula.listMkConj ((!bounding_fm) :: al_as_fml)
	   in
	       case SMT.z3_no_conflicts_judgment vars final_fm of
		   Common.Sat _ => ((* print "Z3_RAG_SAT proved SAT!"; *) J_Sat [])
		 | Common.Unsat => ((* print "Z3_RAG_SAT proved UNSAT!"; *) J_Unsat)
		 | _ => J_Unknown
	   end
    end;

(* Convert input formula to DNF *)

local open Formula in

exception DNF_TOO_LARGE;
val distrib_limit = 32; (* <--- should make this command-line configurable *)

fun psimplify' fm =
    case fm of
	Not False => True
      | Not True => False
      | Not(Not p) => p
      | And(p, False) => False
      | And(False, p) => False
      | And(p, True) => p
      | And(True, p) => p
      | Or(p, False) => p
      | Or(False, p) => p
      | Or(p, True) => True
      | Or(True, p) => True
      | _ => fm;

fun psimplify fm =
    case fm of
	Not p => psimplify' (Not(psimplify p))
      | And(p, q) => psimplify' (And(psimplify p, psimplify q))
      | Or(p, q) => psimplify' (Or(psimplify p, psimplify q))
      | _ => fm;

fun nnf fm =
    case fm of
	And(p, q) => And(nnf p, nnf q)
      | Or(p, q) => Or(nnf p, nnf q)
      | Not(Not p) => nnf p
      | Not(And(p, q)) => Or(nnf(Not p), nnf(Not q))
      | Not(Or(p, q)) => And(nnf(Not p), nnf(Not q))
      | _ => fm;

fun elim_negs fm =
    case fm of
	And(p, q) => And(elim_negs p, elim_negs q)
      | Or(p, q) => Or(elim_negs p, elim_negs q)
      | Not(Atom ("=", args)) => Or(Atom(">", args), Atom("<", args))
      | Not(Atom (">=", args)) => Atom("<", args)
      | Not(Atom (">", args)) => Atom("<=", args)
      | Not(Atom ("<", args)) => Atom(">=", args)
      | Not(Atom ("<=", args)) => Atom(">", args)
      | _ => fm;

fun itlist f l b =
    case l of
	[] => b
      | (h::t) => f h (itlist f t b);

fun allpairs f l1 l2 =
    itlist (fn x => (Useful.curry (op @)) (map (f x) l2)) l1 [];

fun distrib s1 s2 = Useful.setify(allpairs Useful.union s1 s2);

fun purednf fm =
    case fm of
	And(p, q) => (let val d = distrib (purednf p) (purednf q)
			  (* val _ = print ("\ndistrib length: " ^ (Int.toString (length d))) *)
			  val _ = if (length d) > distrib_limit then raise DNF_TOO_LARGE else ()
		      in d end)
      | Or(p, q) => (let val u = Useful.union (purednf p) (purednf q)
			 (* val _ = print ("\nunion length: " ^ (Int.toString (length u))) *)
		     in u end)
      | _ => [[fm]];

fun psubset s1 s2 =
    Useful.subset s1 s2 andalso
    List.exists (fn x => not(Useful.mem x s1)) s2;

fun dnf fm =
    let val enf = elim_negs (psimplify (nnf fm))
	val dnf' = purednf enf
	(* val _ = print ("length of purednf: " ^ (Int.toString (length dnf')) ^ ".\n") *)
	val l = List.length dnf'
    	val dnf'' = if (l = 1 orelse l >= 4096) then
			dnf'
		    else List.filter
			(fn d =>
			    not(List.exists (fn d' => psubset d' d) dnf'))
			dnf'
	(* val _ = print ("!!!finished filtering.\n\n") *)
	val _ = if !traceb andalso (List.length(dnf'') < List.length(dnf')) then
		    trace(1, "\nDNF subset subsumption: " ^
			  Int.toString(List.length dnf') ^ " to " ^
			  Int.toString(List.length dnf'') ^ ".\n")
		else ()
    in dnf''
    end;

end;

(* An ICP-Friendly formula is an RCF formula which is purely
   existential.  We return it as a list of lists of atoms, which
   corresponds to a DNF normalisation of the input formula. *)

datatype fml_icp_fr = ICP_FRIENDLY of ((Atom.atom list) list)
		    | ICP_UNFRIENDLY;

(* Is the quantifier-free matrix of a formula ICP friendly? *)

local open Formula
in
fun icp_atom_lst l : Atom.atom list =
    case l of
	[] => []
      | (h::t) =>
	 case h of
	     Atom(r, a) => (r, a) :: icp_atom_lst t
	   | True => icp_atom_lst t
	   | False => [("=", [Term.Rat (Rat.rat_of_int 0), Term.Rat (Rat.rat_of_int 1)])]
	   | _ => raise Useful.Error ("ICP formula not an Atom list: "
				      ^ Formula.toString(h) ^ ".\n");

(* Is the quantifier prefix of a formula ICP friendly?  This is true
   iff the quantifier prefix is purely existential.  Note: We assume
   formulas are in prenex normal form. If true, then we return the
   quantifier-free matrix of the formula. *)

fun qfm f =
    case f of Forall(v, f1) => NONE
	    | Exists(v, f1) => qfm f1
	    | _ => SOME f;
end;

(* Is a formula ICP friendly?  If it is, then we return the formula
   represented as a list of atoms, wrapped in the monad fml_icp_fr of
   the form ICP_FRIENDLY atom-lst.  If the formula isn't ICP friendly,
   then we return ICP_UNFRIENDLY. *)

fun icp_friendly (f) =
    case qfm f of
	SOME q =>
	let val ex = ref false
	    val qfm_dnf = dnf q
		handle DNF_TOO_LARGE => (ex := true; [])
	    val qfm_dnf_al = map (icp_atom_lst) qfm_dnf
	    (* val _ = print ("\n DNF length: " ^ (Int.toString (List.length qfm_dnf_al)) ^ " -- ") *)
	in if !ex then ICP_UNFRIENDLY else ICP_FRIENDLY qfm_dnf_al end
      | NONE => ICP_UNFRIENDLY;

(* Run branch and prune ICP on a list of conjunctive cases *)

fun bap_on_cases (dnf_al, clim, slim, aslim) =
    case dnf_al of
	[] => BAP_EMPTY
      | (al::als) =>
	case bap_on_al (al, clim, slim, aslim) of
	    BAP_EMPTY => bap_on_cases (als, clim, slim, aslim)
	  | _ => BAP_RESULT [];

(* Combine J_ judgment values for DNF formulas. *)

fun j_co x y =
    case (x, y) of
	(J_Unknown, J_Unsat) => J_Unknown
      | (J_Unsat, J_Unknown) => J_Unknown
      | (_, J_Sat b) => J_Sat b
      | (J_Sat b, _) => J_Sat b
      | (J_Unsat, J_Unsat) => J_Unsat
      | (J_Unknown, J_Unknown) => J_Unknown;

(* Convert a SAT witness to a string. *)

fun witness_to_string w =
    "[" ^
    (String.concatWith "," (map (fn (s, q) => s ^ "=" ^ (Rat.toString q)) w))
     ^ "]";

(* Run ICP-based rational model finding procedure on a list of
   conjunctive cases *)

fun icp_sat_on_cases dnf_al =
    case dnf_al of
	[] => J_Unsat
      | (al::als) =>
	let val r = icp_sat al
	in
	    case r of J_Sat b =>
		      ((* print "sat! : ";
			print ((witness_to_string b) ^ "\n"); *)
		       J_Sat b)
		    | _ => j_co r (icp_sat_on_cases als)
	end;

(* Run ICP/SMT-based algebraic number model finding procedure on a
   list of conjunctive cases *)

fun smt_rag_sat_on_cases dnf_al =
    case dnf_al of
	[] => J_Unsat
      | (al::als) =>
	let val r = smt_rag_sat al
	in
	    case r of J_Sat b =>
		      ((* print "sat! : ";
			print ((witness_to_string b) ^ "\n"); *)
		       J_Sat b)
		    | _ => j_co r (smt_rag_sat_on_cases als)
	end;

(* Run branch and prune ICP on ``ICP friendly'' formulas. *)

fun bap_on_fml (f, clim, slim, aslim) =
    if (f = Formula.True) then BAP_NO_PROGRESS else
    if (f = Formula.False) then BAP_EMPTY else
    case icp_friendly f of
	ICP_FRIENDLY dnf_al =>
	(if !traceb then
	     trace(1, ("\n BAP_ICP: # DNF cases = " ^ Int.toString(List.length dnf_al) ^ ".\n"))
	 else ();
	 let val result = bap_on_cases (dnf_al, clim, slim, aslim)
	 in result end)
      | ICP_UNFRIENDLY => BAP_NO_PROGRESS;

(* Run ICP-based rational model-finding technique on ``ICP friendly'' formulas. *)

fun icp_sat_on_fml f =
    if (f = Formula.True) then J_Sat [] else
    if (f = Formula.False) then J_Unsat else
    case icp_friendly f of
	ICP_FRIENDLY dnf_al => icp_sat_on_cases dnf_al
      | ICP_UNFRIENDLY => J_Unknown;

(* Run ICP/SMT-based algebraic number model-finding technique on ``ICP
   friendly'' formulas. *)

fun smt_rag_sat_on_fml f =
    if (f = Formula.True) then J_Sat [] else
    if (f = Formula.False) then J_Unsat else
    case icp_friendly f of
	ICP_FRIENDLY dnf_al => smt_rag_sat_on_cases dnf_al
      | ICP_UNFRIENDLY => J_Unknown;


(* Check to make sure that Poly/ML is changing rounding mode. *)

fun check_fp_rm_works () =
    let val prevRM = IEEEReal.getRoundingMode() in
	(case prevRM of
	     IEEEReal.TO_NEGINF => IEEEReal.setRoundingMode(IEEEReal.TO_POSINF)
	   | IEEEReal.TO_POSINF => IEEEReal.setRoundingMode(IEEEReal.TO_NEGINF)
	   | IEEEReal.TO_NEAREST => IEEEReal.setRoundingMode(IEEEReal.TO_POSINF)
	   | TO_ZERO => IEEEReal.setRoundingMode(IEEEReal.TO_POSINF);
	 let val newRM = IEEEReal.getRoundingMode()
	     val r = prevRM <> newRM in
	     (if r then IEEEReal.setRoundingMode(prevRM) else ();
	      r)
	 end)
    end;



(* Testing

 val base_ic = mk_intvl_ctxt 7000 : intvl_ctxt;
 val pc0 = Sum (0, 1, GEQ, 2);
 val pc1 = Sum (3, 0, LT, 2);
 val pc2 = Sum (3, 1, EQ, 2);
 val pc3 = Diff(0, 1, LEQ, 3);
 val pc4 = Prod(0, 3, GEQ, 2);
 val i0 = mk_closed_intvl(1,1,2,2);
 val i1 = mk_closed_intvl(3,1,4,1);
 val i2 = mk_closed_intvl(~100,1,1,1);
 update_ic(base_ic, 0, i0);
 update_ic(base_ic, 3, i2);
 val pc_lst = [pc0, pc1, pc2, pc3, pc4];
 icp_pcl(base_ic, pc_lst);

 val base_ic = mk_intvl_ctxt 7000 : intvl_ctxt;
 val pc0 = Sum (0, 1, GEQ, 2);
 val i0 = mk_closed_intvl(1,1,2,2);
 update_ic(base_ic, 0, i0);
 update_ic(base_ic, 1, i2);
 val pc_lst = [pc0, pc1, pc2, pc3, pc4];
 print_ic(base_ic);
 icp_pcl(base_ic, pc_lst);
 print_ic(base_ic);
 icp_pcl(base_ic, pc_lst);
 print_ic(base_ic);

 val base_ic = mk_intvl_ctxt 7000 : intvl_ctxt;
 val pc0 = Sum(0, 0, EQ, 1); (* v0 + v0 = v1 *)
 val pc1 = Prod(0, 1, GEQ, 0); (* v0 * v1 >= v0 *)
 val pc_lst = [pc0, pc1];
 val i0 = mk_closed_intvl(0,1,1,1);
 update_ic(base_ic, 0, i0); (* v0 in [0, 1] *)
 print_ic(base_ic);
 fixed_pt_icp_pcl(base_ic, pc_lst);
 val i1 = mk_closed_intvl(~10,1,1,1);
 update_ic(base_ic, 1, i1); (* v1 in [-10, 1]. *)
 val pc2 = Prod(1, 1, EQ, 2);
 val pc_lst = [pc0, pc1, pc2];
 icp_pcl(base_ic, pc_lst);
 val pc3 = Bin(3, EQ, 0);
 val pc_lst = [pc0, pc1, pc2, pc3];
 val pc4 = Bin(4, GEQ, 0);
 val pc_lst = [pc0, pc1, pc2, pc3, pc4];
 fixed_pt_icp_pcl(base_ic, pc_lst);
 val pc5 = BinConst(5, GT, Rat.rat_of_int 100);
 val pc6 = Sum(0, 5, EQ, 6);
 val pc_lst = [pc0, pc1, pc2, pc3, pc4, pc5, pc6];

 val al = [a0, a1, a2, a21, a3, a4, a5];
 val a6 = ("=", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), Term.Rat (Rat.rat_of_int 2)]);
 al_to_pcl(al);
 icp_on_al(al, 100);

 val a6 = ("=", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), Term.Rat (Rat.rat_of_int 2)]);
 val a7 = (">", [Term.Fn("x", []), Term.Rat(Rat.rat_of_int 1)]);
 val a8 = ("<", [Term.Fn("x", []), Term.Rat(Rat.rat_of_int 2)]);
 val a9 = ("=", [Term.Fn("y", []), Term.Fn("+", [Term.Fn("x",[]), Term.Rat(Rat.rat_of_int 5)])]);
 val a10 = ("=", [Term.Fn("*", [Term.Fn("x",[]), Term.Fn("y",[])]), Term.Rat(Rat.rat_of_int 0)]);
 val a11 =
 icp_on_al([a6, a7, a8, a9, a10], 100);
 bap_on_al([a7, a8, a9], 100, 10);
*)


end
