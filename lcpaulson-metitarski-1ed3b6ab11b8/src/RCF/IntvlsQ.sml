(* ======================================================================== *)
(*               Core Arithmetical and Narrowing Machinery for              *)
(*                 Generalised (Non-Compact) Real Intervals                 *)
(*                        version 0.0a, 13-June-2011                        *)
(* with interval end-point values taken over Q_ext = (Q union {-inf, +inf}) *)
(*                                                                          *)
(* by G.O.Passmore, Cambridge Computer Laboratory and LFCS, Edinburgh, 2011 *)
(* Contact: (e) grant.passmore@cl.cam.ac.uk   (w) www.cl.cam.ac.uk/~gp351/. *)
(* ======================================================================== *)

structure IntvlsQ :> IntvlsQ =
struct

(* Boundary type: Either left closed ('[') or right closed (']') *)

datatype bt = LEFT_CLOSED | RIGHT_CLOSED;

(* Infinity type *)

datatype infty = NEG_INFTY | POS_INFTY;

(* Endpoint type, Q_ext: Either an exact precision rational or +/- infty *)

datatype ep = Rat of Rat.rat | Infty of infty;

(* Generalised interval type: a left boundary type, left and right
   endpoints, and a right boundary type. *)

type intvl = bt * ep * ep * bt;

(* Some simple tracing *)

val trace_lvl = ref 0;

fun trace (i, s) =
    if (i <= !trace_lvl) then print(s ^ "\n") else ();

fun set_icp_trace(i) = trace_lvl := i;

(* Exception for bad endpoint arithmetic *)

exception EP_ARITH_UNDEF;

(* The zero endpoint *)

val ep_zero = Rat(Rat.rat_of_int 0);

(* Negation of infinities *)

fun inf_negate NEG_INFTY = POS_INFTY
  | inf_negate POS_INFTY = NEG_INFTY;

(* Negation of endpoints *)

fun ep_negate (e) =
    case e of Infty inf => Infty (inf_negate inf)
	    | Rat q => Rat (Rat.neg q);

(* Addition of interval endpoints *)

fun ep_add ((Rat e1), (Rat e2)) = Rat(Rat.add(e1, e2))
  | ep_add ((Rat e1), (Infty e2)) = Infty(e2)
  | ep_add ((Infty e1), (Rat e2)) = Infty(e1)
  | ep_add ((Infty e1), (Infty e2)) =
    if e1 = e2 then (Infty e1)
    else raise EP_ARITH_UNDEF;

(* Negation of interval boundary types *)

fun bt_neg LEFT_CLOSED = RIGHT_CLOSED
  | bt_neg RIGHT_CLOSED = LEFT_CLOSED;

(* Subtraction of interval endpoints *)

fun ep_sub ((Rat e1), (Rat e2)) = Rat(Rat.add(e1, Rat.neg(e2)))
  | ep_sub ((Rat e1), (Infty e2)) = Infty(inf_negate(e2))
  | ep_sub ((Infty e1), (Rat e2)) = Infty(e1)
  | ep_sub ((Infty NEG_INFTY), (Infty POS_INFTY)) = Infty(NEG_INFTY)
  | ep_sub ((Infty POS_INFTY), (Infty NEG_INFTY)) = Infty(POS_INFTY)
  | ep_sub _ = raise EP_ARITH_UNDEF;

(* Multiplication of interval endpoints *)

fun ep_mult ((Rat e1), (Rat e2)) = Rat(Rat.mult(e1, e2))
  | ep_mult ((Infty e1), (Rat e2)) =
    if Rat.gt0(e2) then Infty(e1)
    else if Rat.gt0(Rat.neg(e2)) then Infty(inf_negate(e1))
    else raise EP_ARITH_UNDEF
  | ep_mult ((Rat e1), (Infty e2)) =
    if Rat.gt0(e1) then Infty(e2)
    else if Rat.gt0(Rat.neg(e1)) then Infty(inf_negate(e2))
    else raise EP_ARITH_UNDEF
  | ep_mult ((Infty e1), (Infty e2)) =
    if e1 = e2 then Infty(POS_INFTY) else Infty(NEG_INFTY);

(* Division of interval endpoints *)

fun ep_div ((Rat e1), (Rat e2)) =
    if (e2 = Rat.rat_of_int(0)) then raise EP_ARITH_UNDEF
    else Rat(Rat.mult(e1, Rat.inv(e2)))
  | ep_div ((Infty e1), (Infty e2)) = raise EP_ARITH_UNDEF
  | ep_div ((Infty NEG_INFTY), (Rat e2)) =
    if (e2 = Rat.rat_of_int(0)) then raise EP_ARITH_UNDEF
    else if Rat.gt0(e2) then (Infty NEG_INFTY)
    else (Infty POS_INFTY) (* e2 < 0 *)
  | ep_div ((Infty POS_INFTY), (Rat e2)) =
    if (e2 = Rat.rat_of_int(0)) then raise EP_ARITH_UNDEF
    else if Rat.gt0(e2) then (Infty POS_INFTY)
    else (Infty NEG_INFTY)
  | ep_div ((Rat e1), (Infty _)) = ep_zero;

(* Comparision relations {<=, <, >, >=} on interval endpoints *)

fun ep_leq ((Rat e1), (Rat e2)) = Rat.le(e1, e2)
  | ep_leq ((Infty NEG_INFTY), _) = true
  | ep_leq (_, (Infty POS_INFTY)) = true
  | ep_leq _ = false;

fun ep_lt (e1, e2) = ep_leq(e1, e2) andalso not (e1 = e2);

fun ep_gt (e1, e2) = ep_lt(e2, e1);

fun ep_geq (e1, e2) = ep_leq(e2, e1);

(* Minimum and Maximum of two endpoints *)

fun ep_min (e1, e2) = if ep_leq(e1, e2) then e1 else e2;

fun ep_max (e1, e2) = if ep_geq(e1, e2) then e1 else e2;

(* Interval emptiness predicate *)

fun isEmpty (LEFT_CLOSED, el, er, RIGHT_CLOSED) =
    if (ep_gt(el, er) orelse (el = Infty(POS_INFTY))
	orelse (er = Infty(NEG_INFTY)))
    then true else false
  | isEmpty (_, el, er, _) =
    if (ep_geq(el,er) orelse (el = Infty(POS_INFTY))
	orelse (er = Infty(NEG_INFTY)))
       then true else false;

(* Make an interval *)

fun mk_intvl (bt1, l, r, bt2) =  (bt1, l, r, bt2) : intvl;

(* A canonical empty interval: We use [1, 0]. *)

val EMPTY_INTVL =
    mk_intvl (LEFT_CLOSED,
	      Rat(Rat.rat_of_int 1),
	      Rat(Rat.rat_of_int 0),
	      RIGHT_CLOSED);

(* Convert an interval to a string *)

fun bt_str LEFT_CLOSED = "["
  | bt_str RIGHT_CLOSED = "]";

fun ep_str (Infty POS_INFTY) = "+inf"
  | ep_str (Infty NEG_INFTY) = "-inf"
  | ep_str (Rat q) = Rat.toString q;

fun toString (i : intvl) =
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
	    mk_intvl (bl, ep_add(l1, l2), ep_add(r1, r2), br)
	end;

(* Interval subtraction *)

fun sub ((i1, i2) : intvl * intvl) =
    if (isEmpty(i1) orelse isEmpty(i2)) then EMPTY_INTVL else
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	let val bl = sel_bt_l(b1l = LEFT_CLOSED andalso b2r = RIGHT_CLOSED)
	    val br = sel_bt_r(b1r = RIGHT_CLOSED andalso b2l = LEFT_CLOSED)
	    val l = case ep_sub(l1, r2) of
			(Rat x) => (Rat x)
		      | _ => (Infty NEG_INFTY)
	    val r = case ep_sub(r1, l2) of
			(Rat x) => (Rat x)
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
    else if (l = ep_zero andalso r = ep_zero) then Z
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
	    (P, P) => ep_mult(l1, l2)
	  | (P, M) => ep_mult(r1, l2)
	  | (P, N) => ep_mult(r1, l2)
	  | (M, P) => ep_mult(l1, r2)
	  | (M, M) => ep_min(ep_mult(l1, r2), ep_mult(r1, l2))
	  | (M, N) => ep_mult(r1, l2)
	  | (N, P) => ep_mult(l1, r2)
	  | (N, M) => ep_mult(l1, r2)
	  | (N, N) => ep_mult(r1, r2)
	  | _ => ep_zero;

(* Determine right endpoint value of interval product *)

fun mult_right_ep ((i1, i2) : intvl * intvl) =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), m_classify(i2)) of
	    (P, P) => ep_mult(r1, r2)
	  | (P, M) => ep_mult(r1, r2)
	  | (P, N) => ep_mult(l1, r2)
	  | (M, P) => ep_mult(r1, r2)
	  | (M, M) => ep_max(ep_mult(l1, l2), ep_mult(r1, r2))
	  | (M, N) => ep_mult(l1, l2)
	  | (N, P) => ep_mult(r1, l2)
	  | (N, M) => ep_mult(l1, l2)
	  | (N, N) => ep_mult(l1, l2)
	  | _ => ep_zero;

(* Omega judgment for determing product closure *)

fun omega ((el, er, alpha, gamma) : ep * ep * bool * bool) =
    (alpha andalso gamma) orelse
    (alpha andalso el = ep_zero) orelse
    (gamma andalso er = ep_zero);

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
	  | (M, M) => let val prod_l1_r2 = ep_mult(l1, r2)
			  val prod_r1_l2 = ep_mult(r1, l2)
		      in
			  if ep_lt(prod_l1_r2, prod_r1_l2) then
			      omega(l1, r2, is_bt_cl(b1l), is_bt_cr(b2r))
			  else if prod_l1_r2 = prod_r1_l2 then
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
	  | (M, M) => let val prod_l1_l2 = ep_mult(l1, l2)
			  val prod_r1_r2 = ep_mult(r1, r2)
		      in
			  if ep_lt(prod_l1_l2, prod_r1_r2) then
			      omega(r1, r2, is_bt_cr(b1r), is_bt_cr(b2r))
			  else if prod_l1_l2 = prod_r1_r2 then
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
    else if (l = ep_zero andalso r = ep_zero) then DZ
    else if (l = ep_zero andalso ep_gt(r, ep_zero)) then DP0
    else if (ep_gt(l, ep_zero) andalso ep_gt(r, ep_zero)) then DP1
    else if (ep_lt(l, ep_zero) andalso (r = ep_zero)) then DN0
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
	    (P, DP1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
	  | (P, DP0) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
	  | (P, DM) => CLDBL (false,
			      omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
	  | (P, DN0) => CLSNG (false)
	  | (P, DN1) => CLSNG (omega(r1, r2, is_bt_cl(b1r), is_bt_cl(b2r)))
	  | (M, DP1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (M, DN1) => CLSNG (omega(r1, r2, is_bt_cl(b1r), is_bt_cl(b2r)))
	  | (M, _) => CLSNG (false)
	  | (N, DP1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (N, DP0) => CLSNG (false)
	  | (N, DM) => CLDBL (false,
			      omega(r1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (N, DN0) => CLSNG (omega(r1, l2, is_bt_cl(b1r), is_bt_cl(b2l)))
	  | (N, DN1) => CLSNG (omega(r1, l2, is_bt_cl(b1r), is_bt_cl(b2l)))
	  | (Z, _) => CLSNG (true)
	  | _ => CLSNG (true) (* This will be ultimately ignored in division,
			         as quotients of this class will be empty. *);

(* Determine if interval division should be right closed *)

fun div_right_closed ((i1, i2) : intvl * intvl) : d_lrc =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => CLSNG (omega(r1, l2, is_bt_cl(b1r), is_bt_cl(b2l)))
	  | (P, DP0) => CLSNG (false)
	  | (P, DM) => CLDBL (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)),
			      false)
	  | (P, DN0) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (P, DN1) => CLSNG (omega(l1, l2, is_bt_cl(b1l), is_bt_cl(b2l)))
	  | (M, DP1) => CLSNG (omega(r1, l2, is_bt_cl(b1r), is_bt_cl(b2l)))
	  | (M, DN1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
	  | (M, _) => CLSNG (false)
	  | (N, DP1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
	  | (N, DP0) => CLSNG (omega(r1, r2, is_bt_cl(b1r), is_bt_cl(b2r)))
	  | (N, DM) => CLDBL (omega(r1, r2, is_bt_cl(b1r), is_bt_cl(b2r)),
			      false)
	  | (N, DN0) => CLSNG (false)
	  | (N, DN1) => CLSNG (omega(l1, r2, is_bt_cl(b1l), is_bt_cl(b2r)))
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
	    (P, DP1) => EPSNG (ep_div(l1, r2))
	  | (P, DP0) => EPSNG (ep_div(l1, r2))
	  | (P, DM) => EPDBL ((Infty NEG_INFTY), (ep_div(l1, r2)))
	  | (P, DN0) => EPSNG (Infty NEG_INFTY)
	  | (P, DN1) => EPSNG (ep_div(r1, r2))
	  | (M, DP1) => EPSNG (ep_div(l1, l2))
	  | (M, DN1) => EPSNG (ep_div(r1, r2))
	  | (M, _) => EPSNG (Infty NEG_INFTY)
	  | (N, DP1) => EPSNG (ep_div(l1, l2))
	  | (N, DP0) => EPSNG (Infty NEG_INFTY)
	  | (N, DM) => EPDBL ((Infty NEG_INFTY), ep_div(r1, l2))
	  | (N, DN0) => EPSNG (ep_div(r1, l2))
	  | (N, DN1) => EPSNG (ep_div(r1, l2))
	  | (Z, _) => EPSNG ep_zero
	  (* Final case below will lead to [1,0] - i.e., empty *)
	  | _ => EPSNG (Rat (Rat.rat_of_int(1)));

(* Determine right endpoint value of an interval quotient. Note that
   the result may include two left endpoints, via EPDBL. *)

fun div_right_ep ((i1, i2) : intvl * intvl) : d_ep =
    case (i1, i2) of
	((b1l, l1, r1, b1r), (b2l, l2, r2, b2r)) =>
	case (m_classify(i1), d_classify(i2)) of
	    (P, DP1) => EPSNG (ep_div(r1, l2))
	  | (P, DP0) => EPSNG (Infty POS_INFTY)
	  | (P, DM) => EPDBL ((ep_div(l1, l2)), (Infty POS_INFTY))
	  | (P, DN0) => EPSNG (ep_div(l1, l2))
	  | (P, DN1) => EPSNG (ep_div(l1, l2))
	  | (M, DP1) => EPSNG (ep_div(r1, l2))
	  | (M, DN1) => EPSNG (ep_div(l1, r2))
	  | (M, _) => EPSNG (Infty POS_INFTY)
	  | (N, DP1) => EPSNG (ep_div(r1, r2))
	  | (N, DP0) => EPSNG (ep_div(r1, r2))
	  | (N, DM) => EPDBL ((ep_div(r1, r2)), (Infty POS_INFTY))
	  | (N, DN0) => EPSNG (Infty POS_INFTY)
	  | (N, DN1) => EPSNG (ep_div(l1, r2))
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
    if (i1 = REAL_LINE_INTVL) then i2
    else if (i2 = REAL_LINE_INTVL) then i1 else
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
    if (i1 = REAL_LINE_INTVL orelse i2 = REAL_LINE_INTVL) then
	REAL_LINE_INTVL else
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

(* Construct a closed interval [a/b, c/d] from (a, b, c, d) *)

fun mk_closed_intvl (a, b, c, d) : intvl =
    mk_intvl (LEFT_CLOSED,
	      Rat(Rat.rat_of_quotient(a, b)),
	      Rat(Rat.rat_of_quotient(c, d)),
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
	     (trace(1, "\n v" ^ Int.toString(v) ^ " in " ^ toString(i) ^ ".")))
	 (ic_lst(ic));
     trace(1,"\n"));

(* Given an IC, a variable id v and an interval I containing v,
   update v's bound in IC with the intersection of IC(v) and I.
   Note that we return true iff the IC was modified, i.e., the
   interval for v was narrowed. *)

fun update_ic (ic : intvl_ctxt, v : var_id, i : intvl) =
    let val old_i = get_i_from_ic(ic, v) in
	if not(old_i = i) then
	    let val new_i = intsct(old_i, i) in
		if not(old_i = new_i) then
		    (Polyhash.insert ic (v, new_i);
		     trace(2, "\n IC(v" ^ Int.toString(v) ^ ") := " ^ toString(new_i) ^ ".");
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
    can intersect mult(IC(v1), IC(v1)) with [0, +inf[. *)

fun narrow_prod_generic (ic, pc, narrow_fun0 : nf, narrow_fun1 : nf) =
    case pc of
	Prod (v1, v2, _, v3) =>
	let val old_i_v1 = get_i_from_ic(ic, v1)
	    val old_i_v2 = get_i_from_ic(ic, v2)
	    val old_i_v3 = get_i_from_ic(ic, v3)
	    val progress0 = ref false
	    val progress1 = ref false
	    val progress2 = ref false
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
		 true => progress2 := narrow_fun1(ic, v3, intsct(mult(old_i_v1, old_i_v1),
								 mk_intvl(LEFT_CLOSED,
									  ep_zero,
									  Infty POS_INFTY,
									  LEFT_CLOSED)))
	       | false => progress2 := narrow_fun1(ic, v3, mult(old_i_v1, old_i_v2));
	     (* Now, return boolean specifying whether or not an interval was narrowed. *)
	    !progress0 orelse !progress1 orelse !progress2)
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
	in narrow_fun0(ic, v1, mk_intvl(LEFT_CLOSED,
					Rat q,
					Rat q,
					RIGHT_CLOSED))
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

fun icp_pcl_prog(ic, pcl, progress_made) =
    case pcl of [] => progress_made
	      | (pc::pcs) =>
		let val progress =
			(case pc of
			     Sum _ => narrow_sum(ic, pc)
			   | Diff _ => narrow_diff(ic, pc)
			   | Prod _ => narrow_prod(ic, pc)
			   | Bin _ => narrow_bin(ic, pc)
			   | BinConst _ => narrow_bin(ic, pc))
			handle EMPTY_INTVL_IN_IC =>
			       (trace(2, "-- IC narrowed via " ^ pc_to_string(pc) ^ ".");
				raise EMPTY_INTVL_IN_IC)
		in (if progress then
			(trace(2, "-- IC narrowed via " ^ pc_to_string(pc) ^ ".");
			 ())
		    else ();
		    icp_pcl_prog(ic, pcs, progress_made orelse progress))
		end;

(* Perform interval constraint propagation upon an IC w.r.t.
   a list of primitive constraints.

   This is a ``single pass'' which returns true iff the pass
   narrowed an interval in IC.  We will later iterate icp_pcl
   until a fixed point is reach, i.e., until the return value
   of icp_pcl is false. *)

fun icp_pcl(ic, pcl : prim_con list) = icp_pcl_prog(ic, pcl, false);

(* Auxiliary function for fixed_pt_icp_pcl below *)

fun fixed_pt_icp_pcl_prog(ic, pcl, limit, count, progress_made) =
    let val progress = icp_pcl(ic, pcl) in
	if (progress andalso (count <= limit)) then
	    (print_ic(ic);
	     fixed_pt_icp_pcl_prog(ic, pcl, limit, count+1, true))
	else progress_made
    end;

(* Given an IC and PCL, keep narrowing IC w.r.t. PCL until a
   fixed point is reached, or a contraction limit is reached.

   We return true iff any pass made progress. *)

fun fixed_pt_icp_pcl(ic, pcl, limit) =
    fixed_pt_icp_pcl_prog(ic, pcl, limit, 0, false);

(* ^^^ Should next look at branch and prune loop for interval splitting ^^^  *)

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

exception BAD_TERM;

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
			| _ => raise BAD_TERM)
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
	   | _ => raise BAD_TERM)
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

(* Print the contents of a TC *)

fun print_tc (tc : tmv_ctxt) =
    (trace(1,"Term hashing:");
     app (fn (t, v) =>
	     (trace(1, "\n " ^ Term.toString(t) ^ " |-> v" ^ Int.toString(v) ^ ".")))
	 (tc_lst(tc));
     trace(1,"\n"));

(* Convert a list of RCF atoms into a list of primitive interval constraints *)

fun al_to_pcl(al : Atom.atom list) =
    let val tc = mk_tmv_ctxt(List.length(al) * 100) (* Size can grow as needed *)
    in let val pcl = List.concat (map (fn a => atom_to_pcl(tc, a)) al)
       in (print_tc(tc); pcl)
       end
    end;

(* Type for ICP return values *)

datatype icp_r = ICP_NO_PROGRESS | ICP_PROGRESS | ICP_EMPTY;

(* Given a list of primitive constraints, run ICP upon them *)

fun icp_on_pcl(pcl, limit) =
    let val ic = mk_intvl_ctxt 7000 in
	(if fixed_pt_icp_pcl(ic, pcl, limit)
	 then ICP_PROGRESS else ICP_NO_PROGRESS)
	handle EMPTY_INTVL_IN_IC =>
	       (trace(1, "\n .:. Empty interval found. \n\n ICP result:\n");
		print_ic(ic);
		ICP_EMPTY)
    end;

(* Given a list of atoms, run ICP upon them *)

fun icp_on_al(al, limit) =
    let val pcl = al_to_pcl(al) in
	(trace(1, "\nAtoms:");
	 app (fn x => trace(1, " " ^ Atom.toString(x))) al;
	 trace(1, "\n\nPrimitive constraints:");
	 app (fn x => trace(1, " " ^ pc_to_string(x) ^ "\n")) pcl;
	 icp_on_pcl(pcl, limit))
    end;

(* Check to see if an RCF formula is purely conjunctive, and,
   moreover, doesn't use ``!=.''  We call these formulas ``ICP
   friendly.''  If the formula is friendly, then we return it as a
   list of atoms.  Otherwise, we return ICP_UNFRIENDLY. *)

datatype fml_icp_fr = ICP_FRIENDLY of (Atom.atom list) | ICP_UNFRIENDLY;

(* Is the quantifier-free matrix of a formula ICP friendly? *)

local open Formula
in
fun icp_friendly_qfm (f) =
    case f of Atom(p, args) => ICP_FRIENDLY [(p, args)]
	    | And(a1, a2) =>
	      let val r1 = icp_friendly_qfm(a1)
		  val r2 = icp_friendly_qfm(a2)
	      in case (r1, r2) of
		     (ICP_FRIENDLY al1, ICP_FRIENDLY al2)
		     => ICP_FRIENDLY (al1 @ al2)
		   | _ => ICP_UNFRIENDLY
	      end
	    | Not(Atom(">", l)) => ICP_FRIENDLY [("<=", l)]
	    | Not(Atom(">=", l)) => ICP_FRIENDLY [("<", l)]
	    | Not(Atom("<=", l)) => ICP_FRIENDLY [(">", l)]
	    | Not(Atom("<", l)) => ICP_FRIENDLY [(">=", l)]
	    | _ => ICP_UNFRIENDLY

(* Is the quantifier prefix of a formula ICP friendly?  This is true
   iff the quantifier prefix is purely existential.  Note: We assume
   formulas are in prenex normal form. *)

fun icp_friendly_qp (f) =
    case f of Forall(v, f1) => ICP_UNFRIENDLY
	    | Exists(v, f1) => icp_friendly_qp f1
	    | _ => ICP_FRIENDLY [];
end;

(* Is a formula ICP friendly?  If it is, then we return the formula
   represented as a list of atoms, wrapped in the monad fml_icp_fr of
   the form ICP_FRIENDLY atom-lst.  If the formula isn't ICP friendly,
   then we return ICP_UNFRIENDLY. *)

fun icp_friendly (f) =
    case (icp_friendly_qp (f), icp_friendly_qfm (f)) of
	(ICP_FRIENDLY _, ICP_FRIENDLY al) => ICP_FRIENDLY al
      | _ => ICP_UNFRIENDLY;

(* Run ICP upon ``ICP friendly'' formulas.  If the formula given is
   not ICP friendly, then we return ICP_NO_PROGRESS. *)

fun icp_on_fml (f, limit) =
    case icp_friendly f of
	ICP_FRIENDLY al => icp_on_al(al, limit)
      | ICP_UNFRIENDLY => ICP_NO_PROGRESS;

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

 val a0 = ("=", [Term.Fn("+", [Term.Var "x", Term.Var "y"]), Term.Fn("-", [Term.Var "z", Term.Var "y"])]) : Atom.atom;
 val a1 = (">", [Term.Fn("*", [Term.Var "x", Term.Rat (Rat.rat_of_int 10)]), Term.Var "z"]) : Atom.atom;
 val a2 = ("<", [Term.Var "x", Term.Rat (Rat.rat_of_int 100)]);
 val a21 = (">", [Term.Var "x", Term.Rat(Rat.rat_of_int 99)]);
 val a3 = (">=", [Term.Var "y", Term.Var "x"]);
 val a4 = (">=", [Term.Var "z", Term.Var "y"]);
 val a5 = (">", [Term.Var "z", Term.Rat(Rat.rat_of_int 1000)]);
 val al = [a0, a1, a2, a21, a3, a4, a5];
 val a6 = ("=", [Term.Fn("*", [Term.Fn("x", []), Term.Fn("x", [])]), Term.Rat (Rat.rat_of_int 2)]);
 al_to_pcl(al);
 icp_on_al(al, 100);
*)


end
