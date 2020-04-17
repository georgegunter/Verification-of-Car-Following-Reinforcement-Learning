(* Qepcad signature.
   Note: The Qepcad structure is now a subsidiary of the RCF structure. *)

signature Qepcad =
sig

val close_qepcad : bool -> unit;
val call_qepcad' : bool -> string list -> string list -> Formula.formula -> bool;
val call_qepcad'_ml : bool -> string list -> string list -> Formula.formula -> Common.tv;
val call_qepcad_sat : Formula.formula -> bool;
val qepcad_used : bool ref;
val qepcad_str : string list -> Formula.formula -> string;

end;
