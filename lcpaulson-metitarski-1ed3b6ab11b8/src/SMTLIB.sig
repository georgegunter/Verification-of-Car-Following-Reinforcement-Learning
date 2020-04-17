(* SMTLIB.sig *)
signature SMTLIB =
sig
val testTokenReading : string -> string -> unit
val testSExpressions : string -> string -> unit
val testInterpreter  : string -> string -> unit
val read : string -> Tptp.problem
val write : string -> Tptp.problem -> unit
val filter_tptp_file : string -> string
end
