(* ========================================================================= *)
(* SUPPORT FOR LAZY EVALUATION                                               *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

signature Lazy =
sig

type 'a lazy

val quickly : 'a -> 'a lazy

val delay : (unit -> 'a) -> 'a lazy

val force : 'a lazy -> 'a

val memoize : (unit -> 'a) -> unit -> 'a

end
