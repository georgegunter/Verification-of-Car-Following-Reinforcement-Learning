(* ========================================================================= *)
(* POLYML SPECIFIC FUNCTIONS                                                 *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

CM.autoload "$smlnj/init/init.cmi";

structure Portable :> Portable =
struct

(* ------------------------------------------------------------------------- *)
(* The ML implementation.                                                    *)
(* ------------------------------------------------------------------------- *)

val ml = "SmlNJ";

(* ------------------------------------------------------------------------- *)
(* Pointer equality using the run-time system.                               *)
(* ------------------------------------------------------------------------- *)

fun pointerEqual (x : 'a, y : 'a) = InlineT.ptreql (x,y);

(* ------------------------------------------------------------------------- *)
(* Timing function applications a la Mosml.time.                             *)
(* ------------------------------------------------------------------------- *)

fun time f x =
  let
    fun p t =
      let
        val s = Time.fmt 3 t
      in
        case size (List.last (String.fields (fn x => x = #".") s)) of 3 => s
        | 2 => s ^ "0"
        | 1 => s ^ "00"
        | _ => raise Fail "Portable.time"
      end

    val c = Timer.startCPUTimer ()

    val r = Timer.startRealTimer ()

    fun pt () =
      let
            val {usr,sys} = Timer.checkCPUTimer c
        val real = Timer.checkRealTimer r
      in
        print
        ("User: " ^ p usr ^ "  System: " ^ p sys ^
         "  Real: " ^ p real ^ "\n")
      end

    val y = f x handle e => (pt (); raise e)

    val () = pt ()
  in
    y
  end;

(* ------------------------------------------------------------------------- *)
(* Generating random values.                                                 *)
(* ------------------------------------------------------------------------- *)

local
  val gen = Random.newgenseed 1.0;
in
  fun randomInt max = Random.range (0,max) gen;

  fun randomReal () = Random.random gen;
end;

fun randomBool () = randomInt 2 = 0;

fun randomWord () =
    let
      val h = Word.fromInt (randomInt 65536)
      and l = Word.fromInt (randomInt 65536)
    in
      Word.orb (Word.<< (h,0w16), l)
end;

end

(* ------------------------------------------------------------------------- *)
(* Quotations a la Moscow ML.                                                *)
(* ------------------------------------------------------------------------- *)

datatype 'a frag = QUOTE of string | ANTIQUOTE of 'a;
