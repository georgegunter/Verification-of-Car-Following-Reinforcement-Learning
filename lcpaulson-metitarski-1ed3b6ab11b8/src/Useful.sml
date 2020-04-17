(* ========================================================================= *)
(* ML UTILITY FUNCTIONS                                                      *)
(* Copyright (c) 2001 Joe Hurd, distributed under the MIT license            *)

(* ========================================================================= *)

structure Useful :> Useful =
struct

(* ------------------------------------------------------------------------- *)
(* Exceptions.                                                               *)
(* ------------------------------------------------------------------------- *)

exception Error of string;

exception Bug of string;

fun errorToString (Error message) = "\nError: " ^ message ^ "\n"
  | errorToString _ = raise Bug "errorToString: not an Error exception";

fun bugToString (Bug message) = "\nBug: " ^ message ^ "\n"
  | bugToString _ = raise Bug "bugToString: not a Bug exception";

fun total f x = SOME (f x) handle Error _ => NONE;

fun can f = Option.isSome o total f;

(* ------------------------------------------------------------------------- *)
(* Combinators.                                                              *)
(* ------------------------------------------------------------------------- *)

fun C f x y = f y x;

fun I x = x;

fun K x y = x;

fun S f g x = f x (g x);

fun W f x = f x x;

fun funpow 0 _ x = x
  | funpow n f x = funpow (n - 1) f (f x);

fun exp m =
    let
      fun f _ 0 z = z
        | f x y z = f (m (x,x)) (y div 2) (if y mod 2 = 0 then z else m (z,x))
    in
      f
    end;

fun orf p q x = p x orelse q x;

fun andf p q x = p x andalso q x;

(* ------------------------------------------------------------------------- *)
(* Pairs.                                                                    *)
(* ------------------------------------------------------------------------- *)

fun fst (x,_) = x;

fun snd (_,y) = y;

fun pair x y = (x,y);

fun swap (x,y) = (y,x);

fun curry f x y = f (x,y);

fun uncurry f (x,y) = f x y;

val op## = fn (f,g) => fn (x,y) => (f x, g y);

(* ------------------------------------------------------------------------- *)
(* State transformers.                                                       *)
(* ------------------------------------------------------------------------- *)

val unit : 'a -> 's -> 'a * 's = pair;

fun bind f (g : 'a -> 's -> 'b * 's) = uncurry g o f;

fun mmap f (m : 's -> 'a * 's) = bind m (unit o f);

fun mjoin (f : 's -> ('s -> 'a * 's) * 's) = bind f I;

fun mwhile c b = let fun f a = if c a then bind (b a) f else unit a in f end;

(* ------------------------------------------------------------------------- *)
(* Equality.                                                                 *)
(* ------------------------------------------------------------------------- *)

val equal = fn x => fn y => x = y;

val notEqual = fn x => fn y => x <> y;

fun listEqual xEq =
    let
      fun xsEq [] [] = true
        | xsEq (x1 :: xs1) (x2 :: xs2) = xEq x1 x2 andalso xsEq xs1 xs2
        | xsEq _ _ = false
    in
      xsEq
    end;

(* ------------------------------------------------------------------------- *)
(* Comparisons.                                                              *)
(* ------------------------------------------------------------------------- *)

fun mapCompare f cmp (a,b) = cmp (f a, f b);

fun revCompare cmp x_y =
    case cmp x_y of LESS => GREATER | EQUAL => EQUAL | GREATER => LESS;

fun prodCompare xCmp yCmp ((x1,y1),(x2,y2)) =
    case xCmp (x1,x2) of
      LESS => LESS
    | EQUAL => yCmp (y1,y2)
    | GREATER => GREATER;

fun lexCompare cmp =
    let
      fun lex ([],[]) = EQUAL
        | lex ([], _ :: _) = LESS
        | lex (_ :: _, []) = GREATER
        | lex (x :: xs, y :: ys) =
          case cmp (x,y) of
            LESS => LESS
          | EQUAL => lex (xs,ys)
          | GREATER => GREATER
    in
      lex
    end;

fun optionCompare _ (NONE,NONE) = EQUAL
  | optionCompare _ (NONE,_) = LESS
  | optionCompare _ (_,NONE) = GREATER
  | optionCompare cmp (SOME x, SOME y) = cmp (x,y);

fun boolCompare (false,true) = LESS
  | boolCompare (true,false) = GREATER
  | boolCompare _ = EQUAL;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

fun cons x y = x :: y;

fun hdTl l = (hd l, tl l);

fun append xs ys = xs @ ys;

fun singleton a = [a];

fun first f [] = NONE
  | first f (x :: xs) = (case f x of NONE => first f xs | s => s);

fun maps (_ : 'a -> 's -> 'b * 's) [] = unit []
  | maps f (x :: xs) =
    bind (f x) (fn y => bind (maps f xs) (fn ys => unit (y :: ys)));

fun mapsPartial (_ : 'a -> 's -> 'b option * 's) [] = unit []
  | mapsPartial f (x :: xs) =
    bind
      (f x)
      (fn yo =>
          bind
            (mapsPartial f xs)
            (fn ys => unit (case yo of NONE => ys | SOME y => y :: ys)));

fun zipWith f =
    let
      fun z l [] [] = l
        | z l (x :: xs) (y :: ys) = z (f x y :: l) xs ys
        | z _ _ _ = raise Error "zipWith: lists different lengths";
    in
      fn xs => fn ys => rev (z [] xs ys)
    end;

fun zip xs ys = zipWith pair xs ys;

fun unzip ab =
    foldl (fn ((x, y), (xs, ys)) => (x :: xs, y :: ys)) ([], []) (rev ab);

fun cartwith f =
  let
    fun aux _ res _ [] = res
      | aux xsCopy res [] (_ :: yt) = aux xsCopy res xsCopy yt
      | aux xsCopy res (x :: xt) (ys as y :: _) =
        aux xsCopy (f x y :: res) xt ys
  in
    fn xs => fn ys =>
       let val xs' = rev xs in aux xs' [] xs' (rev ys) end
  end;

fun cart xs ys = cartwith pair xs ys;

fun takeWhile p =
    let
      fun f acc [] = rev acc
        | f acc (x :: xs) = if p x then f (x :: acc) xs else rev acc
    in
      f []
    end;

fun dropWhile p =
    let
      fun f [] = []
        | f (l as x :: xs) = if p x then f xs else l
    in
      f
    end;

fun divideWhile p =
    let
      fun f acc [] = (rev acc, [])
        | f acc (l as x :: xs) = if p x then f (x :: acc) xs else (rev acc, l)
    in
      f []
    end;

fun groups f =
    let
      fun group acc row x l =
          case l of
            [] =>
            let
              val acc = if null row then acc else rev row :: acc
            in
              rev acc
            end
          | h :: t =>
            let
              val (eor,x) = f (h,x)
            in
              if eor then group (rev row :: acc) [h] x t
              else group acc (h :: row) x t
            end
    in
      group [] []
    end;

fun groupsBy eq =
    let
      fun f (x_y as (x,_)) = (not (eq x_y), x)
    in
      fn [] => []
       | h :: t =>
         case groups f h t of
           [] => [[h]]
         | hs :: ts => (h :: hs) :: ts
    end;

local
  fun fstEq ((x,_),(y,_)) = x = y;

  fun collapse l = (fst (hd l), map snd l);
in
  fun groupsByFst l = map collapse (groupsBy fstEq l);
end;

fun groupsOf n =
    let
      fun f (_,i) = if i = 1 then (true,n) else (false, i - 1)
    in
      groups f (n + 1)
    end;

fun index p =
  let
    fun idx _ [] = NONE
      | idx n (x :: xs) = if p x then SOME n else idx (n + 1) xs
  in
    idx 0
  end;

fun enumerate l = fst (maps (fn x => fn m => ((m, x), m + 1)) l 0);

local
  fun revDiv acc l 0 = (acc,l)
    | revDiv _ [] _ = raise Subscript
    | revDiv acc (h :: t) n = revDiv (h :: acc) t (n - 1);
in
  fun revDivide l = revDiv [] l;
end;

fun divide l n = let val (a,b) = revDivide l n in (rev a, b) end;

fun updateNth (n,x) l =
    let
      val (a,b) = revDivide l n
    in
      case b of [] => raise Subscript | _ :: t => List.revAppend (a, x :: t)
    end;

fun deleteNth n l =
    let
      val (a,b) = revDivide l n
    in
      case b of [] => raise Subscript | _ :: t => List.revAppend (a,t)
    end;

(* ------------------------------------------------------------------------- *)
(* Sets implemented with lists.                                              *)
(* ------------------------------------------------------------------------- *)

fun mem x = List.exists (equal x);

fun insert x s = if mem x s then s else x :: s;

fun delete x s = List.filter (not o equal x) s;

fun setify s = rev (foldl (fn (v,x) => if mem v x then x else v :: x) [] s);

fun union s t = foldl (fn (v,x) => if mem v t then x else v :: x) t (rev s);

fun intersect s t =
    foldl (fn (v,x) => if mem v t then v :: x else x) [] (rev s);

fun difference s t =
    foldl (fn (v,x) => if mem v t then x else v :: x) [] (rev s);

fun subset s t = List.all (fn x => mem x t) s;

fun distinct [] = true
  | distinct (x :: rest) = not (mem x rest) andalso distinct rest;

(* ------------------------------------------------------------------------- *)
(* Sorting and searching.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Finding the minimum and maximum element of a list, wrt some order. *)

fun minimum cmp =
    let
      fun min (l,m,r) _ [] = (m, List.revAppend (l,r))
        | min (best as (_,m,_)) l (x :: r) =
          min (case cmp (x,m) of LESS => (l,x,r) | _ => best) (x :: l) r
    in
      fn [] => raise Empty
       | h :: t => min ([],h,t) [h] t
    end;

fun maximum cmp = minimum (revCompare cmp);

(* Merge (for the following merge-sort, but generally useful too). *)

fun merge cmp =
    let
      fun mrg acc [] ys = List.revAppend (acc,ys)
        | mrg acc xs [] = List.revAppend (acc,xs)
        | mrg acc (xs as x :: xt) (ys as y :: yt) =
          (case cmp (x,y) of
             GREATER => mrg (y :: acc) xs yt
           | _ => mrg (x :: acc) xt ys)
    in
      mrg []
    end;

(* Merge sort (stable). *)

fun sort cmp =
    let
      fun findRuns acc r rs [] = rev (rev (r :: rs) :: acc)
        | findRuns acc r rs (x :: xs) =
          case cmp (r,x) of
            GREATER => findRuns (rev (r :: rs) :: acc) x [] xs
          | _ => findRuns acc x (r :: rs) xs

      fun mergeAdj acc [] = rev acc
        | mergeAdj acc (xs as [_]) = List.revAppend (acc,xs)
        | mergeAdj acc (x :: y :: xs) = mergeAdj (merge cmp x y :: acc) xs

      fun mergePairs [xs] = xs
        | mergePairs l = mergePairs (mergeAdj [] l)
    in
      fn [] => []
       | l as [_] => l
       | h :: t => mergePairs (findRuns [] h [] t)
    end;

fun sortMap _ _ [] = []
  | sortMap _ _ (l as [_]) = l
  | sortMap f cmp xs =
    let
      fun ncmp ((m,_),(n,_)) = cmp (m,n)
      val nxs = map (fn x => (f x, x)) xs
      val nys = sort ncmp nxs
    in
      map snd nys
    end;

(* ------------------------------------------------------------------------- *)
(* Integers.                                                                 *)
(* ------------------------------------------------------------------------- *)

fun interval m 0 = []
  | interval m len = m :: interval (m + 1) (len - 1);

fun divides _ 0 = true
  | divides 0 _ = false
  | divides a b = b mod (Int.abs a) = 0;

local
  fun hcf 0 n = n
    | hcf 1 _ = 1
    | hcf m n = hcf (n mod m) m;
in
  fun gcd m n =
      let
        val m = Int.abs m
        and n = Int.abs n
      in
        if m < n then hcf m n else hcf n m
      end;
end;

local
  fun calcPrimes ps n i =
      if List.exists (fn p => divides p i) ps then calcPrimes ps n (i + 1)
      else
        let
          val ps = ps @ [i]
          and n = n - 1
        in
          if n = 0 then ps else calcPrimes ps n (i + 1)
        end;

  val primesList = ref [2];
in
  fun primes n =
      let
        val ref ps = primesList

        val k = n - length ps
      in
        if k <= 0 then List.take (ps,n)
        else
          let
            val ps = calcPrimes ps k (List.last ps + 1)

            val () = primesList := ps
          in
            ps
          end
      end;
end;

fun primesUpTo n =
    let
      fun f k =
          let
            val l = primes k

            val p = List.last l
          in
            if p < n then f (2 * k) else takeWhile (fn j => j <= n) l
          end
    in
      f 8
    end;

(* ------------------------------------------------------------------------- *)
(* Strings.                                                                  *)
(* ------------------------------------------------------------------------- *)

local
  fun len l = (length l, l)

  val upper = len (explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ");

  val lower = len (explode "abcdefghijklmnopqrstuvwxyz");

  fun rotate (n,l) c k =
      List.nth (l, (k + Option.valOf (index (equal c) l)) mod n);
in
  fun rot k c =
      if Char.isLower c then rotate lower c k
      else if Char.isUpper c then rotate upper c k
      else c;
end;

fun nChars x n = if n<0 then "" else CharVector.tabulate(n, fn _ => x) : string;

fun chomp s =
    let
      val n = size s
    in
      if n = 0 orelse String.sub (s, n - 1) <> #"\n" then s
      else String.substring (s, 0, n - 1)
    end;

local
  fun chop [] = []
    | chop (l as (h :: t)) = if Char.isSpace h then chop t else l;
in
  val trim = implode o chop o rev o chop o rev o explode;
end;

fun join _ [] = ""
  | join s (h :: t) = foldl (fn (x,y) => y ^ s ^ x) h t;

local
  fun match [] l = SOME l
    | match _ [] = NONE
    | match (x :: xs) (y :: ys) = if x = y then match xs ys else NONE;

  fun stringify acc [] = acc
    | stringify acc (h :: t) = stringify (implode h :: acc) t;
in
  fun split sep =
      let
        val pat = String.explode sep
        fun div1 prev recent [] = stringify [] (rev recent :: prev)
          | div1 prev recent (l as h :: t) =
            case match pat l of
              NONE => div1 prev (h :: recent) t
            | SOME rest => div1 (rev recent :: prev) [] rest
      in
        fn s => div1 [] [] (explode s)
      end;
end;

fun capitalize s =
    if s = "" then s
    else str (Char.toUpper (String.sub (s,0))) ^ String.extract (s,1,NONE);

fun mkPrefix p s = p ^ s;

fun destPrefix p =
    let
      fun check s = String.isPrefix p s orelse raise Error "destPrefix"

      val sizeP = size p
    in
      fn s => (check s; String.extract (s,sizeP,NONE))
    end;

fun isPrefix p = can (destPrefix p);

fun stripPrefix pred s = Substring.string (Substring.dropl pred (Substring.full s));

fun stripSuffix pred s = Substring.string (Substring.dropr pred (Substring.full s));

(* ------------------------------------------------------------------------- *)
(* Tables.                                                                   *)
(* ------------------------------------------------------------------------- *)

type columnAlignment = {leftAlign : bool, padChar : char}

fun alignColumn {leftAlign,padChar} column =
    let
      val (n,_) = maximum Int.compare (map size column)

      fun pad entry row =
          let
            val padding = nChars padChar (n - size entry)
          in
            if leftAlign then entry ^ padding ^ row
            else padding ^ entry ^ row
          end
    in
      zipWith pad column
    end;

local
  fun alignTab aligns rows =
      case aligns of
        [] => map (K "") rows
      | [{leftAlign = true, padChar = #" "}] => map hd rows
      | align :: aligns =>
        alignColumn align (map hd rows) (alignTab aligns (map tl rows));
in
  fun alignTable aligns rows =
      if null rows then [] else alignTab aligns rows;
end;

(* ------------------------------------------------------------------------- *)
(* Reals.                                                                    *)
(* ------------------------------------------------------------------------- *)

(*Real number formatting with the specified number of decimal digits*)
fun realToString d = Real.fmt (StringCvt.FIX (SOME d));

fun percentToString x = Int.toString (Real.round (100.0 * x)) ^ "%";

fun pos r = Real.max (r,0.0);

local
  val invLn2 = 1.0 / Math.ln 2.0;
in
  fun log2 x = invLn2 * Math.ln x;
end;

(* ------------------------------------------------------------------------- *)
(* Sums.                                                                     *)
(* ------------------------------------------------------------------------- *)

datatype ('a,'b) sum = Left of 'a | Right of 'b

fun destLeft (Left l) = l
  | destLeft _ = raise Error "destLeft";

fun isLeft (Left _) = true
  | isLeft (Right _) = false;

fun destRight (Right r) = r
  | destRight _ = raise Error "destRight";

fun isRight (Left _) = false
  | isRight (Right _) = true;

(* ------------------------------------------------------------------------- *)
(* Useful impure features.                                                   *)
(* ------------------------------------------------------------------------- *)

local
  val generator = ref 0
in
  fun newInt () =
      let
        val n = !generator
        val () = generator := n + 1
      in
        n
      end;

  fun newInts 0 = []
    | newInts k =
      let
        val n = !generator
        val () = generator := n + k
      in
        interval n k
      end;
end;

fun withRef (r,new) f x =
  let
    val old = !r
    val () = r := new
    val y = f x handle e => (r := old; raise e)
    val () = r := old
  in
    y
  end;

fun cloneArray a =
    let
      fun index i = Array.sub (a,i)
    in
      Array.tabulate (Array.length a, index)
    end;

(* ------------------------------------------------------------------------- *)
(* Environment.                                                              *)
(* ------------------------------------------------------------------------- *)

fun host () = Option.getOpt (OS.Process.getEnv "HOSTNAME", "unknown");

fun time () = Date.fmt "%H:%M:%S" (Date.fromTimeLocal (Time.now ()));

fun date () = Date.fmt "%d/%m/%Y" (Date.fromTimeLocal (Time.now ()));

fun readDirectory {directory = dir} =
    let
      val dirStrm = OS.FileSys.openDir dir

      fun readAll acc =
          case OS.FileSys.readDir dirStrm of
            NONE => acc
          | SOME file =>
            let
              val filename = OS.Path.joinDirFile {dir = dir, file = file}

              val acc = {filename = filename} :: acc
            in
              readAll acc
            end

      val filenames = readAll []

      val () = OS.FileSys.closeDir dirStrm
    in
      rev filenames
    end;

fun readTextFile {filename} =
  let
    open TextIO
    val h = openIn filename
    val contents = inputAll h
    val () = closeIn h
  in
    contents
  end;

fun writeTextFile {contents,filename} =
  let
    open TextIO
    val h = openOut filename
    val () = output (h,contents)
    val () = closeOut h
  in
    ()
  end;

(* ------------------------------------------------------------------------- *)
(* Profiling and error reporting.                                            *)
(* ------------------------------------------------------------------------- *)

val tracePrint = ref print;

val traceLevel = ref 1;

fun chatting l = (l <= !traceLevel);

fun trace message = !tracePrint message;

fun chat s = (TextIO.output (TextIO.stdErr, s ^ "\n"); true);

local
  fun err x s = chat (x ^ ": " ^ s);
in
  fun try f x = f x
      handle e as Error _ => (err "try" (errorToString e); raise e)
           | e as Bug _ => (err "try" (bugToString e); raise e)
           | e => (err "try" "strange exception raised"; raise e);

  val warn = ignore o err "WARNING";

  fun die s = (err "\nFATAL ERROR" s; OS.Process.exit OS.Process.failure);
end;

fun timed f a =
  let
    val tmr = Timer.startCPUTimer ()
    val res = f a
    val {usr,sys,...} = Timer.checkCPUTimer tmr
  in
    (Time.toReal usr + Time.toReal sys, res)
  end;

local
  val MIN = 1.0;

  fun several n t f a =
    let
      val (t',res) = timed f a
      val t = t + t'
      val n = n + 1
    in
      if t > MIN then (t / Real.fromInt n, res) else several n t f a
    end;
in
  fun timedMany f a = several 0 0.0 f a
end;

val executionTime =
    let
      val startTime = Time.toReal (Time.now ())
    in
      fn () => Time.toReal (Time.now ()) - startTime
    end;

end
