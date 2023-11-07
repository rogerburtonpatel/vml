structure Unit :> sig
  val checkExpectWith : (''a -> string) -> string -> (unit -> ''a) -> ''a -> unit
    (* Calling `checkExpectWith show name test result` has these effects:
        Expression `test()` is evaluated, and the result is compared
        with `result`.  If they are equal, the test passes; otherwise it fails.
        If the test fails, `name` is used to identify the failing test.
    *)

  val intString : int -> string
  val stringString : string -> string
  val boolString : bool -> string

  val listString : ('a -> string) -> ('a list -> string)
  val optionString : ('a -> string) -> ('a option -> string)
  val pairString : ('a -> string) -> ('b -> string) -> ('a * 'b -> string)
  val valueString : 'a -> string   (* just says "a value" *)


  val checkAssert : string -> (unit -> bool) -> unit
    (* Calling `checkAssert name test` has these effects:
        Expression `test()` is evaluated, and if the result is `true`,
        the test passes; otherwise it fails.  If the test fails, `name`
        is used to identify the failing test.
    *)

  val checkExnWith : ('a -> string) -> string -> (unit -> 'a) -> unit
    (* Calling `checkExn show name test` has these effects:
        Expression `test()` is evaluated, and if it raises an exception,
        the test passes.  If `test()` returns a value, the test fails.
        If the test fails, `name` is used to identify the failing test.
    *)

  val checkExnSatisfiesWith : ('a -> string) -> string -> (unit -> 'a) -> (string * (exn -> bool)) -> unit
    (* Calling `checkExnSatisfiesWith show name test (ename, predicate)` 
      has these effects:
        Expression `test()` is evaluated, and if it raises an exception `e`,
        the test passes, provided `predicate e` is true.  If `test()` raises
        a non-satisfying exception, or if `test()` returns a value, the test fails,
        complaining that exception `ename` was expected.
        If the test fails, `name` is used to identify the failing test.

        Example:
            checkExnSatisfiesWith
                Int.toString
                "sum of big ints overflows"
                (fn () => valOf Int.maxInt + valOf Int.maxInt)
                ("Overflow", fn Overflow => true | _ => false)
    *)


  val report : unit -> unit
    (* If any tests were run, print, on standard output, a report of what passed. *)

  val reportWhenFailures : unit -> unit
    (* If any tests failed, print, on standard output,
      a report of what did and did not pass. *)

end
  = 
struct 
  val ran = ref 0
  val passed = ref 0

  fun eprint   s = TextIO.output (TextIO.stdErr, s)
  fun eprintln s = (eprint s; eprint "\n")

  fun passTest () = (ran := !ran + 1; passed := !passed + 1)
  fun failTest msgs = (ran := !ran + 1; app eprint msgs; eprint "\n")

  fun checkExpectWith show name thunk a =
    let val a' = thunk ()
    in  if a' = a then
          passTest ()
        else
          failTest ["In test '", name, "', expected value ", show a, " but got ", show a']
    end handle e =>
      failTest ["In test '", name, "', expected value ", show a, " but got exception ", exnName e]

  fun checkAssert name thunk =
    let val a' = thunk ()
    in  if a' then
          passTest ()
        else
          failTest ["In test '", name, "', the assertion was not satisfied"]
    end handle e =>
      failTest ["In test '", name, "', the assertion raised exception ", exnName e]

  fun checkExnSatisfiesWith show name thunk (ename, pred) =
    let val a' = thunk ()
    in  failTest ["In test '", name, "', expected exception ", ename,
                  " but got value ", show a']
    end handle e =>
      if pred e then
        passTest ()
      else
        failTest ["In test '", name, "', expected exception ", ename,
                  " but got some other exception named ", exnName e]

  fun checkExnWith show name thunk =
    checkExnSatisfiesWith show name thunk ("any exception", fn _ => true)


  fun reportTestResultsOf what (npassed, nthings) =
    case (npassed, nthings)
      of (_, 0) => ()  (* no report *)
      | (0, 1) => eprintln ("The only " ^ what ^ " failed.")
      | (1, 1) => eprintln ("The only " ^ what ^ " passed.")
      | (0, 2) => eprintln ("Both " ^ what ^ "s failed.")
      | (1, 2) => eprintln ("One of two " ^ what ^ "s passed.")
      | (2, 2) => eprintln ("Both " ^ what ^ "s passed.")
      | _ => if npassed = nthings then
                app eprint ["All ", Int.toString nthings, " " ^ what ^ "s passed.\n"]
              else if npassed = 0 then
                app eprint ["All ", Int.toString nthings, " " ^ what ^ "s failed.\n"]
              else
                app eprint [Int.toString npassed, " of ", Int.toString nthings,
                            " " ^ what ^ "s passed.\n"]

  fun report () = reportTestResultsOf "internal Unit test" (!passed, !ran)

  fun reportWhenFailures () =
    if !passed <> !ran then
      reportTestResultsOf "internal Unit test" (!passed, !ran)
    else
      ()



  fun listString _ [] = "[]"
    | listString show (x::xs) =
        concat ("[" :: show x :: foldr (fn (y, tail) => ", " :: show y :: tail) ["]"] xs)

  fun optionString show NONE = "NONE"
    | optionString show (SOME x) = "SOME (" ^ show x ^ ")"

  fun pairString showa showb (a, b) = "(" ^ showa a ^ ", " ^ showb b ^ ")"

  fun valueString _ = "a value"

  val intString = Int.toString
  val stringString = fn s => "\"" ^ String.toCString s ^ "\""
  val boolString = Bool.toString

end 