signature PRODUCER = sig
  type input
  type 'a error = 'a Error.error
  type 'a producer
  type 'a producer_fun = input list -> ('a error * input list) option

  val asFunction : 'a producer     -> 'a producer_fun
  val ofFunction : 'a producer_fun -> 'a producer

  val produce : 'a producer -> input list -> 'a error
    (* consumes the entire list to produce a single 'a, or errors *)


  (* main builders: applicative functor plus alternative *)
  val succeed : 'a -> 'a producer
  val <*> : ('a -> 'b) producer * 'a producer -> 'b producer
  val <$> : ('a -> 'b) * 'a producer -> 'b producer
  val <|> : 'a producer * 'a producer -> 'a producer

  (* shortcuts for parsing something and dropping the result *)
  val <~> : 'a producer * 'b producer -> 'a producer
  val >>  : 'a producer * 'b producer -> 'b producer

  (* conditional parsing *)
  val sat   : ('a -> bool)      -> 'a producer -> 'a producer
  val maybe : ('a -> 'b option) -> 'a producer -> 'b producer

  val eos : unit producer   (* end of stream *)
  val one : input producer  (* one token *)

  (* classic EBNF, plus "one or more" *)
  val optional : 'a producer -> 'a option producer
  val many  : 'a producer -> 'a list producer
  val many1 : 'a producer -> 'a list producer


  (* check for a semantic error, turn it into a syntax error *)
  val check : 'a error producer -> 'a producer


  (* occasionally useful *)
  val pzero : 'a producer (* always fails *)
  val perror : string -> 'a producer (* always errors *)

  (* for special things *)
  val notFollowedBy : 'a producer -> unit producer

  (* recursive parsers *)
  val fix : ('a producer -> 'a producer) -> 'a producer   (* for usage see below *)
     (* law: fix f tokens == f (fix f) tokens *)

  (* useful for building semantic functions *)
  val id   : 'a -> 'a
  val fst  : 'a * 'b -> 'a
  val snd  : 'a * 'b -> 'b
  val pair : 'a -> 'b -> 'a * 'b
  val triple : 'a -> 'b -> 'c -> 'a * 'b * 'c
  val eq   : ''a -> ''a -> bool

  val curry  : ('a * 'b      -> 'c) -> ('a -> 'b -> 'c)
  val curry3 : ('a * 'b * 'c -> 'd) -> ('a -> 'b -> 'c -> 'd)


  (* useful for wrapping producers, e.g., for debugging *)
  val transformWith :
        ('a producer_fun -> 'a producer_fun) -> ('a producer -> 'a producer)

end


(******* Using the fixed-point combinators *****

Suppose you want to define a recursive parser for an evaluator of
sums, like this:

    exp = int <|> succeed plus <~> the "(" <*> exp <~> the "+" <*> exp <~> the ")"

where `fun plus x y = x + y`.

You can't write this in ML.  But you can use a fixed-point combinator
that is just like the Y combinator in the lambda calculus.  First,
turn the recursion equation into a function that, when given `exp`,
returns `exp`:

    exp =  int <|> succeed plus <~> the "(" <*> exp <~> the "+" <*> exp <~> the ")"

 fn exp => int <|> succeed plus <~> the "(" <*> exp <~> the "+" <*> exp <~> the ")"

Then pass the whole thing to `fix`:
  
 fix (fn exp => int <|> succeed plus <~> the "(" <*> exp <~> the "+" <*> exp <~> the ")")

The result is your parser.

(The knot is tied using a mutable reference cell that is deferenced every
time tokens are delivered, so it's reasonably efficient.)

*)



functor MkListProducer(val species : string  (* identifies the producer *)
                       type input
                       val show : input list -> string
                      ) :> PRODUCER where type input = input
  =
struct
  fun curry f x y = f (x, y)
  fun fst (x, y) = x
  fun snd (x, y) = y
  fun id x = x
  fun pair x y = (x, y)
  fun triple x y z = (x, y, z)
  fun curry3 f x y z = f (x, y, z)
  fun eq x y = x = y

  type input = input
  structure E = Error
  type 'a error = 'a E.error
  
  type 'a producer_fun = input list -> ('a error * input list) option
  type 'a producer = 'a producer_fun
  fun asFunction p = p
  fun ofFunction f = f
  fun transformWith t = t

  fun produce p inputs =
    case p inputs
      of NONE => E.ERROR (species ^ " did not recognize this input: " ^ show inputs)
       | SOME (a, []) => a
       | SOME (a, leftover) =>
           let val outcome =
                 case a
                   of E.ERROR s => " failed with error \"" ^ s ^ "\" at input: "
                    | _ => " succeeded but did not consume this input: "
           in  E.ERROR (species ^ outcome ^ show leftover)
           end

  fun succeed y = fn xs => SOME (E.OK y, xs)


  infix 3 <*>
  fun tx_f <*> tx_b =
    fn xs => case tx_f xs
               of NONE => NONE
                | SOME (E.ERROR msg, xs) => SOME (E.ERROR msg, xs)
                | SOME (E.OK f, xs) =>
                    case tx_b xs
                      of NONE => NONE
                       | SOME (E.ERROR msg, xs) => SOME (E.ERROR msg, xs)
                       | SOME (E.OK y, xs) => SOME (E.OK (f y), xs)

  infixr 4 <$>
  fun f <$> p = succeed f <*> p

  (* val _ = <$> : ('a -> 'b) -> 'a parser -> 'b parser *)


  infix 1 <|>
  fun t1 <|> t2 = (fn xs => case t1 xs of SOME y => SOME y | NONE => t2 xs) 
            

  fun pzero _ = NONE
  fun perror msg ts = SOME (E.ERROR msg, ts)

  infix 6 <~> >>
  fun p1 <~> p2 = curry fst <$> p1 <*> p2
  fun p1  >> p2 = curry snd <$> p1 <*> p2

  fun one [] = NONE
    | one (y :: ys) = SOME (E.OK y, ys)

  fun eos []       = SOME (E.OK (), [])
    | eos (_ :: _) = NONE

  fun sat p tx xs =
    case tx xs
      of answer as SOME (E.OK y, xs) => if p y then answer else NONE
       | answer => answer

  fun maybe f tx xs =
    case tx xs
      of SOME (E.OK y, xs) =>
           (case f y of SOME z => SOME (E.OK z, xs) | NONE => NONE)
       | SOME (E.ERROR msg, xs) => SOME (E.ERROR msg, xs)
       | NONE => NONE

  fun notFollowedBy t xs =
    case t xs
      of NONE => SOME (E.OK (), xs)
       | SOME _ => NONE

  fun many t = 
    curry (op ::) <$> t <*> (fn xs => many t xs) <|> succeed []

  fun many1 t = 
    curry (op ::) <$> t <*> many t

  fun optional t = 
    SOME <$> t <|> succeed NONE

  fun check p xs =
    Option.map (fn (result, xs) => (Error.join result, xs)) (p xs)

  fun fix mk_p =
    let fun diverge tokens = diverge tokens
        val cell = ref diverge
        val parser = mk_p (fn ts => ! cell ts)
                      (* delay ! until after tokens are delivered,
                         therefore until after cell is updated *)
        val _ = cell := parser
    in  parser
    end

  infix 0 ===

  fun p1 === p2 = (fn tokens => p1 tokens = p2 tokens)


  fun maybe_sat_law f p =
        maybe f p === valOf <$> sat isSome p

  fun demo showToken =
    let
    fun expected what =
      let fun bad t = Error.ERROR ("expected " ^ what ^
                                   ", but instead found this token: " ^ showToken t)
      in check (  bad <$> one
              <|> perror ("expected " ^ what ^ ", but there was no more input")
               )
      end
    in expected
    end

end
