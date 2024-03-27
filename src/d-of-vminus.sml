structure DofVminus :> sig
  structure D : DECISION_TREE
  structure V : VMINUS
  exception Stuck of unit V.guarded_exp list
  val compile : 'a V.guarded_exp list -> 'a D.tree
end
  =
struct
  structure V = VMFn(structure A = Alpha)
  structure D = DecisionTree(type 'a exp = 'a V.exp
                             val expString = V.expString)

  exception Stuck of unit V.guarded_exp list


  val mapPartial = List.mapPartial

  datatype status = KNOWN | UNKNOWN  (* status of each bound variable *)
  
  val emptyContext = Env.empty

  type context = status Env.env

  fun addVar status x rho = Env.bind (x, status, rho)
  val _ = addVar : status -> V.name -> context -> context
  
  val makeKnown = addVar KNOWN
  fun known context x = Env.binds (context, x) 
                        andalso Env.find (x, context) = KNOWN

(* to generate a decision-tree TEST node, we require an EQN that has a
   known name on the left and a constrcutor application on the right 

   to generate an IF node, an EQN with both sides known, or an EXPSEQ with a known exp
*)

  val matchName :
      V.name -> (Core.vcon * 'a V.exp list) -> 'a V.guarded_exp -> 'a V.guarded_exp option
    = fn _ => Impossible.unimp "not yet"
  (*
     matchName (x = y :: ys) [[x = z :: zs --> e]] = SOME [[y = z, ys = zs --> e]]
     matchName (x = y :: ys) [[x = nil --> e]] = NONE
   *)

  (* fun member x xs = List.exists (fn y => x y ) *)

(* stuck says: can I solve this with the information I have now? 
i.e. do I have all the names I need to evaluate this expression? 
f is a function 'a -> bool, which lets us see if the final 'a is stuck. *)
val rec stuck : context -> ('a -> bool) -> 'a V.exp ->  bool = 
  fn ctx => fn f => fn ex => 
    let fun unknown n = if not (Env.binds (ctx, n)) then raise V.NameNotBound n 
                        else (Env.find (n, ctx)) = UNKNOWN
        fun has_unbound_names e = 
          case e of V.ALPHA a => f a 
           | V.NAME name => unknown name 
           | V.VCONAPP (v, es) => List.exists has_unbound_names es
           | V.FUNAPP (e1, e2) => has_unbound_names e1 orelse has_unbound_names e2 
           | V.IF_FI gs => List.exists has_unbound_gexp gs  
           | V.LAMBDAEXP (n, body) => 
                  stuck (Env.bind (n, KNOWN, ctx)) f body
        and has_unbound_gexp g = 
          case g of V.ARROWALPHA e    => has_unbound_names e
                  | V.EXISTS (_, g')  => has_unbound_gexp g'
                  | V.EXPSEQ (e', g') => has_unbound_names e' 
                                       orelse has_unbound_gexp g'
                  | V.EQN (n, e', g') => unknown n 
                                       orelse has_unbound_names e'
                                       orelse has_unbound_gexp g'
    in has_unbound_names ex 
  end 

  val rec findOneConstructorApplication : context -> 'a V.guarded_exp -> V.name option
    = fn ctx => fn gexp => 
    let fun findOneConapp g = 
       case g of 
            V.ARROWALPHA _      => NONE
          | V.EXISTS (n, g')    => findOneConstructorApplication (addVar UNKNOWN n ctx) g'
          | V.EXPSEQ (_, g')    => findOneConapp g'
          | V.EQN    (n, V.VCONAPP _, g') => if known ctx n then SOME n
                                             else findOneConapp g'
          | V.EQN    (_, _, g')           => findOneConapp g'
    (* return a known name that is equal to a VCONAPP *)
    in findOneConapp gexp 
    end 

  fun findAnyConstructorApplication context [] = NONE
    | findAnyConstructorApplication context (g::gs) =
        case findOneConstructorApplication context g
          of SOME answer => SOME answer
           | NONE => findAnyConstructorApplication context gs
  
  val _ : context -> 'a V.guarded_exp list -> V.name option
    = findAnyConstructorApplication

  val findAnyKnownRHS : context -> 'a V.guarded_exp list -> (V.name * 'a V.exp) option
    = fn _ => Impossible.unimp "not yet"

  val addEquality   : (V.name * 'a V.exp) -> 'a V.guarded_exp -> 'a V.guarded_exp option
    = fn (n, e) => 
      let exception BadEquality
          fun reduce g = 
            case g of 
              ar as V.ARROWALPHA e' => ar
            | V.EXPSEQ (e', g')     => 
                V.EXPSEQ (e', reduce g')
            | V.EXISTS (n', g')     => 
                V.EXISTS (n', reduce g')
            | V.EQN (n', e', g')    => 
                if n = n' andalso V.eqexp (e, e')
                then reduce g'
                else raise BadEquality
    in fn g =>
      SOME (reduce g)
      handle
        BadEquality => NONE
    end  

  val addInequality : (V.name * 'a V.exp) -> 'a V.guarded_exp -> 'a V.guarded_exp option
    = fn (n, e) => 
      let exception BadInequality
          fun reduce g = 
            case g of 
              ar as V.ARROWALPHA e' => ar
            | V.EXPSEQ (e', g')     => 
                V.EXPSEQ (e', reduce g')
            | V.EXISTS (n', g')     => 
                V.EXISTS (n', reduce g')
            | V.EQN (n', e', g')    => 
                if n = n' andalso V.eqexp (e, e')
                then raise BadInequality
                else reduce g'
    in fn g =>
      SOME (reduce g)
      handle
        BadInequality => NONE
    end  

  (*  *)
  val ifEq : (V.name * 'a V.exp) -> 'a D.tree -> 'a D.tree -> 'a D.tree
    = fn (n, e) => fn tbranch => fn fbranch => 
    let val c = FreshName.freshNameGen ()
    in 
      D.LET (c, (Impossible.unimp "n = e"), D.IF (c, tbranch, fbranch))
    end 

  val nameExp : 'a V.exp -> V.name -> 'a V.guarded_exp -> 'a V.guarded_exp   
    (* nameExp (x, e) replaces all occurrences of e with x *)
    = fn e => 
    fn n => 
    let fun replace g = 
      case g of 
              ar as V.ARROWALPHA e' => V.ARROWALPHA (swapIfEq e e')
            | V.EXPSEQ (e', g') => 
                V.EXPSEQ (swapIfEq e e', replace g')
            | V.EXISTS (n', g') => V.EXISTS (n', replace g')
            | V.EQN (n', e', g') => 
                V.EQN (n', swapIfEq e e', replace g')

      and swapIfEq e1 e2 = if V.eqexp (e1, e2) then (V.NAME n) else e2
  in replace
  end  

  (* addEquality   (x, e) [[x = e, g]] = SOME [[g]]
     addInequality (x, e) [[x = e, g]] = NONE
   *)

        

(*
  KNOWN n, m
    if E x y . x = f n, x = SOME y -> launch
    [] #t -> stand down
    fi

  LET x = f n
  IN TEST x
      of SOME y => launch
       | _ => stand down

  KNOWN n, m
    if E x y . x = f n, x = SOME y -> launch
    [] E x   . x = f n, x = 3 -> cower
    [] #t -> stand down
    fi

  LET x = f n
  IN TEST x
      of SOME y => launch
       | _ => if x = 3 then cower
              else stand down
   

*)



  (* What can we find?

       ARROW  ==   if unguarded, MATCH
       SEQ    ==   if known, convert to LET, IF
       EQN (x, e) ==
          - if x is known and e is VCONAPP, generate TEST
          - if x is known and e is not VCONAPP and e is known
               generate LET, IF
          - if x is unknown and e is known, then generate LET
  *)


  (* don't love the case where x = e, and e is both VCONAPP and known *)



  fun compile context [] = Impossible.impossible "no choices"
    | compile context (choices as (V.ARROWALPHA e :: _)) =
         D.MATCH e  (* unguarded ARROW *)
    | compile context choices =
        (case findAnyConstructorApplication context choices (* x known, VCONAPP *)
           of SOME x =>
                D.TEST ( x
                       , Impossible.unimp "simplified g's, compiled"
                       , Option.map (compile context)
                                    (Impossible.unimp "g's that are 'none of the above'")
                       )
            | NONE =>
        (case findAnyKnownRHS context choices  (* e is known *)
           of SOME (x, rhs) =>
                if known context x then
                  ifEq (x, rhs) (compile context
                                         (mapPartial (addEquality   (x, rhs)) choices))
                                (compile context
                                         (mapPartial (addInequality (x, rhs)) choices))
                else
                  D.LET (x, rhs,
                         compile (addVar KNOWN x context)
                                 (map (nameExp rhs x) choices))
            | NONE =>
                raise Stuck (map (V.gmap (fn _ => ())) choices)))


  val compile = fn things => compile emptyContext things
     
(*

  fun compile fresh (root, []) = 
    | compile fresh (root, frontiers as (first :: _)) =
        case anyApplicationPath first
          of SOME x =>
               let val cons = nub (List.mapPartial (constructorAppliedAt x) frontiers)
                   val apps = map (appify fresh) cons

                   fun choiceFor (app : string * SP.atom list) =
                     let val frontiers = List.mapPartial (refineFrontier x app) frontiers
                         val app = dropUnconstrainedNames app frontiers
                         val subtree = compile fresh (x, frontiers)
                     in  (SP.APPLY app, subtree)
                     end

                   val defaults = List.filter (unconstrainedAt x) frontiers
                   val lastChoice = if null defaults then []
                                    else [(SP.ATOM SP.WILDCARD, compile fresh (x, defaults))]

                   val edges = foldr (fn (app, cs) => choiceFor app :: cs) lastChoice apps
               in  caseExp (var x, edges)
               end
           | NONE =>
               let val (e, c) = first
               in  registerize c (fn env => aliases (env, e))
               end
        
*)


end


(*
signature NEW_COMPILERX = sig
  eqtype name
  type exp
  type arity = int
  type pat = Pattern.pat
  type labeled_constructor = Pattern.vcon * arity
  datatype constraint
    = MATCHES of name * pat
    | /\- of constraint * constraint   (* conjunction *)  (* neither child is SATISFIED *)
    | SATISFIED

  val compile : (unit -> name) -> name * (exp * constraint) list -> exp
end

functor NewMatchCompilerX (type exp
                          type name = string
                          val caseExp : exp SimpleCase.t -> exp
                          val aliases : (name * name) list * exp -> exp
                          val var : string -> exp)
  : 
sig
  include NEW_COMPILER (* rab: why this? why not `: NEW_COMPILER =` ?*)
end
  =
struct
  structure P  = Pattern
  structure SP = SimplePattern
  structure LU = ListUtil

  type name = string
  type exp = exp
  type arity = int
  type pat = Pattern.pat
  type labeled_constructor = Pattern.vcon * arity

  datatype constraint
    = MATCHES of name * pat
    | /\- of constraint * constraint   (* conjunction *)  (* neither child is SATISFIED *)
    | SATISFIED

  infix 5 MATCHES
  infix 4 /\ /\- /\+

  fun SATISFIED /\ c = c
    | c /\ SATISFIED = c
    | c /\ c' = c /\- c'


  type frontier = exp * constraint

  type choice = SP.pat * frontier list

  (* compile : name * choice list -> exp *)

  datatype 'a matchable
    = MATCHABLE of 'a
    | UNMATCHABLE

  fun (MATCHABLE c) /\+ (MATCHABLE c') = MATCHABLE (c /\ c')
    | _ /\+ _ = UNMATCHABLE

  val _ = op /\+ : constraint matchable * constraint matchable -> constraint matchable

  val patternAt : name -> frontier -> pat option =
    fn x => fn (_, c) =>
      let fun at (y MATCHES p) = if y = x then SOME p else NONE
            | at (c /\- c') = (case at c of NONE => at c' | SOME pat => SOME pat)
            | at SATISFIED = NONE
      in  at c
      end

  fun constructorAppliedAt r f =
    case patternAt r f
     of SOME (P.APPLY (con, ps)) => SOME (con, length ps)
      | _ => NONE

  fun unconstrainedAt r f = not (isSome (constructorAppliedAt r f))

  fun refineConstraint x (con, atoms) =
        (* add knowledge "name matches SP.APPLY (con, atoms) *)
    let fun refine SATISFIED = MATCHABLE SATISFIED
          | refine (c /\- c') = refine c /\+ refine c'
          | refine (c as (y MATCHES P.APPLY (con', pats))) =
              if x <> y then
                  MATCHABLE c
              else if con <> con' orelse length pats <> length atoms then
                  UNMATCHABLE
              else
                  MATCHABLE
                    (ListPair.foldrEq (fn (SP.WILDCARD, P.WILDCARD, c) => c
                                        | (SP.WILDCARD, _, _) => Impossible.impossible "wildcard"
                                        | (SP.VAR x, p, c) => c /\ x MATCHES p)
                                      SATISFIED
                                      (atoms, pats))
          | refine (c as (y MATCHES _)) = MATCHABLE c
    in  refine
    end

  fun refineFrontier x p (e, c) =
    case refineConstraint x p c
      of MATCHABLE c => SOME (e, c)
       | UNMATCHABLE => NONE


  fun anyApplicationPath (_, c) =
    let fun path (x MATCHES P.APPLY _) = SOME x
          | path (_ MATCHES _)      = NONE
          | path SATISFIED     = NONE
          | path (c /\- c')    = (case path c of NONE => path c' | SOME pat => SOME pat)
    in  path c
    end

  val _ = anyApplicationPath : frontier -> name option

  type atom = SimplePattern.atom

  fun appify fresh (vcon, i) =
    let fun args 0 = []
          | args n = SP.VAR (fresh ()) :: args (n - 1)
    in  (vcon, args i)
    end

  fun addConstrainedNames (x MATCHES P.WILDCARD, xs) = xs
    | addConstrainedNames (x MATCHES _, xs) = Set.insert (x, xs)
    | addConstrainedNames (c /\- c', xs) = addConstrainedNames (c, addConstrainedNames (c', xs))
    | addConstrainedNames (SATISFIED, xs) = xs

  fun dropUnconstrainedNames (vcon, atoms) frontiers =
    let val constrained =
              foldl (fn ((_, c), xs) => addConstrainedNames (c, xs)) Set.empty frontiers
        val () = app IOUtil.eprint ["constrained: ", String.concatWith ", " (Set.elems constrained), "\n"]
        fun keep SP.WILDCARD = SP.WILDCARD
          | keep (SP.VAR x) = if Set.member (x, constrained) then SP.VAR x else SP.WILDCARD
    in  (vcon, map keep atoms)
    end

  fun registerize SATISFIED k = k []
    | registerize (x MATCHES P.VAR y) k = k [(y, x)]
    | registerize (x MATCHES P.WILDCARD) k = k []
    | registerize (x MATCHES P.APPLY _) k = Impossible.impossible "application at match node"
    | registerize (c /\- c') k =
        registerize c (fn env => registerize c' (fn env' => k (env @ env')))

  val _ = registerize : constraint -> ((name * name) list -> 'a) -> 'a


  fun nub xs = Set.elems (Set.ofList xs)



(*@ true*)
end




*)
