structure DofVminus :> sig
  structure D : DECISION_TREE
  structure V : VMINUS
  val compile : 'a V.guarded_exp list -> 'a V.exp D.tree
end
  =
struct
  structure V = VMFn(structure A = Alpha)
  structure D = DecisionTree()


  datatype status = KNOWN | UNKNOWN  (* status of each bound variable *)
  
  val emptyContext = Env.empty

  fun compile context [] = Impossible.impossible "no choices"
    | compile context (choices as (V.ARROWALPHA e :: _)) =
         D.MATCH e
    | compile context choices =
        Impossible.unimp "match compiler"
 
(* to generate a decision-tree TEST node, we require an EQN that has a
   known name on the left and a constrcutor application on the right 

   to generate an IF node, an EQN with both sides known, or an EXPSEQ with a known exp
*)

  (* val findGoodConstructorApplication :  *)

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
