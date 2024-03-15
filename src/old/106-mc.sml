signature DECISION_TREE = sig
  (* Describes the target of match compilation, a data structure that
     can be visualized *)
  type register
  type arity = int
  type labeled_constructor = Pattern.vcon * arity
  type pat = Pattern.pat
  datatype 'a tree = TEST      of register * 'a edge list * 'a tree option
                   | LET_CHILD of (register * int) * (register -> 'a tree)
                                            (* ^ slot number *)
                   | MATCH     of 'a * register Env.env
  and      'a edge = E of labeled_constructor * 'a tree
end

functor MatchCompiler (eqtype register
                       val regString : register -> string)
  : 
sig
  include DECISION_TREE
  val decisionTree : register * (pat * 'a) list -> 'a tree
    (* register argument is the register that will hold
       the value of the scrutinee. *)
end
  =
struct
  structure P = Pattern
  structure LU = ListUtil

  fun fst (x, y) = x
  fun snd (x, y) = y
  infixr 0 $
  fun f $ g = f g


  (************** BASIC DATA STRUCTURES *************)

  type register = register
  type arity = int
  type labeled_constructor = Pattern.vcon * arity
  type pat = Pattern.pat
  datatype 'a tree = TEST      of register * 'a edge list * 'a tree option
                   | LET_CHILD of (register * int) * (register -> 'a tree)
                   | MATCH     of 'a * register Env.env
  and      'a edge = E of labeled_constructor * 'a tree

  datatype path = REGISTER of register | CHILD of register * int
    (* in order to match block slots, children should be numbered from 1 *)

  type constraint = path * pat
    (* (π, p) is satisfied if the subject subtree at path π matches p *)

  datatype 'a frontier = F of 'a * constraint list
    (* A frontier holds a set of constraints that apply to the scrutinee.

       A choice's initial frontier has just one contraint: [(root, p)],
       where root is the scrutinee register and p is the original pattern
       in the source code.

       A choice is known to match the scrutinee if its frontier
       contains only constraints of the form (REGISTER t, VAR x).
       These constraints show in which register each bound name is stored.
    
       The key operation on frontiers is *refinement* (called `project`
       in the paper).  Refing revises the constraints under the assumption
       that a given register holds an application of a given labeled_constructor 
     *)

  datatype 'a compatibility = INCOMPATIBLE | COMPATIBLE of 'a
   (* Any given point in the decision tree represents knowledge
      about the scrutinee.  At that point, a constraint or a frontier
      may be compatible with that knowledge or incompatible *)

  val mapCompatible : ('a -> 'b compatibility) -> ('a list -> 'b list) =
    (* applies a function to each element of a list; keeps only compatible results *)
    fn f =>
      foldr (fn (a, bs) => case f a of COMPATIBLE b => b :: bs | INCOMPATIBLE => bs) []
           
  val compatibilityConcat : 'a list compatibility list -> 'a list compatibility =
    (* Like List.concat, but result is compatible only if all args are compatible *)
    fn zs =>
      foldr (fn (COMPATIBLE xs, COMPATIBLE ys) => COMPATIBLE (xs @ ys)
              | _ => INCOMPATIBLE)
            (COMPATIBLE [])
            zs



  (************* DEBUGGING SUPPORT ****************)

  val eprint = IOUtil.output TextIO.stdErr

  val patString = WppScheme.patString
  fun pathString (REGISTER r) = regString r
    | pathString (CHILD (r, i)) = regString r ^ "." ^ Int.toString i

  fun frontierString (F (_, constraints)) =
    let fun conString (pi, p) = patString p ^ "@" ^ pathString pi
    in  String.concatWith " /\\ " (map conString constraints)
    end



  (************* DIRTY TRICKS *************)

  (* allow integer literals to masquerade as value constructors *)

  val maybeConstructed : constraint -> (path * P.vcon * pat list) option
    (* maybeConstructed (π, p) 
          = SOME (π, vcon, pats), when p is equivalent to P.APPLY (vcon, pats)
          = NONE                  otherwise
     *)
    = fn (pi, P.APPLY (vcon, pats)) => SOME (pi, vcon, pats)
       | _ => NONE


  (********** USEFUL OPERATIONS ON PATHS AND FRONTIERS ********)

  (* Function `patternAt` implements the @ operation from the paper.
     When `frontier` is `(i, f)`, f@π is `patternAt π frontier` *)

  val patternAt : path -> 'a frontier -> pat option =
    fn pi => fn (F (_, pairs)) =>
      let fun pathIs pi (pi', _) = pi = pi'
      in  Option.map snd (List.find (pathIs pi) pairs)
      end


  (* Substitution for paths: `(new forPath old)` returns
     a substitution function *)

  infix 0 forPath
  fun newPi forPath oldPi =
    let fun constraint (c as (pi, pat)) = if pi = oldPi then (newPi, pat) else c
    in  fn (F (i, constraints)) => F (i, map constraint constraints)
    end


  (************* FUNCTIONS YOU NEED TO WRITE ********)

  (* the match compiler *)

  fun refineConstraint r (vcon, arity) (constraint as (pi', pattern)) = 
    (case maybeConstructed constraint
      of SOME (path, vcon', pats) => 
        if pi' <> REGISTER r then 
           COMPATIBLE [constraint] 
        else if vcon = vcon' andalso arity = List.length pats then 
          (* let fun wildcardElim (i, P.WILDCARD) = (MATCH ) *)
          (* in  *)
           COMPATIBLE (ListUtil.mapi (fn (i, p) => (CHILD (r, i + 1), p)) pats)
          (* end *)
        else 
           INCOMPATIBLE
       | NONE => COMPATIBLE [constraint])

  val _ = refineConstraint :
        register -> labeled_constructor -> constraint -> constraint list compatibility
      (* assuming register r holds C/n,
            refineConstraint r C/n (π, p)
         returns the refinement of constraint (π, p),
         provided p is compatible with C/n at π
       *)


(* frontier is the part of the scrutinee you haven't matched yet *)
(* it was right! *)
  fun refineFrontier r labeled_con (F (rule, constraints)) = 
    let 
        val all_constraints = 
        (* val refinedWithWildcardElim = List.filter (fn (_, p) => case p of P.WILDCARD => false | _ => true) constraints *)
     compatibilityConcat (List.map (refineConstraint r labeled_con) constraints)
    in case all_constraints
         of COMPATIBLE cs => SOME (F (rule, cs))
          | INCOMPATIBLE => NONE
    end

  (* fun optionString s NONE = "NONE"
  | optionString s (SOME x) = "SOME (" ^ s x ^ ")"

  fun conString (vcon, arity) = vcon ^ "/" ^ Int.toString arity

  val refineFrontier = fn r => fn con => fn frontier =>
    let val () = app eprint ["Refining ", frontierString frontier, " at register ", 
                              regString r, " with constructor ", conString con, "\n" ]
        val result = refineFrontier r con frontier
        val () = app eprint ["result is ", optionString frontierString result, "\n"]
        in  result
        end *)

  val _ = refineFrontier :
        register -> labeled_constructor -> 'a frontier -> 'a frontier option
      (* returns the refinement of the given frontier, if compatible
       *)
  fun asReg (REGISTER r) k = k r
    | asReg (CHILD c)    k = LET_CHILD (c, k)

  (* here's where we do wildcard elim. *)
  fun registerize [] k = k Env.empty
    | registerize ((pi, P.WILDCARD)::pairs) k = registerize pairs k
    | registerize ((pi, P.VAR x)::pairs) k = 
       asReg pi (fn t => registerize pairs (fn env => k (Env.bind (x, t, env))))
    | registerize ((_, pat)::_) _ = Impossible.impossible ("non-VAR `" ^
                                         WppScheme.patString pat ^ "` at MATCH")

  (* thank you to norman for this one! *)
  fun anyApplication (F (_, pairs)) = 
        Option.join (List.find isSome (map maybeConstructed pairs))

  infix 0 forPath 
  fun newPath forPath oldPath = 
    let fun constraint (c as (pi, pattern)) = if pi = oldPath then 
                                                (newPath, pattern) 
                                              else c
    in fn (F (i, constraints)) => F (i, map constraint constraints)
    end

  fun nub xs = Set.elems $ Set.ofList xs

  fun constructorAppliedAt pi frontier =
    case patternAt pi frontier
      of SOME (Pattern.APPLY (vcon, ps)) => SOME (vcon, List.length ps)
       | _ => NONE

  fun unconstraintedAt pi frontier = 
     case patternAt pi frontier
      of SOME (Pattern.VAR _)  => true
       | SOME Pattern.WILDCARD => 
          Impossible.impossible "wildcard presence violates invariant!"
       | NONE => true
       | SOME _ => false

  (* this is pretty much all nr's code, with some renaming to more closely 
     match (haha) the paper *)
  fun compile [] = Impossible.impossible "no frontiers to compile in MC"
    | compile (frontiers as (first::_)) = 
        case anyApplication first 
          of SOME (CHILD (reg, i), _, _) =>
            LET_CHILD ((reg, i), fn t => 
                    compile (map (REGISTER t forPath CHILD (reg, i)) frontiers))
          | SOME (pi as REGISTER reg, _, _) => 
                 let val cs = nub (List.mapPartial (constructorAppliedAt pi) 
                                                   frontiers)
                     fun subtreeAt con = compile (List.mapPartial 
                                                      (refineFrontier reg con) 
                                                      frontiers)
                     val edges = map (fn con => E (con, subtreeAt con)) cs
                     val defaults = List.filter (unconstraintedAt pi) frontiers
                     val defaultTree = if null defaults then 
                                          NONE 
                                       else 
                                          SOME (compile defaults)
                  in TEST (reg, edges, defaultTree)
                  end
          | NONE => (* match node! *)
            let val F (rule, pairs) = first 
            in  registerize pairs (fn env => MATCH (rule, env))
            end


  val _ = compile : 'a frontier list -> 'a tree 

  fun decisionTree (reg, choices) =
    let fun frontier (P.WILDCARD, e) = F (e, []) (* norman's wildcard elim *)
          | frontier (pattern, e)    = F (e, [(REGISTER reg, pattern)])
    in compile (List.map frontier choices)
    end 

end




