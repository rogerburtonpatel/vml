structure DofVminus :> sig
  val defs : VMinus.def list -> D.def list
  exception Stuck of string
end
  =
struct

  structure V = DesugaredVMinus
  structure D = D
  structure C = Core

  type 'a guarded_exp = V.exp V.guard list * 'a

  exception Stuck of string

  fun unitify (gs, a) = (gs, ())
  val mapPartial = List.mapPartial
  fun curry f x y = f (x, y)
  infixr 0 $
  fun f $ g = f g
  fun fst (x, _) = x
  fun snd (_, y) = y
  val member = ListUtil.member
  infix 1 xor 
  fun a xor b = (a orelse b) andalso not (a andalso b)

  fun nub xs = Set.elems (Set.fromList xs)

  datatype status = KNOWN | UNKNOWN  (* status of each bound variable *)
  
  type context = status Env.env
  val emptyContext = Env.empty
  val empty = Env.empty


  fun addVar status x rho = Env.bind (x, status, rho)
  val _ = addVar : status -> V.name -> context -> context
  
  val makeKnown = addVar KNOWN
  val makeUnknown = addVar UNKNOWN
  fun known context x = Env.binds (context, x) 
                        andalso Env.find (x, context) = KNOWN

  fun makeAllUnkown ns ctx = foldl (fn (n, c) => makeUnknown n c) ctx ns
  fun makeAllKnown ns ctx = foldl (fn (n, c) => makeKnown n c) ctx ns
  
  fun containsDuplicates xs = length xs <> length (nub xs)
  exception DuplicateNames of V.name list
  
  fun introduce x rho = Env.bind (x, NONE, rho)

  fun getDuplicates xs = 
  let val ys = nub xs
  in foldl (fn (x, dups) => if not (member x ys) then x::dups else dups) [] xs
  end 
  fun introduceMany ns rho = 
  let val dups = getDuplicates ns
  in if length dups <> 0
     then raise DuplicateNames dups
     else foldl (fn (n, env) => introduce n env) rho ns
  end

  fun env_of_ctx ctx = Env.map (fn UNKNOWN => NONE 
                                 | KNOWN => SOME (C.VCON (C.K "Dummy", []))) ctx

  (*** Debugging ***)

  fun gexpString ([], rhs) = "([], " ^ V.expString rhs ^ ")"
    | gexpString (gs, rhs) = "(" ^ String.concatWith ";" (map V.guardString gs) ^ " -> " ^ V.expString rhs ^ ")"

  fun choicesString choices = String.concatWith "[]" (map gexpString choices)

  fun println x = print (x ^ "\n")

  fun dumpctx ctx = println ("context: " ^  Env.toString (fn KNOWN => "KNOWN" | _ => "UNKNOWN") ctx)

  (* Compiler helper functions *)

  val rec findOneConstructorApplication : context -> 'a guarded_exp -> V.name option
    = fn ctx => fn (guards, a) => 
    let 
    fun findOneConapp gs = 
       case gs of 
            []      => NONE
          | V.CONDITION e::gs' => findOneConapp gs'
          | V.EQN (n, V.C (C.VCONAPP _))::gs' => if known ctx n then SOME n
                                                        else findOneConapp gs'
          | V.EQN (n, V.C (C.LITERAL (C.VCON _)))::gs' => 
                                                 if known ctx n then SOME n
                                                        else findOneConapp gs'
          | V.EQN _::gs' => findOneConapp gs'
    in findOneConapp guards 
    end 
    (* return a known name that is equal to a VCONAPP *)

  fun findAnyConstructorApplication context [] = NONE
    | findAnyConstructorApplication context (g::gs) =
        case findOneConstructorApplication context g
          of SOME answer => SOME answer
           | NONE => findAnyConstructorApplication context gs
  
  val _ : context -> 'a guarded_exp list -> V.name option
    = findAnyConstructorApplication


  exception NameNotBound of string 

  fun addFromExp (V.C ce) = 
     (case ce of 
          C.LITERAL v => (addFromVal v)
        | C.LAMBDAEXP (n, body) => addFromExp body
        | C.NAME n    => Set.insert (n, Set.empty)
        | C.VCONAPP (vc, es) => Set.union' (map addFromExp es)
        | C.FUNAPP (e1, e2) =>  Set.union' [addFromExp e1, addFromExp e2])
    | addFromExp (V.I (V.IF_FI branches)) = 
      Set.union' (map (addFromBranch o snd) branches)
  and addFromVal (C.LAMBDA (n, _, body)) = addFromExp body
    | addFromVal (C.VCON (vc, vs)) = Set.union' (map addFromVal vs)
  and addFromGuard (V.CONDITION e) = addFromExp e
    | addFromGuard (V.EQN (x, e)) = addFromExp e
  and addFromBranch (gs, rhs) = Set.union' (addFromExp rhs :: map addFromGuard gs)

  fun addConstrainedNames (gs_rhs, xs) = Set.union' (addFromBranch gs_rhs::[xs])
  (* all names used *)
  
  fun dropUnconstrainedNames (vcon, atoms) choices =
    let val constrained =
              foldl (fn (gs_rhs, xs) => addConstrainedNames (gs_rhs, xs)) Set.empty choices
    in  (vcon, List.filter (fn x => Set.member (x, constrained)) atoms)
    end

  fun solvable ctx e = 
    let val (rho : V.value option Env.env) = env_of_ctx ctx
    in V.currently_solvable rho e
    end


  (* observers *can* be nice *)

  fun extracteq (SOME (V.EQN (x, e))) = SOME (x, e)
    | extracteq (SOME _) = Impossible.impossible "misuse of extracteq"
    | extracteq NONE = NONE

  fun extractc (SOME (V.CONDITION e)) = SOME e
    | extractc (SOME _) = Impossible.impossible "misuse of extractc"
    | extractc NONE = NONE

  fun findAnyLHSBinding ctx cs = 
    let val allgs = (List.concat o map fst) cs
    in extracteq (List.find (fn V.EQN (x, e) => 
                  not (known ctx x) andalso solvable ctx e | _ => false) allgs)
    end

  fun findAnyRHSBinding ctx cs = 
    let val allgs = (List.concat o map fst) cs
    in extracteq (List.find (fn V.EQN (x, e) => 
                  known ctx x andalso not (solvable ctx e) | _ => false) allgs)
    end


  fun findAnyConstraint ctx cs = 
    let val allgs = (List.concat o map fst) cs
    in extracteq (List.find (fn V.EQN (x, e) => 
                  known ctx x andalso solvable ctx e | _ => false) allgs)
    end


  fun findAnyCondition ctx cs = 
    let val allgs = (List.concat o map fst) cs
    in extractc (List.find (fn V.CONDITION e => 
                  solvable ctx e | _ => false) allgs)
    end

  fun eqguard (V.CONDITION e1, V.CONDITION e2) = V.eqexp (e1, e2)
    | eqguard (V.EQN (x1, e1), V.EQN (x2, e2)) = x1 = x2 andalso V.eqexp (e1, e2)
    | eqguard _ = false 

  (* take all instances of g out of gs, for success trees *)
  fun prune g gs = 
    mapPartial (fn g' => 
                  if eqguard (g, g')
                  then NONE 
                  else SOME g') gs

  (* remove all choices with g in them, for failure trees *)
  fun pruneall g choices = 
    mapPartial (fn (gs, rhs) => if List.exists (curry eqguard g) gs 
                                then NONE 
                                else SOME (gs, rhs)) choices

  infix 6 --
  fun choices -- g = map (fn (gs, rhs) => (prune g gs, rhs)) choices

  infix 6 ---
  fun choices --- g = pruneall g choices

  fun subst (x, e) choices = 
    let fun dosubst e' = if V.eqexp (e, e') then V.C (C.NAME x) else e'
        val subguard = V.gmap dosubst
    in map (fn (gs, rhs) => (map subguard gs, dosubst rhs)) choices
    end

  infix 6 withsubst
  fun choices withsubst (x, e) = subst (x, e) choices

  exception Can'tUnify of string 

  fun can'tunify x e = 
    let val kind = 
      case e of V.C (C.FUNAPP _) => "function application"  
              | V.C (C.LAMBDAEXP _) => "lambda expression"
              | V.C (C.LITERAL (C.LAMBDA _)) => "lambda expression"
              | V.C (C.LITERAL (C.VCON _)) => 
                       Impossible.impossible "can'tunify called on vcon literal"
              | V.C (C.NAME _) => 
                       Impossible.impossible "can'tunify called on name"
              | V.C (C.VCONAPP _) => 
                       Impossible.impossible "can'tunify called on vconapp"  
              | V.I (V.IF_FI _) => "if-fi"
        val msg1 = "can't unify "
        val s =  V.expString e
        val msg2 = " (" ^ s ^ ") with unbound names"
        val msg = msg1 ^ kind ^ msg2
    in raise Can'tUnify (msg ^ " with known name " ^ x)
    end

  (* find all things x is compared with so we can test x against all
  possibilities *)
  fun allApplicationsEquatedTo x guards = 
  let 
    fun findAllEq gs = 
       case gs of 
            []      => []
          | V.CONDITION e::gs' => findAllEq gs'
          | V.EQN (n, V.C (C.VCONAPP (vc, es)))::gs' => 
              (if n = x then [(vc, length es)] else []) @ findAllEq gs'
          | V.EQN _::gs' => findAllEq gs'
    in findAllEq guards
    end 

  val _ = allApplicationsEquatedTo : V.name -> V.exp V.guard list -> (C.vcon * int) list

  fun givenames (vcon, i) =
    let fun args 0 = []
          | args n = FreshName.freshNameGen () :: args (n - 1)
    in  (vcon, args i)
    end

  fun refineGexp x vconapp gs_rhs = 
    let val (vc' as C.K vname, ns)  = vconapp
        val (gs_, rhs) = gs_rhs
        fun refine gs = 
          case gs of 
                [] => SOME []
              | (g as V.CONDITION e)::gs' => Option.map (curry op :: g) (refine gs')
              (* todo weak- want to refine in condition as well *)
              | (g as V.EQN (n, V.C (C.VCONAPP (vc, es))))::gs' => 
                  if n = x then 
                    if vc' = vc andalso length es = length ns
                    then Option.map (curry op @ (ListPair.map V.EQN (ns, es))) 
                    (* todo only introduce as many as are used. constrainedAt helps here.  *)
                                    (refine gs')
                    else NONE  
                  else 
                      Option.map (curry op :: g) (refine gs')
              | (g as V.EQN _)::gs' => Option.map (curry op :: g) (refine gs')
        in case refine gs_ of NONE => NONE | SOME refined => SOME (refined, rhs)
    end 

  val _ = refineGexp : V.name -> (C.vcon * V.name list) -> (V.exp V.guard list * V.exp) -> (V.exp V.guard list * V.exp) option


  fun noApp x (guards, rhs) = 
    let 
    fun xNotAnApp gs = 
       case gs of 
            [] => true
          | V.CONDITION e::gs' => xNotAnApp gs'
          | V.EQN (n, V.C (C.VCONAPP _))::gs' => x <> n andalso xNotAnApp gs'
          | V.EQN (n, V.C (C.LITERAL (C.VCON _)))::gs' => 
                                                 x <> n andalso xNotAnApp gs'
          | V.EQN _::gs' => xNotAnApp gs'
    in xNotAnApp guards 
    end 
      

  fun translate ctx (V.C ce) = 
      let val tr = translate ctx 
          fun translate_val ctx' (C.LAMBDA (n, _, body)) = 
                                 C.LAMBDA (n, empty, translate (makeKnown n ctx') body)
                    (* translation does not preserve closures, nor should it *)
            | translate_val ctx' (C.VCON (vc, vs)) = 
                                 C.VCON (vc, map (translate_val ctx') vs)
      in  D.C 
    (case ce of 
      C.LITERAL v => (C.LITERAL (translate_val ctx v))
    | C.LAMBDAEXP (n, body) => C.LAMBDAEXP (n, translate (makeKnown n ctx) body)
    | C.NAME n    => (C.NAME n)
    | C.VCONAPP (vc, es) => C.VCONAPP (vc, map tr es)
    | C.FUNAPP (e1, e2) => C.FUNAPP (tr e1, tr e2))
    end 
  
    | translate ctx (V.I (V.IF_FI branches)) = 
    (* Assumes global name uniqueness - todo establish *)
    let val (names, gexps) = ListPair.unzip branches
        val allnames = List.concat names
        val initialcontex = foldl (fn (n, ctx') => addVar UNKNOWN n ctx') 
                            ctx allnames
      in D.I (compile initialcontex gexps)
      end 

(* need rule for removing fail 
   all subtracts are s[fail/thing]
   just go by paper. should be one case per rule. label each. 
   update the README after 
   *)
  and compile context [] = D.FAIL
    | compile context (choices as ([], e) :: _) = 
         D.MATCH (translate context e)  (* unguarded rhs *)
    | compile context choices = 
      (
     
     (* rule 1 *)
     (* ... *)
     (* rule n *)

        (* dumpctx context;  *)
      case findAnyConstructorApplication context choices
        of SOME x =>  
        let val cons = nub $ List.concat $ map (allApplicationsEquatedTo x o fst) choices
            fun refineChoicesWith (app : C.vcon * int) = 
              let val k_ns = givenames app
                  val ns = snd k_ns
                  val choices' = mapPartial (refineGexp x k_ns) choices
              in (k_ns, compile (makeAllKnown ns context) choices')
              end 

            val edges    = map refineChoicesWith cons 
            val defaults = List.filter (noApp x) choices
            val default  = if null defaults 
                           then NONE
                           else SOME (compile context defaults)
        in D.TEST (x, edges, default)
        end 
        | NONE => 
        (case findAnyLHSBinding context choices
          of SOME (x, e) => 
            let val eq =  V.EQN (x, e)
                val c  = (V.CONDITION e)
                val choices_no_eq = choices -- eq withsubst (x, e)
                val choices_no_e = choices --- eq --- c
            in  D.LET_UNLESS (x, translate context e, 
                            compile (makeKnown x context) choices_no_eq, 
                            SOME (compile context choices_no_e))
            end 
        | NONE => 
        (case findAnyRHSBinding context choices
          of SOME (x, y as V.C (C.NAME y')) => 
              D.LET_UNLESS (x, D.C (C.NAME y'), compile (makeKnown y' context) 
                        (choices -- (V.EQN (x, y))), NONE)
          | SOME (x, e) => can'tunify x e
          | NONE => 
        (case findAnyConstraint context choices
          of SOME (x, e) => 
            let val eq = V.EQN (x, e)
                val c  = V.CONDITION e
                val cmp_pruned = choices withsubst (x, e)
                val y = FreshName.freshNameGen () 
              val no_eq_choices_no_c = choices --- eq -- c
                val no_e_choices = choices --- eq --- c
            in 
            (raise Impossible.unimp "inconsistent with paper- being fixed")
            (* D.IF_THEN_ELSE (x, , 
                         compile context cmp_pruned, 
                         compile context no_eq_choices_no_c, 
                         compile context no_e_choices) *)
            end 
          | NONE => 
        (case findAnyCondition context choices
          of SOME e => 
            let val x = FreshName.freshNameGen ()
                val eq =  V.EQN (x, e)
                val c  = V.CONDITION e
                val choices_x_for_e = choices -- c withsubst (x, e)
                val choices_no_e = choices --- eq --- c
            in  D.LET_UNLESS (x, translate context e, 
                            compile (makeKnown x context) choices_x_for_e, 
                            SOME (compile context choices_no_e))
            end 
          | NONE => raise Stuck (choicesString choices))))))
          

  (* compilation continues until there are no known variables equal to constructor applications *)

  val translate : context -> VMinus.exp -> D.exp = 
  fn context => fn e => translate context (DesugaredVMinus.desugar e)
  
  val compile = compile emptyContext

  fun def context (VMinus.DEF (n, e)) = 
    let val newcontext = makeKnown n context
    in (D.DEF (n, translate newcontext e), newcontext)
    end 


  fun defs ds = snd (ListUtil.foldlmap (fn (d, ctx) => def ctx d) emptyContext ds)

end
