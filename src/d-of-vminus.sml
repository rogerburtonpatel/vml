structure DofVminus :> sig
  val def : VMinus.def -> D.def
  type 'a guarded_exp' = VMinus.name list * (VMinus.exp VMinus.guard list * 'a)
  exception Stuck of unit guarded_exp' list
  val compile : VMinus.exp guarded_exp' list -> (D.exp, D.exp) D.tree
  val translate : VMinus.exp -> D.exp 
end
  =
struct

  structure V = VMinus
  structure D = D
  structure C = Core

  type 'a guarded_exp' = V.name list * (V.exp V.guard list * 'a)

  exception Stuck of unit guarded_exp' list

  fun unitify (ns, (gs, a)) = (ns, (gs, ()))
  val member = ListUtil.member
  val mapPartial = List.mapPartial


  datatype status = KNOWN | UNKNOWN  (* status of each bound variable *)
  
  type context = status Env.env

  val emptyContext = Env.empty

  fun addVar status x rho = Env.bind (x, status, rho)
  val _ = addVar : status -> V.name -> context -> context
  
  val makeKnown = addVar KNOWN
  val makeUnknown = addVar UNKNOWN
  fun known context x = Env.binds (context, x) 
                        andalso Env.find (x, context) = KNOWN

  fun makeAllUnkown ns ctx = foldl (fn (n, c) => makeUnknown n c) ctx ns


(* to generate a decision-tree TEST node, we require an EQN that has a
   known name on the left and a constrcutor application on the right 

   to generate an IF node, an EQN with both sides known, or an EXPSEQ with a known exp
*)


(* Not used, so far- replaced by addEquality/addInequality *)
  (* val matchName :
      V.name -> (Core.vcon * V.exp list) -> 'a guarded_exp' -> 'a guarded_exp' option
    = fn _ => Impossible.unimp "not yet" *)
  (*
     matchName (x = y :: ys) [[x = z :: zs --> e]] = SOME [[y = z, ys = zs --> e]]
     matchName (x = y :: ys) [[x = nil --> e]] = NONE
   *)    

  val rec findOneConstructorApplication : context -> 'a guarded_exp' -> V.name option
    = fn ctx => fn (names, (guards, a)) => 
    let 
    val ctx' = foldl (fn (n, base) => addVar UNKNOWN n base) ctx names
    fun findOneConapp gs = 
       case gs of 
            []      => NONE
          | V.CONDITION e::gs' => findOneConapp gs'
          | V.EQN (n, V.C (C.VCONAPP _))::gs' => if known ctx' n then SOME n
                                                        else findOneConapp gs'
          | V.EQN _::gs' => findOneConapp gs'
          | V.CHOICE (g1, g2)::gs' => Impossible.unimp "todo - choice"
    in findOneConapp guards 
    end 
    (* return a known name that is equal to a VCONAPP *)

  fun findAnyConstructorApplication context [] = NONE
    | findAnyConstructorApplication context (g::gs) =
        case findOneConstructorApplication context g
          of SOME answer => SOME answer
           | NONE => findAnyConstructorApplication context gs
  
  val _ : context -> 'a guarded_exp' list -> V.name option
    = findAnyConstructorApplication


  exception NameNotBound of string 

(************* BEGIN FAILED ATTEMPTS AT findAnyKnownRHS *************)




(* an expression e is known in context ctx if all names in e are KNOWN in ctx.
  fun expKnown (ctx : context) (V.C ce) = 
    (case ce of 
      C.LITERAL v => true 
    | C.NAME n => known ctx n
    | C.VCONAPP (vc, es) => List.all (expKnown ctx) es
    | C.LAMBDAEXP (n, body) => expKnown (addVar KNOWN n ctx) body 
    | C.FUNAPP (e1, e2) => expKnown ctx e1 andalso expKnown ctx e2)
    | expKnown ctx (V.I (V.IF_FI branches)) = 
      let fun doGuard ctx' g = 
        case g of 
          V.CONDITION e => expKnown ctx' e  
        | V.EQN (n, e) => _
        | V.CHOICE _ => _


      
      fun doBranch (ns, (gs, a)) = 
        let val ctx' = makeAllUnkown ns ctx 
        in Impossible.unimp "todo"
        end 
      in Impossible.unimp "todo"
      end 

(* stuck says: can I solve this with the information I have now? 
i.e. do I have all the names I need to evaluate this expression? *)
(* val rec stuck : context -> V.exp -> bool = 
  fn ctx => fn ex => 
    let fun unknown n = if not (Env.binds (ctx, n)) then raise NameNotBound n 
                        else (Env.find (n, ctx)) = UNKNOWN
        fun has_unbound_names (V.C ce) = 
          (case ce of C.LITERAL _ => false 
           | C.NAME name => unknown name 
           | C.VCONAPP (v, es) => List.exists has_unbound_names es
           | C.FUNAPP (e1, e2) => has_unbound_names e1 orelse has_unbound_names e2 
           | C.LAMBDAEXP (n, body) => 
                  stuck (makeKnown n ctx) body)
           | has_unbound_names (V.I (V.IF_FI branches)) = 
              let fun multiStuck (Multi.MULTI es) = List.exists has_unbound_names es
                  fun guardStuck g = 
                     case g of V.CONDITION e' => has_unbound_names e' 
                  | V.EQN (n, e') => unknown n 
                                       orelse has_unbound_names e'
                  | V.CHOICE (gs1, gs2) => Impossible.unimp "todo s"
                  fun branchStuck (ns, ([], a)) = multiStuck a
                    | branchStuck (ns, (g::gs), a) = 
                  
              
                  val ctx' = makeAllUnkown names ctx 
                  val (gs, rhss)     = ListPair.unzip gexps
              in 
           List.exists (has_unbound_gexp ctx) gs 
           end 
        and has_unbound_gexp ctx g = Impossible.unimp "todo"
          (* case g of V.CONDITION e' => has_unbound_names e' 
                  | V.EQN (n, e') => unknown n 
                                       orelse has_unbound_names e'
                  | V.CHOICE (gs1, gs2) => Impossible.unimp "todo s" *)
    in has_unbound_names ex 
  end  *)
  

  val rec findOneKnownRHS : context -> 'a guarded_exp' -> V.name option
    = fn ctx => fn (names, (guards, a)) => 
    let 
    val ctx' = makeAllUnkown names ctx
    fun findOneRHS gs = 
       case gs of 
            []      => NONE
          | V.CONDITION e::gs' => findOneRHS gs'
          | V.EQN (n, e)::gs' => if known ctx' n then SOME n
                                                        else findOneConapp gs'
          | V.EQN _::gs' => findOneConapp gs'
          | V.CHOICE (g1, g2)::gs' => Impossible.unimp "todo - choice"
    in findOneConapp guards 
    end  *)
    (* return a known name that is equal to a VCONAPP *)

(************* END FAILED ATTEMPTS AT findAnyKnownRHS *************)

  fun findOneKnownRHS ctx g = Impossible.unimp "todo"

  fun findAnyKnownRHS context [] = NONE
    | findAnyKnownRHS context (g::gs) =
        case findOneKnownRHS context g
          of SOME answer => SOME answer
           | NONE => findAnyKnownRHS context gs

  val _  : context -> 'a guarded_exp' list -> (V.name * V.exp) option
    = findAnyKnownRHS

  fun eqEqns (n1, e1) (n2, e2) = n1 = n2 andalso V.eqexp (e1, e2)

  val addEquality   : (V.name * V.exp) -> 'a guarded_exp' -> 'a guarded_exp' option
    = fn (n, e) => 
      let exception BadEquality
      val check = List.filter 
        (fn g => case g of V.EQN eqn => 
                    if eqEqns (n, e) eqn
                    then false
                    else raise BadEquality  
                  | _ => true)
    in fn (ns, (gs, a)) =>
      SOME (ns, (check gs, a))
      handle
        BadEquality => NONE
    end   
    
(* example of where you want side conditions *)

  val addInequality : (V.name * V.exp) -> 'a guarded_exp' -> 'a guarded_exp' option
    = fn (n, e) => 
      let exception BadInequality
      val check = List.filter 
        (fn g => case g of V.EQN eqn => 
                    if not (eqEqns (n, e) eqn)
                    then false   
                    else raise BadInequality
                  | _ => true)
    in fn (ns, (gs, a)) =>
      SOME (ns, (check gs, a))
      handle
        BadInequality => NONE
    end   

  (*  *)
  val ifEq : (V.name * D.exp) -> ('e, 'a) D.tree -> ('e, 'a) D.tree -> ('e, 'a) D.tree
    = fn (n, e) => fn tbranch => fn fbranch => 
    let val c = FreshName.freshNameGen ()
    in 
      D.LET (c, (Impossible.unimp "n = e"), D.IF (c, tbranch, fbranch))
    end 

  val nameExp : V.exp -> V.name -> 'a guarded_exp' -> 'a guarded_exp'   
    (* nameExp (x, e) replaces all occurrences of e with x *)
    = fn e => fn n => fn (ns, (gs, a)) =>
    let fun swapIfEq e1 e2 = if V.eqexp (e1, e2) then (V.C (C.NAME n)) else e2
        fun replace gs = List.map 
          (fn V.CONDITION e' => V.CONDITION (swapIfEq e e')
            | V.EQN (n', e') => V.EQN (n', swapIfEq e e')
            | V.CHOICE (gs1, gs2) => V.CHOICE (replace gs1, replace gs2)) gs
        in (ns, (replace gs, a))
        end 
(* question: swap a as well? *)

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

       No guards  ==  MATCH
       CONDITION  ==   if known, convert to LET, IF
       EQN (x, e) ==
          - if x is known and e is VCONAPP, generate TEST
          - if x is known and e is not VCONAPP and e is known
               generate LET, IF
          - if x is unknown and e is known, then generate LET
          
    What if we don't find any of the above? 
    There must be only unknown guards. 
    Can't compile! 
  *)


  (* To generate TEST: 
     - find all instances of x bound to a VCONAPP 
     - the 'test' is here: which one of these is x, actually, at runtime?
     what's below the test:   *)

  (* don't love the case where x = e, and e is both VCONAPP and known *)



(* todo: translate must also propegate a context *)
  fun translate (V.C ce) = D.C (Core.map translate ce)
    | translate (V.I (V.IF_FI branches)) = 


(* problem: how to introduce names only into the right part? *)
    let val (names, gexps) = ListPair.unzip branches
        (* val initialcontex = foldl (fn (n, ctx) => addVar UNKNOWN n ctx) emptyContext names *)
      in D.I (compile emptyContext branches)
      end 

  and compile context [] = Impossible.impossible "no choices"
    | compile context (choices as ((_, ([], e)) :: _)) =
         D.MATCH (translate e)  (* unguarded ARROW *)
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
                  ifEq (x, translate rhs) (compile context (* is x added to this context?  *)
                                         (mapPartial (addEquality   (x, rhs)) choices))
                                (compile context
                                         (mapPartial (addInequality (x, rhs)) choices))
                else
                  D.LET (x, translate rhs,
                         compile (addVar KNOWN x context)
                                 (map (nameExp rhs x) choices))
            | NONE =>
                raise Stuck (map unitify choices)))


  (*  *)
  (* fun findAllVconBindingsOf x gss =  *)

  (* this will be nubbed *)

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
          | V.CHOICE (g1, g2)::gs' => Impossible.unimp "todo - choice"
    in findAllEq guards
    end 

  val _ = allApplicationsEquatedTo : V.name -> V.exp V.guard list -> (C.vcon * int) list

  fun curry f x y = f (x, y)

  fun refineGuardedExp x vconapp gs_rhs = 
    let val (vc', ns)  = vconapp
        val (gs', rhs) = gs_rhs
        fun refine gs = 
       case gs of 
            []      => SOME []
          | V.CONDITION e::gs' => refine gs'
          (* weak- want to refine in condition as well *)
          | V.EQN (n, V.C (C.VCONAPP (vc, es)))::gs' => 
              if n = x then 
                if vc' = vc andalso length es = length ns
                then Option.map (curry op @ (ListPair.map V.EQN (ns, es))) 
                                (refine gs')
                else NONE  
              else refine gs'
          | V.EQN _::gs' => refine gs'
          | V.CHOICE (g1, g2)::gs' => Impossible.unimp "todo - choice"
        in NONE 
    end 

  val _ = refineGuardedExp : V.name -> (C.vcon * V.name list) -> (V.exp V.guard list * V.exp) -> (V.exp V.guard list * V.exp) option
    (* rge x app g  = SOME g', where app is substituted for x everywhere, or NONE if the the compiler can determine that a guard cannot succeed *)
    (* rge x [[(z :: zs)]] [[(x = y :: ys -> command)]] == [[(z = y, zs = ys -> command)]] *)

    (* rge x [[K y1 y2]]  [[gs, x = K e1 e2, gs' -> e]] == SOME [[gs, y1 = e2, y2 = e2, gs' -> e]] *)
    (* rge x [[K y1 ... yn]]  [[gs, x = K e1 ... en, gs' -> e]] == SOME [[gs, y1 = e1, ..., yn = en, gs' -> e]] *)
    (* rge x [[K y1 ... yn]] [[gs, x = K' e1 ... em, gs' -> e]] == NONE, where K != K' *)
    (* rge x [[K y1 ... yn]] [[gs, x = K e1 ... em, gs' -> e]] == NONE, where n != m *)

    (* this has to happen until there are no free occurrences of x *)


    (* compilation continues until there are no known variables equal to constructor applications *)

    (* fun sanityCheckTree gss = findAnyConstructorApplication gss = NONE *)

  val compile = fn things => compile emptyContext things

  fun def (V.DEF (n, e)) = D.DEF (n, translate e)

end


