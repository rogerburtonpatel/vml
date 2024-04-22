signature VMINUS = sig 
  type name = Core.name
  type vcon = Core.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list

  datatype exp = C of exp Core.t
               | I of (exp, exp) if_fi

  datatype def = DEF of name * exp

  type value = exp Core.value

  exception Fail of string

  val expString : exp -> string 
  val valString : value -> string 
  val defString : def -> string 

  val eqexp : exp * exp -> bool

  val gmap :  ('a -> 'b) -> 'a guard -> 'b guard
  val currently_solvable :   exp Core.value option Env.env -> exp -> bool
  val eval : value option Env.env -> exp -> value

  val runProg : def list -> unit

end 
structure VMinus :> VMINUS
  = struct
  type name = string
  type vcon = Core.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list

  datatype exp = C of exp Core.t
               | I of (exp, exp) if_fi

  datatype def = DEF of name * exp

  type value = exp Core.value

  exception Fail of string


    fun gmap f (EQN (n, e))        = EQN (n, f e)
      | gmap f (CONDITION e)       = CONDITION (f e)
      | gmap f (CHOICE (gs1, gs2)) = CHOICE (map (gmap f) gs1, map (gmap f) gs2)


  fun eqval (e1, e2) = Core.eqval (e1, e2)

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"

  structure C = Core

  fun expString (C ce) = 
  (case ce of C.FUNAPP (e1, e2)  => 
                          maybeparenthesize e1 ^ " " ^ maybeparenthesize e2
            | C.VCONAPP (vc, es) => C.vconAppStr maybeparenthesize vc es
            | _ => C.expString expString ce)
    | expString   (I (IF_FI bindings)) = "if\n" ^ if_fiString bindings ^ "\nfi"
  and guardString (EQN (n, e))         = n ^ " = " ^ expString e
    | guardString (CONDITION e)        = expString e
    | guardString (CHOICE (gs1, gs2))  = 
            let val compress = String.concatWith "; " o map guardString
            in  br' (compress gs1 ^ " | " ^ compress gs2 )
            end 
  and gexpString (ns, (gs, r)) = 
        let val (existential, dot) = if null ns then ("", "") else ("E ", ". ")
            val binds    = existential ^ String.concatWith " " ns ^ dot
            val gStrings = String.concatWith "; " (map guardString gs)
            val rString  = expString r
        in binds ^ gStrings ^ " -> " ^ rString
        end 
  and if_fiString gexps = 
    "    " ^ String.concatWith "\n[]  " (List.map gexpString gexps) 
  and valString v = C.valString expString v
  and maybeparenthesize (C e) = C.maybeparenthesize expString e
    | maybeparenthesize other = br' (expString other)
    

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

  (* XXX TODO this is a bit sus *)
  fun eqexp (e1, e2) = expString e1 = expString e2

  fun optString printer (SOME x) = printer x 
    | optString printer NONE     = "NONE"

  (* environment utils *)

  type lvar_env = value option Env.env

  infix 6 <+>
  val op <+> = Env.<+>

  infix 9 binds
  fun rho binds n = Env.binds (rho, n)

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, SOME v, rho)
  fun introduce x rho = Env.bind (x, NONE, rho)
  fun lookupv x rho = valOf (lookup x rho)
  val empty = Env.empty

  infix 9 exists_in
  fun n exists_in (rho: lvar_env) = 
    rho binds n andalso isSome (lookup n rho)

  infix 9 unknown_in 
  fun n unknown_in (rho: lvar_env) = 
    rho binds n andalso not (isSome (lookup n rho))

  exception Unsolvable of string 


  (* for debugging *)
  fun println s = print (s ^ "\n")
  fun optValString v = optString (C.valString expString) v

  fun nub xs = (Set.elems o Set.fromList) xs
  fun containsDuplicates xs = length xs <> length (nub xs)
  exception DuplicateNames of name list

  val member = ListUtil.member


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

  fun lvarEnvMerge (rho1 : lvar_env) (rho2 : lvar_env) = 
    Env.merge (fn (SOME x, SOME y)   => SOME x
                | (NONE,   SOME x)   => SOME x
                | (SOME x, NONE)     => SOME x
                | (NONE,   NONE)     => NONE) (rho1, rho2)

  fun makeKnown x rho = (bind x (C.VCON (C.K "Dummy", [])) rho)

  fun currently_solvable rho (C ce) = 
    (case ce of 
    C.NAME n => if not (rho binds n)
                then raise C.NameNotBound n 
                else n exists_in rho
  | C.LITERAL v => val_solvable rho v
  | C.VCONAPP (_, es) => List.all (currently_solvable rho) es
  | C.LAMBDAEXP (n, body) => currently_solvable (makeKnown n rho) body
  | C.FUNAPP (e1, e2) =>         currently_solvable rho e1 
                         andalso currently_solvable rho e2)
    | currently_solvable rho (I (IF_FI [])) = true
    | currently_solvable rho (I (IF_FI branches)) =  
        List.all (branch_currently_solvable rho) branches
  and val_solvable rho (C.LAMBDA (n, body)) = 
                                      currently_solvable (makeKnown n rho) body
    | val_solvable rho (C.VCON (vc, vs)) = List.all (val_solvable rho) vs
  and guard_solvable rho g = 
        case g of CONDITION e => currently_solvable rho e  
                | EQN (x, e) => x exists_in rho orelse currently_solvable rho e
                | CHOICE (gs1, gs2) => List.all (guard_solvable rho) gs1 
                                        orelse List.all (guard_solvable rho) gs2
  and tryfindorder rho made_progress [] [] = (rho, [])
    | tryfindorder rho made_progress stuck [] = 
      if made_progress 
      then tryfindorder rho false [] stuck
      else raise Unsolvable "guards cannot be sorted"
    | tryfindorder rho made_progress stuck (g::gs) = 
      (case g of EQN (x, _) => 
        if guard_solvable rho g 
        then tryfindorder (makeKnown x rho) true stuck gs
        else tryfindorder rho made_progress (g::stuck) gs  
       | CONDITION e => 
        if guard_solvable rho g 
        then tryfindorder rho true stuck gs
        else tryfindorder rho made_progress (g::stuck) gs  
      | CHOICE (gs1, gs2) => 
          (let val (rho1, _) = tryfindorder rho made_progress [] gs1 
          in tryfindorder (Env.<+> (rho, rho1)) true stuck gs
          end
            handle Unsolvable _ => 
            let val (rho2, _) = tryfindorder rho made_progress [] gs1
            in tryfindorder (Env.<+> (rho, rho2)) true stuck gs
            end 
              handle Unsolvable _ => 
                tryfindorder rho made_progress (g::stuck) gs))
  and branch_currently_solvable rho branch = 
      let val (ns, (gs, rhs)) = branch
          val doguards = tryfindorder (introduceMany ns rho) false []
          val guards_solvable = ((ignore (doguards gs) ; true)
                                  handle Unsolvable _ => false)
      in guards_solvable andalso currently_solvable rho rhs
      end 


(* unify binds a value to an expression that may contain unknown names, or
   fails. *)
  fun unify rho ((v as C.VCON (C.K vc, vs)), (C ce))  = 
      let fun fail () = 
          raise Fail ( "failed attempting to unify incompatible values " 
                            ^ valString v ^ " and " ^ expString (C ce)) 
      in 
      (case ce of 
        C.LITERAL v' =>  
          if not (eqval (v, v')) 
          then raise Fail ( "failed attempting to unify incompatible values " 
                            ^ valString v ^ " and " ^ expString (C ce)) 
          else empty
      | C.NAME n     => 
        if n exists_in rho 
        then if not (eqval (lookupv n rho, v)) 
             then raise Fail ( "failed attempting to unify incompatible values " 
                            ^ valString v ^ " and " ^ expString (C ce)) 
             else empty
        else bind n v empty
      | C.VCONAPP (C.K vc', es) => 
          if vc <> vc' orelse length es <> length vs 
          then raise Fail ( "failed attempting tjo unify incompatible values " 
                            ^ valString v ^ " and " ^ expString (C ce)) 
          else unifyMany rho es vs
      | e as C.LAMBDAEXP _  => 
          raise Unsolvable ("can't unify any value (" 
                               ^ valString v ^ ") with a lambda (" 
                               ^ Core.expString expString e ^ ")")
      | e as C.FUNAPP    _  => 
          raise Unsolvable ("can't unify any value (" 
                              ^ valString v ^ ") with a function application (" 
                              ^ Core.expString expString e ^ ") that has " 
                              ^ "unbound names"))
      end 
        | unify rho (v, (if_fi as I _))        = 
       raise Unsolvable ("can't unify any value (" 
                              ^ valString v ^ ") with an if-fi (" 
                              ^ expString if_fi ^ ") that has " 
                              ^ "unbound names")
        | unify rho ((v as C.LAMBDA _), e) =           
            raise Unsolvable ("can't unify any value (" 
                               ^ valString v ^ ") with a lambda (" 
                               ^ expString e ^ ")")
  and unifyMany rho es vs = 
    foldr (fn ((ex, vl), rho') => 
                        let val rho'' = unify rho' (vl, ex) 
                        in (lvarEnvMerge rho'' rho') 
                        end)
                  rho (ListPair.zip (es, vs))


  fun find_or_die n rho = 
        if n exists_in rho then lookupv n rho else raise C.NameNotBound n

  fun findSplit f xs = 
    let fun findSplit' acc [] = NONE 
          | findSplit' acc (y::ys) =  if f y
                                      then SOME (y, acc @ ys)
                                      else findSplit' (y::acc) ys
  in findSplit' [] xs
  end 

  fun eval rho (C ce) = 
    (case ce of
      C.LITERAL v => v
    | C.NAME n    => find_or_die n rho
    | C.VCONAPP (vc, es)    => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, body)
    | C.FUNAPP (C (C.NAME "print"), param)  => 
    (* dirty trick to print values *)
                    ( println (C.valString expString (eval rho param)) 
                          ; C.VCON (C.K "unit", [])
                    ) 
    | C.FUNAPP (fe, param)  => 
              (case eval rho fe 
                of C.LAMBDA (n, b) => 
                  let val arg  = eval rho param
                      val rho' = bind n arg rho
                    in 
                     eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
    | eval rho (I (IF_FI ((ns, (gs, rhs))::branches))) = 
        ( let val rho'  = introduceMany ns rho
            val rho'' = solve rho' gs  (* may raise Fail *)
          in eval rho'' rhs
          end 
            handle Fail _ => eval rho (I (IF_FI branches))
        )
    | eval rho (I (IF_FI [])) = raise Fail "ran out of options in if-fi"

  and solve rho [] = rho
    | solve (rho : lvar_env) (guards as (_::gs)) = 
        let 

  (* making nondeterminism of picking an equation deterministic *)
  fun pickAnEquation gs = case findSplit (guard_solvable rho) gs of SOME r => r
  | NONE => raise Unsolvable ("cannot make progress on guards (" 
                               ^ String.concatWith ";" (map guardString gs)
                               ^ ") because the program could not pick a "
                               ^ "solvable guard from among them.")
        
        val (g, gs) = pickAnEquation guards

        in (case g 
            of CONDITION e =>
                (ignore (eval rho e) ; 
                  solve rho gs)
          | EQN (x, e) => 
              let val rho' = 
                    case (x exists_in rho, currently_solvable rho e)
                      of (true, _) => 
                          unify rho (lookupv x rho, e)
                      | (false, true) => 
                          bind x (eval rho e) rho
                      | (false, false) => Impossible.impossible "no progress"
              in solve rho' gs
              end 
          | CHOICE (gs1, gs2) => 
              let val rho' = 
                      (solve rho gs1 handle Fail _ => solve rho gs2)
              in solve rho' gs
              end)
          end 

  fun def rho (DEF (n, e)) = 
    let val v = eval rho e
    in bind n v rho
    end

  fun runProg defs = 
  (  foldl (fn (d, env) => 
      let val rho = def env d
      in  rho <+> env
      end) empty defs;
      ()
  )


end

structure DesugaredVMinus :> sig
  type name = Core.name
  type vcon = Core.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list

  datatype exp = C of exp Core.t
               | I of (exp, exp) if_fi

  datatype def = DEF of name * exp
  type value = exp Core.value

  val desugar : VMinus.exp -> exp

  val expString : exp -> string 
  val guardString : exp guard -> string 
  val valString : value -> string 
  val defString : def -> string 

  val eqexp : exp * exp -> bool

  val def : VMinus.def -> def
  val gmap :  ('a -> 'b) -> 'a guard -> 'b guard

  val currently_solvable :   exp Core.value option Env.env -> exp -> bool

  (* 


  
  val eval : value option Env.env -> exp -> value

  val runProg : def list -> unit *)

  (* val def : VMinus.def -> D.def
  type 'a guarded_exp' = VMinus.name list * (VMinus.exp VMinus.guard list * 'a)
  exception Stuck of unit guarded_exp' list
  val compile : VMinus.exp guarded_exp' list -> (D.exp, D.exp) D.tree
  val translate : VMinus.exp -> D.exp  *)
end
  =
struct
  type name = Core.name
  type vcon = Core.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list
  datatype exp = C of exp Core.t
               | I of (exp, exp) if_fi

  datatype def = DEF of name * exp

  type value = exp Core.value

  structure V = VMinus
  structure C = Core
  fun curry f x y = f (x, y)

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"


  fun expString (C ce) = 
  (case ce of C.FUNAPP (e1, e2)  => 
                          maybeparenthesize e1 ^ " " ^ maybeparenthesize e2
            | C.VCONAPP (vc, es) => C.vconAppStr maybeparenthesize vc es
            | _ => C.expString expString ce)
    | expString   (I (IF_FI bindings)) = "if\n" ^ if_fiString bindings ^ "\nfi"
  and guardString (EQN (n, e))         = n ^ " = " ^ expString e
    | guardString (CONDITION e)        = expString e
  and gexpString (ns, (gs, r)) = 
        let val (existential, dot) = if null ns then ("", "") else ("E ", ". ")
            val binds    = existential ^ String.concatWith " " ns ^ dot
            val gStrings = String.concatWith "; " (map guardString gs)
            val rString  = expString r
        in binds ^ gStrings ^ " -> " ^ rString
        end 
  and if_fiString gexps = 
    "    " ^ String.concatWith "\n[]  " (List.map gexpString gexps) 
  and valString v = C.valString expString v
  and maybeparenthesize (C e) = C.maybeparenthesize expString e
    | maybeparenthesize other = br' (expString other)
    

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

  fun eqexp (e1, e2) = expString e1 = expString e2
    


    fun gmap f (EQN (n, e))        = EQN (n, f e)
      | gmap f (CONDITION e)       = CONDITION (f e)

  type lvar_env = value option Env.env

  infix 6 <+>
  val op <+> = Env.<+>

  infix 9 binds
  fun rho binds n = Env.binds (rho, n)

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, SOME v, rho)
  fun introduce x rho = Env.bind (x, NONE, rho)
  fun lookupv x rho = valOf (lookup x rho)
  val empty = Env.empty

  infix 9 exists_in
  fun n exists_in (rho: lvar_env) = 
    rho binds n andalso isSome (lookup n rho)

  infix 9 unknown_in 
  fun n unknown_in (rho: lvar_env) = 
    rho binds n andalso not (isSome (lookup n rho))

  exception Unsolvable of string 

  fun nub xs = (Set.elems o Set.fromList) xs
  fun containsDuplicates xs = length xs <> length (nub xs)
  exception DuplicateNames of name list

  val member = ListUtil.member


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

  fun makeKnown x rho = (bind x (C.VCON (C.K "Dummy", [])) rho)


  fun currently_solvable rho (C ce) = 
    (case ce of 
    C.NAME n => if not (rho binds n)
                then raise C.NameNotBound n 
                else n exists_in rho
  | C.LITERAL v => val_solvable rho v
  | C.VCONAPP (_, es) => List.all (currently_solvable rho) es
  | C.LAMBDAEXP (n, body) => currently_solvable (makeKnown n rho) body
  | C.FUNAPP (e1, e2) =>         currently_solvable rho e1 
                         andalso currently_solvable rho e2)
    | currently_solvable rho (I (IF_FI [])) = true
    | currently_solvable rho (I (IF_FI branches)) =  
        List.all (branch_currently_solvable rho) branches
  and val_solvable rho (C.LAMBDA (n, body)) = 
                                      currently_solvable (makeKnown n rho) body
    | val_solvable rho (C.VCON (vc, vs)) = List.all (val_solvable rho) vs
  and guard_solvable rho g = 
        case g of CONDITION e => currently_solvable rho e  
                | EQN (x, e) => x exists_in rho orelse currently_solvable rho e
  and tryfindorder rho made_progress [] [] = (rho, [])
    | tryfindorder rho made_progress stuck [] = 
      if made_progress 
      then tryfindorder rho false [] stuck
      else raise Unsolvable "guards cannot be sorted"
    | tryfindorder rho made_progress stuck (g::gs) = 
      (case g of EQN (x, _) => 
        if guard_solvable rho g 
        then tryfindorder (makeKnown x rho) true stuck gs
        else tryfindorder rho made_progress (g::stuck) gs  
       | CONDITION e => 
        if guard_solvable rho g 
        then tryfindorder rho true stuck gs
        else tryfindorder rho made_progress (g::stuck) gs)
  and branch_currently_solvable rho branch = 
      let val (ns, (gs, rhs)) = branch
          val doguards = tryfindorder (introduceMany ns rho) false []
          val guards_solvable = ((ignore (doguards gs) ; true)
                                  handle Unsolvable _ => false)
      in guards_solvable andalso currently_solvable rho rhs
      end 

  fun desugar (V.C ce) = 
      (case ce of C.LITERAL v => 
        let fun desugarv (C.VCON (vc, vs)) = C.VCON (vc, map desugarv vs)
              | desugarv (C.LAMBDA (n, body)) = C.LAMBDA (n, desugar body)
        in C (C.LITERAL (desugarv v))
        end 
        | C.NAME n => C (C.NAME n)
        | C.VCONAPP (vc, es) => C (C.VCONAPP (vc, map desugar es))
        | C.LAMBDAEXP (n, body) => C (C.LAMBDAEXP (n, desugar body))
        | C.FUNAPP (e1, e2) => C (C.FUNAPP (desugar e1, desugar e2)))
    | desugar (V.I (V.IF_FI branches)) = 
      let fun combine g ns_gs_rhss = 
        let val (ns, gs_rhss) = ListPair.unzip ns_gs_rhss
            val (gs, rhss) = ListPair.unzip gs_rhss
        in ListPair.zip (ns, ListPair.zip (map (curry op :: g) gs, rhss))
        end 
          fun desugarGexp (ns, ([], rhs)) = [(ns, ([], desugar rhs))]
            | desugarGexp (ns, (g::gs, rhs)) = 
              (case g of V.CONDITION e => 
                         combine (CONDITION (desugar e)) 
                                 (desugarGexp (ns, (gs, rhs)))
                       | V.EQN (x, e)  => 
                            combine (EQN (x, desugar e)) 
                                    (desugarGexp (ns, (gs, rhs)))
                       | V.CHOICE (gs1, gs2) => 
                          desugarGexp (ns, (gs1 @ gs, rhs)) @
                          desugarGexp (ns, (gs2 @ gs, rhs)))
          val newBranches = (List.concat o map desugarGexp) branches
          in I (IF_FI newBranches)
          end 

  fun def (V.DEF (n, e)) = DEF (n, desugar e)
end