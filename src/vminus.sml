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

  val expString : exp -> string 
  val valString : value -> string 
  val defString : def -> string 

  val eqexp : exp * exp -> bool

  val gmap :  ('a -> 'b) -> 'a guard -> 'b guard
  
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


  (* making nondeterminism of picking an equation deterministic *)
  fun pickAnEquation (g::gs) = (g, gs)
    | pickAnEquation []      = Impossible.impossible "picking from no equations" 

  exception Unsolvable


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

(* bindwith binds a value to an expression that may contain unknown names, 
   or fails. 
   Another name for this function could be 'unify.' *)
  fun bindwith rho ((v as C.VCON (C.K vc, vs)), (C ce))  = 
      (case ce of 
        C.LITERAL v' =>             if v <> v' then raise Unsolvable else empty
      | C.NAME n     => 
        if n exists_in rho 
        then if not (eqval (lookupv n rho, v)) then raise Unsolvable else empty 
        else bind n v empty
      | C.VCONAPP (C.K vc', es) => 
          if vc <> vc' orelse length es <> length vs 
          then raise Unsolvable 
          else bindwithMany rho es vs
      | C.LAMBDAEXP _  => raise Unsolvable
      | C.FUNAPP    _  => raise Unsolvable)
        | bindwith rho (_, (I _))        = raise Unsolvable
        | bindwith rho ((C.LAMBDA _), _) = raise Unsolvable

  and bindwithMany rho es vs = 
    foldr (fn ((ex, vl), rho') => 
                        let val rho'' = bindwith rho' (vl, ex) 
                        in (lvarEnvMerge rho'' rho') 
                        end)
                  rho (ListPair.zip (es, vs))


  fun find_or_die n rho = 
        if n exists_in rho then lookupv n rho else raise C.NameNotBound n

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
            val rho'' = solve rho' [] false gs  (* may raise Unsolvable *)
          in eval rho'' rhs
          end 
            handle Unsolvable => eval rho (I (IF_FI branches))
        )
    | eval rho (I (IF_FI [])) = raise Core.NoMatch

  and solve rho [] made_progress [] = rho
    | solve rho gs made_progress [] = 
        if made_progress then solve rho [] false gs else raise Unsolvable
    | solve (rho : lvar_env) stuck made_progress guards = 
        let val (g, gs) = pickAnEquation guards
            fun currently_solvable e = (
            (eval rho e ; true)
              handle Unsolvable       => false
                   | C.NoMatch        => false
                   | C.NameNotBound _ => false)
        in (case g 
            of CONDITION e =>
                let val (stuck', made_progress') = 
                    if currently_solvable e
                    then  if eval rho e = Core.VCON (Core.K "false", []) 
                          then raise Unsolvable 
                          else (stuck, true) 
                    else (g::stuck, made_progress)
                  in solve rho stuck' made_progress' gs
                  end  
          | EQN (x, e) => 
              let val (rho', stuck', made_progress') = 
                    case (x exists_in rho, currently_solvable e)
                      of (true, true) => 
                        if not (eqval (lookupv x rho, eval rho e)) 
                        then raise Unsolvable 
                        else (rho, stuck, true)
                      | (true, false) => 
                          (bindwith rho (lookupv x rho, e), stuck, true)
                      | (false, true) => 
                          (bind x (eval rho e) rho, stuck, true)
                      | (false, false) => 
                          (rho, g::stuck, made_progress)
              in solve rho' stuck' made_progress' gs
              end 
          | CHOICE (gs1, gs2) => 
              let val (rho', stuck', made_progress') = 
                      ((solve rho stuck made_progress gs1, stuck, true)
                        handle Unsolvable => 
                      ((solve rho stuck made_progress gs2, stuck, true)
                        handle Unsolvable => 
                      (rho, g::stuck, made_progress)))
              in solve rho' stuck' made_progress' gs
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
