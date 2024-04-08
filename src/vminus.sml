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
            | _ => Core.expString expString ce)
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
  and maybeparenthesize (C e) = 
(case e of C.LITERAL v => br' (C.valString expString v)
        | C.NAME n     => n
        | C.VCONAPP (C.K vc, es) => 
            if null es then vc else br' (C.vconAppStr expString (C.K vc) es)
        | C.LAMBDAEXP (n, body)  => 
          br' (StringEscapes.backslash ^ n ^ ". " ^ (expString body))
        | C.FUNAPP (e1, e2)      => br' (expString e1 ^ " " ^ expString e2))
  | maybeparenthesize other = br' (expString other)
    

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

fun eqexp (C cex1, C cex2) = Core.expString expString cex1 = Core.expString expString cex2
  | eqexp (I i1, I i2) = Impossible.unimp "compare 2 if-fis"
  | eqexp _ = false 

  fun optString printer (SOME x) = printer x 
    | optString printer NONE     = "NONE"

  infix 9 binds
  fun rho binds n = Env.binds (rho, n)

  exception NameNotBound of string 

  type lvar_env = value option Env.env

  infix 9 exists_in

  fun n exists_in (rho: lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))

  fun checkBound e rho_ = 
        case e of C (C.NAME n) => if not (rho_ binds n)
                                  then raise NameNotBound n
                                  else ()
                              |  _ =>  ()

  fun println s = print (s ^ "\n")


  fun lookup x rho = Env.find (x, rho)

  fun lookupv x rho = valOf (lookup x rho)

  (* making nondeterminism deterministic *)
  fun pickAnEquation (g::gs) = (g, gs)
    | pickAnEquation []      = Impossible.impossible "picking from no equations" 

  exception Unsolvable

  infix 6 <+>

  val op <+> = Env.<+>

  fun optValString v = optString (C.valString expString) v

  fun nub xs = (Set.elems o Set.fromList) xs

  fun containsDuplicates xs = length xs <> length (nub xs)

  exception DuplicateNames

  fun addAsNONETo ns rho = 
  if containsDuplicates ns 
  then raise DuplicateNames
  else foldl (fn (n, env) => Env.bind (n, NONE, env)) rho ns

  fun lvarEnvMerge (rho1 : lvar_env) (rho2 : lvar_env) = 
    Env.merge (fn (SOME x, SOME y)   => SOME x
                | (NONE,   SOME x)   => SOME x
                | (SOME x, NONE)     => SOME x
                | (NONE,   NONE)     => NONE) (rho1, rho2)

(* bindwith binds a value to an expression with unknown names, or fails. *)

  fun bindwith rho ((v as C.VCON (C.K vc, vs)), (C ce))  = 
      (case ce of 
    C.LITERAL v' => if v <> v' then raise Unsolvable else Env.empty
  | C.NAME n => 
    if n exists_in rho 
    then if not (eqval (lookupv n rho, v)) then raise Unsolvable else Env.empty 
    else Env.bind (n, SOME v, Env.empty)
  | C.VCONAPP (C.K vc', es) => 
      if vc <> vc' orelse length es <> length vs 
      then raise Unsolvable 
      else foldr (fn ((ex, vl), rho') => 
                  let 
                  val rho'' = bindwith rho' (vl, ex) 
                  in (lvarEnvMerge rho'' rho') 
                  end)
            rho (ListPair.zip (es, vs))
  | C.LAMBDAEXP _  => raise Unsolvable
  | C.FUNAPP    _  => raise Unsolvable)
    | bindwith rho (_, (I _))        = raise Unsolvable
    | bindwith rho ((C.LAMBDA _), _) = raise Unsolvable


  fun eval rho (C ce) = 
    (case ce of
      C.LITERAL v => v
    | C.NAME n    => 
        if n exists_in rho then lookupv n rho else raise Core.NameNotBound n
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
                      val rho' = Env.bind (n, SOME arg, rho)
                    in 
                     eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
    | eval rho (I (IF_FI ((ns, (gs, rhs))::branches))) = 
    (let val rho'  = addAsNONETo ns rho
         val rho'' = solve rho' [] false gs  (* may raise Unsolvable *)
      in eval rho'' rhs
      end 
        handle Unsolvable => eval rho (I (IF_FI branches)))
    | eval rho (I (IF_FI [])) = raise Core.NoMatch

  and solve rho [] made_progress [] = rho
    | solve rho gs made_progress [] = 
        if made_progress then solve rho [] false gs else raise Unsolvable
    | solve (rho : lvar_env) stuck made_progress guards = 
        let val (g, gs) = pickAnEquation guards
            fun currently_solvable e = (
            (eval rho e ; true)
              handle _ => false)
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
          | EQN (x, e) => let val (rho', stuck', made_progress') = 
                    case (x exists_in rho, currently_solvable e)
                      of (true, true) => 
                        if not (eqval (lookupv x rho, eval rho e)) 
                        then raise Unsolvable 
                        else (rho, stuck, true)
                      | (true, false) => 
                          (bindwith rho ((lookupv x rho), e), stuck, true)
                      | (false, true) => 
                          (Env.bind (x, (SOME (eval rho e)), rho), stuck, true)
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
    in Env.bind (n, SOME v, rho)
    end

  fun runProg defs = 
  (  foldl (fn (d, env) => 
      let val rho = def env d
      in  rho <+> env
      end) Env.empty defs;
      ())


end
