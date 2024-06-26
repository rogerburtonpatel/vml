structure VMinusSimple :> sig 
  type name = string 

  exception NameNotBound of name 
  exception BadFunApp of string
  exception Cycle of string 
  exception Todo of string 
  
  type core_exp = Core.core_exp
  datatype exp = 
                NAME of name 
              | IF_FI of guarded_exp list 
              | VCONAPP of Core.vcon * exp list
              | FUNAPP  of exp * exp
              | LAMBDAEXP of name * exp
      and guarded_exp = ARROWEXP of exp 
                      | EXPSEQ of exp  * guarded_exp 
                      | EXISTS of name * guarded_exp
                      | EQN    of name * exp * guarded_exp
  type value = exp Core.core_value
  datatype result = VAL of value | REJECT (* guarded_exps return results *)


  datatype def = DEF of name * exp

  val eval: value option Env.env -> exp -> value
  val solve: value option Env.env -> guarded_exp -> result

  val valString  : value -> string 
  val gexpString : guarded_exp -> string 
  val expString  : exp -> string 
  val defString  : def -> string 

  val runProg : def list -> unit 

end 
  =
struct 

  type name = string 

  exception NameNotBound of name 
  exception BadFunApp of string
  exception Cycle of string 
  exception Todo of string 
  
  type core_exp = Core.core_exp
  datatype exp = 
                NAME of name 
              | IF_FI of guarded_exp list 
              | VCONAPP of Core.vcon * exp list
              | FUNAPP  of exp * exp
              | LAMBDAEXP of name * exp
      (* and  sugared_guarded_exp = S_ARROWALPHA of  exp 
                      | S_EXPSEQ of  exp *  sugared_guarded_exp 
                      | S_EXISTS of name *  sugared_guarded_exp
                      | S_EQN    of  exp *  exp *  sugared_guarded_exp *)
      and guarded_exp = ARROWEXP of exp 
                      | EXPSEQ of exp  * guarded_exp 
                      | EXISTS of name * guarded_exp
                      | EQN    of name * exp * guarded_exp
  type value = exp Core.core_value
  datatype result = VAL of value | REJECT (* guarded_exps return results *)


  datatype def = DEF of name * exp

  


  fun boolOfValue (Core.VCON FALSE) = false 
    | boolOfValue _                 = true

  fun eqval (Core.VCON (v1, vs), Core.VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) =  false 

  fun optString printer (SOME x) = printer x 
    | optString printer NONE     = "NONE"


    fun gexpString (ARROWEXP e) = "-> " ^ expString e
      | gexpString (EXPSEQ (e, ge)) = expString e ^ "; " ^ gexpString ge
      | gexpString (EXISTS (x, ge)) = "∃ " ^ x ^ ". " ^ gexpString ge
      | gexpString (EQN (x, e, ge)) = 
                    x ^ " = " ^ expString e ^ "; " ^ gexpString ge 
    and expString (NAME n) = n
      | expString (IF_FI gs) = "if " ^ ListUtil.join gexpString "[]\n" gs ^ " fi"
      | expString (VCONAPP (v, es)) = Core.vconAppStr expString v es
      | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
      | expString (LAMBDAEXP (n, body)) = 
          StringEscapes.backslash ^ n ^ ". " ^ (expString body)
    and optExpString (SOME e) = "SOME " ^ expString e 
    | optExpString    NONE    = "NONE"

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

  fun valString (v as (Core.VCON (n, vs))) = Core.valString v
    | valString (Core.LAMBDA (x, body)) = 
        Char.toString (chr 92) ^ x ^ ". " ^ expString body

  fun optValStr v = optString valString v
    (* val optValStr = optString valString *)


  type lvar_env = value option Env.env

  fun binds (rho: lvar_env) n = Env.binds (rho, n)

  fun exists_in n (rho: lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))
    (* todo use this more! *)

  fun lvarEnvMerge (rho1 :  lvar_env) (rho2 :  lvar_env) = 
    Env.merge (fn (SOME x, SOME y)   => SOME x
                | (NONE,   SOME x)   => SOME x
                | (SOME x, NONE)     => SOME x
                | (NONE,   NONE)     => NONE) (rho1, rho2)

val rec stuck : lvar_env -> exp ->  bool = 
  fn rho => fn ex => 
    let fun unknown n = if not (Env.binds (rho, n)) then raise NameNotBound n 
                        else (Env.binds (rho, n))
                              andalso (not (isSome (Env.find (n, rho))))
        fun has_unbound_names e = 
          case e of NAME name => unknown name 
           | VCONAPP (v, es) => List.exists has_unbound_names es
           | FUNAPP (e1, e2) => has_unbound_names e1 orelse has_unbound_names e2 
           | IF_FI gs => List.exists has_unbound_gexp gs
           | LAMBDAEXP (n, body) => 
                  stuck (Env.bind (n, SOME (Core.VCON (Core.TRUE, [])), rho)) body
        and has_unbound_gexp g = 
          case g of ARROWEXP e    => has_unbound_names e
                  | EXISTS (_, g')  => has_unbound_gexp g'
                  | EXPSEQ (e', g') => has_unbound_names e' 
                                       orelse has_unbound_gexp g'
                  | EQN (n, e', g') => unknown n 
                                       orelse has_unbound_names e'
                                       orelse has_unbound_gexp g'
    in has_unbound_names ex 
  end 

  fun valIn (rho : lvar_env) n = 
    if exists_in n rho 
    then (Env.find (n, rho))
    else NONE 

  fun solve (rho_: lvar_env) gexpr = 
  (* chooseAndSolve reduces g and expands rho. 
  if it finds something it can't solve yet, 
  it skips it and add it to buildRest, 
  which lets solve look at the skipped part later. *)
    let datatype 'b solution = OK of 'b | REJ
        and status = CHANGED | UNCHANGED
      (* withtype 'b builder = ('b guarded_exp -> 'b guarded_exp) *)
        fun chooseAndSolve rho g buildRest status = 
         case g of ar as ARROWEXP e => OK (ar, rho, buildRest, status)
                 | EXISTS (n, g')     => let val rho' = Env.bind (n, NONE, rho) 
                                         in OK (g', rho', buildRest, CHANGED) 
                                         end 
              (* if e is stuck, move on. if we can do e, do e. yes status. *)
              | EXPSEQ (e, g') => 
                if stuck rho e
                then  let fun builder rest = buildRest (EXPSEQ (e, rest)) 
                      in  chooseAndSolve rho g' builder status
                      end
                else (case eval rho e of Core.VCON FALSE => REJ
                                      | _ => OK (g', rho, buildRest, CHANGED))
              | EQN (n, e, g') => 
                let val nstuck   = stuck rho (NAME n)
                    val rhsstuck = stuck rho e
                in 
                  (case (nstuck, rhsstuck) of 
                  (true, true) => 
                        let fun builder rest = buildRest (EQN (n, e, rest))
                        in  chooseAndSolve rho g' builder status
                        end 
                | (false, true) => 
                 let val nval = valOf (Env.find (n, rho)) 
                 in (case bindWith rho (e, nval)
                      of OK rho' => OK (g', rho', buildRest, CHANGED)
                             | _ => REJ)
                 end
                | _ => 
                    let val rhs  = eval rho e
                        val rho' = Env.bind (n, SOME rhs, rho)
                    in  if not (binds rho n) 
                        then OK (g', rho', buildRest, CHANGED)
                        else 
                          (case Env.find (n, rho)
                            of NONE   => OK (g', rho', buildRest, CHANGED)
                             | SOME v => if (eqval (v, rhs)) 
                                         then OK (g', rho, buildRest, UNCHANGED) 
                                         else REJ)
                    end) 
                end 
        and bindWith (rho : lvar_env) (e : exp, v : value) = 
        let val _ = print ("Env entering bindWith: " ^ (Env.toString optValStr rho) ^ "\n") 
            val _ = print ("bindwith on " ^ expString e ^ ", " ^ valString v ^ "\n")
            in 
          case (e, v) 
            of (NAME n, _) => 
                let val nval = valIn rho n 
                    val _ = print ("VAL of " ^ n ^ ": " ^ optValStr nval ^ "\n")
                in if isSome nval 
                  then if (eqval ((valOf nval), v)) then OK rho else REJ
                  else OK (Env.bind (n, SOME v, rho))
                end 
            | (VCONAPP (Core.K n, es), Core.VCON (Core.K n', vs)) => 
                if n <> n'
                  orelse List.length es <> List.length vs
                then REJ 
                else 
                  (* need to use the same environment, preventing bad name duplication *)
                  let val solns = 
                    foldr (fn ((ex, vl), OK rho') => 
                            (case bindWith rho' (ex, vl) 
                              of OK rho'' => OK (lvarEnvMerge rho'' rho')
                              | _ => REJ)
                           | _ => REJ) 
                    (OK rho) (ListPair.zip (es, vs))
                  (* List.map (bindWith rho) (ListPair.zip (es, vs)) *)
                      (* fun envSolutionConcat zs = 
                            foldr (fn (OK rho1, OK rho2) => 
                                        OK (lvarEnvMerge rho1 rho2)
                                      | _                => REJ) 
                                  (OK rho) zs *)
                  val x = solns
                  val _ =  print (case x of OK r => "ENV: " ^ (Env.toString optValStr r) ^ "\n" | REJ => "REJ")
                  in x 
                  end 
              | _ => if eqval (eval rho e, v) then OK rho else REJ
    end 
        fun solve' rho g = 
          case chooseAndSolve rho g (fn x => x) UNCHANGED  
            of REJ => REJECT 
            | OK (g', rho', buildRest, status) =>
            let val leftover = buildRest g' in 
            (case leftover
              of ARROWEXP e  => 
              VAL (eval rho' e)
              | nontrivial_gex  => 
                        if status = UNCHANGED
                          then raise Cycle ("cannot sort " ^ gexpString gexpr 
                                          ^ " because it contains a cycle"
                                          ^ " of logical variables.")
                        else 
                        solve' rho' leftover)
                        end 
        in solve' rho_ gexpr
        end 
      and eval (rho : lvar_env) e = 
          case e 
            of NAME n => 
              if not (Env.binds (rho, n))
              then raise NameNotBound (n ^ " in expr")
              else (case (Env.find (n, rho)) 
                      of NONE   => 
                      raise NameNotBound (n ^ " bound to bottom in " ^ 
                                         ((Env.toString optValStr rho) ^ "\n"))
                      | SOME v  => v)
            | IF_FI []      => raise Match
            | IF_FI (g::gs) => (case solve rho g
                                  of VAL v => v
                                  | REJECT => eval rho (IF_FI gs))
            | VCONAPP (Core.TRUE,  []) => Core.VCON (Core.TRUE, [])
            | VCONAPP (Core.FALSE, []) => Core.VCON (Core.FALSE, []) 
            | VCONAPP (Core.K n, es)  => Core.VCON (Core.K n, map (eval rho) es)
            | VCONAPP _ => 
               raise Impossible.impossible "erroneous vcon argument application"
            | FUNAPP (fe, param) => 
              (case eval rho fe 
                of Core.LAMBDA (n, b) => 
                  let val arg = eval rho param
                      val rho' = Env.bind (n, SOME arg, rho)
                    in eval rho' b
                    end
                 | _ => raise BadFunApp "attempted to apply non-function")  
                 | LAMBDAEXP (n, body) => Core.LAMBDA (n, body)

  fun def rho (DEF (n, e)) = 
    let val v = eval rho e
    in Env.bind (n, SOME v, rho)
    end

  fun runProg defs = 
  (  foldl (fn (d, env) => 
      let val rho = def env d
      in  Env.<+> (rho, env)
      end) Env.empty defs;
      ())  

end
