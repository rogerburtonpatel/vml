signature VMINUS = sig 
  type name = Core'.name
  type vcon = Core'.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list
  type 'e multi = 'e Multi.multi
  datatype exp = C of exp Core'.t
               | I of (exp, exp multi) if_fi

  datatype def = DEF of name * exp

  type value = exp Core'.value

  val expString : exp -> string 
  val defString : def -> string 

  val eqexp : exp * exp -> bool

  val gmap :  ('a -> 'b) -> 'a guard -> 'b guard

end 
structure VMinus :> VMINUS
  = struct
  type name = string
  type vcon = Core'.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * ('e guard list * 'a)) list
  type 'e multi = 'e Multi.multi
  datatype exp = C of exp Core'.t
               | I of (exp, exp multi) if_fi

  datatype def = DEF of name * exp

  type value = exp Core'.value

    fun gmap f (EQN (n, e))        = EQN (n, f e)
      | gmap f (CONDITION e)       = CONDITION (f e)
      | gmap f (CHOICE (gs1, gs2)) = CHOICE (map (gmap f) gs1, map (gmap f) gs2)


  fun expString   (C ce)               = Core'.expString expString ce
    | expString   (I (IF_FI bindings)) = "if\n" ^ if_fiString bindings ^ "\nfi"
  and guardString (EQN (n, e))         = n ^ " = " ^ expString e
    | guardString (CONDITION e)        = expString e
    | guardString (CHOICE (gs1, gs2))  = 
            let val compress = String.concatWith "; " o map guardString
            in  compress gs1 ^ " | " ^ compress gs2 
            end 
  and if_fiString [] = ""
    | if_fiString ((ns, (gs, r)) :: rest) = 
        let val (existential, dot) = if null ns then ("", "") else ("E ", ". ")
            val binds    = existential ^ String.concatWith " " ns ^ dot
            val gStrings = String.concatWith "; " (map guardString gs)
            val rString  = (Multi.multiString expString r)
        in "  " ^ binds ^ gStrings ^ " -> " ^ rString ^ "\n" ^ if_fiString rest
        end 

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

fun eqexp (C cex1, C cex2) = Core'.expString expString cex1 = Core'.expString expString cex2
  | eqexp (I i1, I i2) = Impossible.unimp "compare 2 if-fis"
  | eqexp _ = false 

    
    (* (ALPHA a1, ALPHA a2) => Alpha.eqval a1 a2 
     | (NAME n1, NAME n2)   => n1 = n2
     | (IF_FI gs1, IF_FI gs2) => ListPair.allEq eqgexp(gs1, gs2)
     | (VCONAPP (vc1, es1), VCONAPP (vc2, es2)) => 
        Core.eqval (Core.VCON (vc1, []), Core.VCON (vc1, []))
        andalso 
        ListPair.allEq eqexp (es1, es2)
     | (FUNAPP (e1, e2), FUNAPP (e3, e4)) =>
        ListPair.allEq eqexp ([e1, e2], [e3, e4])
     | (LAMBDAEXP (n1, e1), LAMBDAEXP (n2, e2)) => 
        n1 = n2 andalso eqexp (e1, e2)
     | _ => false  *)

  fun optString printer (SOME x) = printer x 
    | optString printer NONE     = "NONE"

  (* fun eval  *)


end

structure FinalVMinusWithAlpha = struct 
  type name = Core'.name
  type vcon = Core'.vcon
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * 'e guard list * 'a) list
  datatype 'e multi = MULTI of 'e list

type 'e core_exp = 'e Core'.t

datatype simple = C_S of simple core_exp
                | I_S  of (simple, simple) if_fi

datatype 'a exp = S of simple 
                | C of 'a exp core_exp
                | I of (simple, 'a) if_fi

val x__ = S (C_S (Core'.NAME "n"))
val _ = S (C_S (Core'.NAME "n"))
val test__ = I (IF_FI [([], [], 3)])

  datatype 'a def = DEF of name * 'a exp

end 


structure RenamedVMinus = struct
  type name = string
  datatype 'a exp = 
                 ALPHA of 'a 
              |  NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp
              | LAMBDAEXP of name * 'a exp
      and 'a guarded_exp = GUARDED of name list * 'a guard list * 'a exp 
      and 'a guard = CONDITION of 'a exp
                   | EQN of name * 'a exp
  and 'a vcon = K of name * 'a value list | TRUE | FALSE 
  and 'a value = VALPHA of 'a | VCON of 'a vcon | LAMBDA of name * 'a exp (* expressions return values *)
end

signature OLDVMINUS = sig  
  type name = string 

  exception NameNotBound of name 
  exception Cycle of string 

  type core_exp = Core.core_exp

  datatype 'a exp = 
                 ALPHA of 'a 
              |  NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp
              | LAMBDAEXP of name * 'a exp
      and 'a guarded_exp = ARROWALPHA of 'a exp 
                      | EXPSEQ of 'a exp * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp * 'a guarded_exp
  and 'a vcon = K of name * 'a value list | TRUE | FALSE 
  and 'a value = VALPHA of 'a | VCON of 'a vcon | LAMBDA of name * 'a exp (* expressions return values *)

  datatype 'a sugared_guarded_exp
    = S_ARROWALPHA of 'a exp 
    | S_EXPSEQ of 'a exp * 'a sugared_guarded_exp 
    | S_EXISTS of name * 'a sugared_guarded_exp
    | S_EQN    of 'a exp * 'a exp * 'a sugared_guarded_exp
  
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)
  datatype 'a def = DEF of name * 'a exp

  val valString : 'a value -> string 
  val gexpString : 'a guarded_exp -> string 
  val expString : 'a exp -> string 
  val eval      : 'a value option Env.env -> 'a exp -> 'a value 
  val solve      : 'a value option Env.env -> 'a guarded_exp -> 'a result
  val eqexp      : 'a exp * 'a exp -> bool 
  
  val map  : ('a -> 'b) -> 'a exp -> 'b exp
  val gmap : ('a -> 'b) -> 'a guarded_exp -> 'b guarded_exp

end 

functor VMFn (structure A : ALPHA (*sus*) ) :> OLDVMINUS = struct  
   (* signature ALPHA probably cannot be implemented in any useful way *)

  (* type name = string
  datatype vcon = CONS | NIL | K of name | INT of int
  datatype exp = NAME of name 
               | IF_FI of exp guarded_exp list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp  
      and 'a guarded_exp = ARROWALPHA of 'a
                         | EXPSEQ of exp * 'a guarded_exp 
                         | EXISTS of name * 'a guarded_exp
                         | EQN    of name * exp * 'a guarded_exp
  datatype def = DEF of name * exp *)
  (* idea: qualify many more things with a 'a. *)
  type name = string 

  exception NameNotBound of name 
  exception Cycle of string 

  type core_exp = Core.core_exp

  datatype 'a exp = 
                 ALPHA of 'a 
              |  NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp
              | LAMBDAEXP of name * 'a exp
      and 'a sugared_guarded_exp = S_ARROWALPHA of 'a exp 
                      | S_EXPSEQ of 'a exp * 'a sugared_guarded_exp 
                      | S_EXISTS of name * 'a sugared_guarded_exp
                      | S_EQN    of 'a exp * 'a exp * 'a sugared_guarded_exp
      and 'a guarded_exp = ARROWALPHA of 'a exp 
                      | EXPSEQ of 'a exp * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp * 'a guarded_exp
  and 'a vcon = K of name * 'a value list | TRUE | FALSE 
  and 'a value = VALPHA of 'a | VCON of 'a vcon | LAMBDA of name * ('a exp ) (* expressions return values *)
  
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)
  datatype 'a def = DEF of name * 'a exp


  fun boolOfValue (VCON FALSE) = false 
    | boolOfValue _              = true

  
fun eqexp (ex1, ex2) = 
  case (ex1, ex2)
    of (ALPHA a1, ALPHA a2) => Alpha.eqval a1 a2 
     | (NAME n1, NAME n2)   => n1 = n2
     | (IF_FI gs1, IF_FI gs2) => ListPair.allEq eqgexp(gs1, gs2)
     | (VCONAPP (vc1, es1), VCONAPP (vc2, es2)) => 
        Core.eqval (Core.VCON (vc1, []), Core.VCON (vc1, []))
        andalso 
        ListPair.allEq eqexp (es1, es2)
     | (FUNAPP (e1, e2), FUNAPP (e3, e4)) =>
        ListPair.allEq eqexp ([e1, e2], [e3, e4])
     | (LAMBDAEXP (n1, e1), LAMBDAEXP (n2, e2)) => 
        n1 = n2 andalso eqexp (e1, e2)
     | _ => false 

and eqgexp (g1, g2) = Impossible.unimp "not yet"

  fun eqval (VALPHA a, VALPHA a')  = A.eqval a a'
    | eqval (VCON v1, VCON v2)     = 
      (case (v1, v2)
       of (TRUE, TRUE)             => true 
        | (FALSE, FALSE)           => true 
        | (K (n, vs), K (n', vs')) => 
            n = n' andalso ListPair.all eqval (vs, vs')
        | (_, _)   => false)
    | eqval (_, _) =  false 

  fun optString printer (SOME x) = printer x 
    | optString printer NONE     = "NONE"


(* 
  fun solve (rho : 'a value option Env.env) g = 
    case g of ARROWALPHA e => VAL (eval rho e)
            | EXPSEQ (e, g') => 
                if (boolOfValue (eval rho e)) then solve rho g' else REJECT 
            | EXISTS (n, g') => solve (Env.bind (n, NONE, rho)) g'
            | EQN (n, e, g') => 
                              if not (Env.binds (rho, n))
                              then raise NameNotBound (n ^ " in guarded expr")
                              (* check for solvability *)
                              else let val v = eval rho e
                                       val nv = Env.find (n, rho)
                                   in (case nv of NONE => REJECT 
                                        | SOME v' => 
                                   if not (eqval (v, v'))
                                   then REJECT 
                                   else solve (Env.bind (n, SOME v, rho)) g')
                                   end
  and eval (rho : 'a value option Env.env) e = 
    case e 
      of ALPHA a => VALPHA a 
        | NAME n => 
        if not (Env.binds (rho, n))
        then raise NameNotBound (n ^ " in expr")
        else (case (Env.find (n, rho)) 
                of NONE => raise NameNotBound (n ^ " bound to bottom")
                | SOME v => v)
       | IF_FI [] => raise Match
       | IF_FI (g::gs) => (case solve rho g
                            of VAL v => v
                            | REJECT => eval rho (IF_FI gs))
      | VCONAPP (Core.TRUE, []) => VCON TRUE
      | VCONAPP (Core.FALSE, []) => VCON FALSE 
      | VCONAPP (Core.K n, []) => VCON (K (n, []))
      | VCONAPP (Core.K n, es) => VCON (K (n, map (eval rho) es))
      | VCONAPP _ => 
              raise Impossible.impossible "erroneous vcon argument application"
      | FUNAPP (fe, es) => raise Todo "eval function application" *)


    fun gexpString (ARROWALPHA e) = "-> " ^ expString e
      | gexpString (EXPSEQ (e, ge)) = expString e ^ "; " ^ gexpString ge
      | gexpString (EXISTS (x, ge)) = "∃ " ^ x ^ ". " ^ gexpString ge
      | gexpString (EQN (x, e, ge)) = 
                    x ^ " = " ^ expString e ^ "; " ^ gexpString ge 
    and expString (ALPHA a) = "'a"
      | expString (NAME n) = n
      | expString (IF_FI gs) = "if " ^ ListUtil.join gexpString "[]" gs ^ " fi"
      | expString (VCONAPP (v, es)) = Core.vconAppStr expString v es
      | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
      | expString (LAMBDAEXP (n, body)) = 
          StringEscapes.backslash ^ n ^ ". " ^ (expString body)
    and optExpString (SOME e) = "SOME " ^ expString e 
    | optExpString    NONE    = "NONE"

  fun valString (VALPHA a) = "alpha"
    | valString (VCON v) = (case v of   
       (K (n, vs)) => 
        Core.vconAppStr valString (Core.K n) vs 
    | TRUE  => "true"
    | FALSE => "false")
    | valString (LAMBDA (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (expString body)

    
    
    val _ = optString  : ('a -> string) -> 'a option -> string 
    val _ = valString : 'a value -> string

    fun optValStr v = optString valString v
    (* val optValStr = optString valString *)


  (* sorting and solving *)

  type 'a lvar_env = 'a value option Env.env

  fun binds (rho: 'a lvar_env) n = Env.binds (rho, n)

  fun exists_in n (rho: 'a lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))
    (* todo use this more! *)

  fun lvarEnvMerge (rho1 : 'a lvar_env) (rho2 : 'a lvar_env) = 
    Env.merge (fn (SOME x, SOME y)   => SOME x
                | (NONE,   SOME x)   => SOME x
                | (SOME x, NONE)     => SOME x
                | (NONE,   NONE)     => NONE) (rho1, rho2)


(* stuck says: can I solve this with the information I have now? 
i.e. do I have all the names I need to evaluate this expression? 
f is a function 'a -> bool, which lets us see if the final 'a is stuck. *)
val rec stuck : 'a lvar_env -> ('a -> bool) -> 'a exp ->  bool = 
  fn rho => fn f => fn ex => 
    let fun unknown n = if not (Env.binds (rho, n)) then raise NameNotBound n 
                        else (Env.binds (rho, n))
                              andalso (not (isSome (Env.find (n, rho))))
        fun has_unbound_names e = 
          case e of ALPHA a => f a 
           | NAME name => unknown name 
           | VCONAPP (v, es) => List.exists has_unbound_names es
           | FUNAPP (e1, e2) => has_unbound_names e1 orelse has_unbound_names e2 
           | IF_FI gs => List.exists has_unbound_gexp gs  
           | LAMBDAEXP (n, body) => 
                  stuck (Env.bind (n, SOME (VCON TRUE), rho)) f body
                                        (* dummy sentinel, "name is bound" *)
        and has_unbound_gexp g = 
          case g of ARROWALPHA e    => has_unbound_names e
                  | EXISTS (_, g')  => has_unbound_gexp g'
                  | EXPSEQ (e', g') => has_unbound_names e' 
                                       orelse has_unbound_gexp g'
                  | EQN (n, e', g') => unknown n 
                                       orelse has_unbound_names e'
                                       orelse has_unbound_gexp g'
    in has_unbound_names ex 
  end 

  (* todo: this. *)
  val stuckFn : 'a -> bool = A.stuckFn 

  val alphaEvaluator: 'a -> 'b = A.alphaEvaluator


  fun valIn (rho : 'a lvar_env) n = 
    if exists_in n rho 
    then (Env.find (n, rho))
    else NONE 

  (* bindWith takes an envrionment, an expression, and a value 
     and returns a refined environment with names in the expression
     bound to corresponding parts of the value or fails. *)


    

  (* datatype 'a exp = 
                 ALPHA of 'a 
              |  NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp *)


  (* solve repeatedly calls chooseAndSolve until we're done or 
    until we reach a fixed point. if nothing changes and 
     we're not done, solve explodes. *)
  fun solve (rho_: 'a lvar_env) gexpr = 
  (* chooseAndSolve reduces g and expands rho. 
  if it finds something it can't solve yet, 
  it skips it and add it to buildRest, 
  which lets solve look at the skipped part later. *)
    let datatype 'b solution = OK of 'b | REJ
        and status = CHANGED | UNCHANGED
      (* withtype 'b builder = ('b guarded_exp -> 'b guarded_exp) *)
        fun chooseAndSolve rho g buildRest status = 
         case g of ar as ARROWALPHA e => OK (ar, rho, buildRest, status)
                 | EXISTS (n, g')     => let val rho' = Env.bind (n, NONE, rho) 
                                         in OK (g', rho', buildRest, CHANGED) 
                                         end 
              (* if e is stuck, move on. if we can do e, do e. yes status. *)
              | EXPSEQ (e, g') => 
                if stuck rho stuckFn e
                then  let fun builder rest = buildRest (EXPSEQ (e, rest)) 
                      in  chooseAndSolve rho g' builder status
                      end
                else (case eval rho e of VCON FALSE => REJ
                                      | _ => OK (g', rho, buildRest, CHANGED))
              | EQN (n, e, g') => 
                let val nstuck   = stuck rho stuckFn (NAME n)
                    val rhsstuck = stuck rho stuckFn e
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
        and bindWith (rho : 'a lvar_env) (e : 'a exp, v : 'a value) = 
        let 
            val _ = print ("Env entering bindWith: " ^ (Env.toString optValStr rho) ^ "\n") 
            val _ = print ("bindwith on " ^ expString e ^ ", " ^ valString v ^ "\n")
            val () = () 
            in 
          case (e, v) 
            of (NAME n, _) => 
                let val nval = valIn rho n 
                    val _ = print ("VAL of " ^ n ^ ": " ^ optValStr nval ^ "\n")
                in if isSome nval 
                  then if (eqval ((valOf nval), v)) then OK rho else REJ
                  else OK (Env.bind (n, SOME v, rho))
                end 
            | (VCONAPP (Core.K n, es), VCON (K (n', vs))) => 
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
              of ARROWALPHA e  => 
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
      and eval (rho : 'a lvar_env) e = 
          case e 
            of ALPHA a => VALPHA (alphaEvaluator a) 
              | NAME n => 
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
            | VCONAPP (Core.TRUE,  []) => VCON TRUE
            | VCONAPP (Core.FALSE, []) => VCON FALSE 
            | VCONAPP (Core.K n, es)   => VCON (K (n, map (eval rho) es))
            | VCONAPP _ => 
               raise Impossible.impossible "erroneous vcon argument application"
            | FUNAPP (fe, param) => 
              (case eval rho fe 
                  of LAMBDA (n, b) => 
                    let val arg = eval rho param
                        val rho' = Env.bind (n, SOME arg, rho)
                      in eval rho' b
                      end
                  | _ => raise Core.BadFunApp "attempted to apply non-function")
            | LAMBDAEXP (n, ex) => LAMBDA (n, ex)

                  (* if (stuck rho stuckFn (NAME n)) 
                      andalso stuck rho stuckFn e
                  then let fun builder rest = buildRest (EQN (n, e, rest))
                        in  chooseAndSolve rho g' builder status
                        end 
                  else 
                    let val rhs  = eval rho e
                        val rho' = Env.bind (n, SOME rhs, rho)
                    in  if not (binds rho n) 
                        then OK (g', rho', buildRest, CHANGED)
                        else 
                          (case Env.find (n, rho)
                            of NONE => OK (g', rho', buildRest, CHANGED)
                             | SOME v => if (eqval (v, rhs)) 
                                         then OK (g', rho, buildRest, UNCHANGED) 
                                         else REJ)
                    end  *)

  (* and sortBindings rho gexpr = 
    let fun sortBindings' (EXISTS (e, ge)) = EXISTS (e, sortBindings' ge)
          | sortBindings' ge = 
      let fun moveAll rho_ binder_acc gex = 
          let val (bind_builder, changed, leftover, rho') = 
            moveIndependentsWith rho_ binder_acc (fn gexp => gexp) false gex
          (* val () = print ("intermediate sort: \n"
                          ^ "lhs: " 
                          ^ gexpString (bind_builder (ARROWALPHA (NAME "")))
                          ^ "\n rhs: " ^ gexpString leftover
                          ^ "\n rho: " ^ Env.toString optExpString rho'
                          ^ "\n") *)
          in case leftover 
              of ar as ARROWALPHA a => bind_builder ar
                | nontrivial_gex  => 
                if not changed 
                then raise Cycle ("cannot sort " ^ gexpString gexpr 
                                  ^ " because it contains a cycle"
                                  ^ " of logical variables.")
                else moveAll rho' bind_builder leftover
          end 
      in moveAll rho (fn gexp => gexp) ge 
      end 
    in sortBindings' gexpr
    end *)


  (* fun solve (rho_: 'a lvar_env) g_ = 
    let fun chooseAndSolve rho g changed = 
      case g of ARROWALPHA a   => (ARROWALPHA a, rho, changed)
              | EXISTS (n, g') => (g', Env.bind (n, NONE, rho), true)
              | EXPSEQ (e, g') => 
    
    in chooseAndSolve rho_ g_ false 
    end  *)
    (* fun solve (rho : 'a lvar_env) g = 
    case g of ARROWALPHA a => VAL (VALPHA a)
            | EXPSEQ (e, g') => 
                if (boolOfValue (eval rho e)) then solve rho g' else REJECT 
            | EXISTS (n, g') => solve (Env.bind (n, NONE, rho)) g'
            | EQN (n, e, g') => 
                              if not (Env.binds (rho, n))
                              then raise NameNotBound (n ^ " in guarded expr")
                              (* check for solvability *)
                              else let val v = eval rho e
                                       val nv = Env.find (n, rho)
                                   in (case nv of NONE => REJECT 
                                        | SOME v' => 
                                   if not (eqval (v, v'))
                                   then REJECT 
                                   else solve (Env.bind (n, SOME v, rho)) g')
                                   end
  and eval (rho : 'a value option Env.env) e = 
    case e 
      of NAME n => 
        if not (Env.binds (rho, n))
        then raise NameNotBound (n ^ " in expr")
        else (case (Env.find (n, rho)) 
                of NONE => raise NameNotBound (n ^ " bound to bottom")
                | SOME v => v)
       | IF_FI [] => raise Match
       | IF_FI (g::gs) => (case solve rho g
                            of VAL v => v
                            | REJECT => eval rho (IF_FI gs))
      | VCONAPP (Core.TRUE, []) => VCON TRUE
      | VCONAPP (Core.FALSE, []) => VCON FALSE 
      | VCONAPP (Core.K n, []) => VCON (K (n, []))
      | VCONAPP (Core.K n, es) => VCON (K (n, map (eval rho) es))
      | VCONAPP _ => 
              raise Impossible.impossible "erroneous vcon argument application"
      | FUNAPP (fe, es) => raise Todo "eval function application" *)

(* 
  fun floatExists rho gexp = 
    let fun checkBound e rho_ = 
          case e of NAME n => if not (binds rho_ n)
                                      then raise NameNotBound n
                                      else ()
                                |    _ =>  ()
    fun normalize rho' buildEs buildGEs gexpr = 
      case gexpr of 
        ar as (ARROWALPHA a) => buildEs (buildGEs ar)
       | (EXPSEQ (e, ge)) =>
            let val () = checkBound e rho'
                val bind_seq = (fn ge' => buildGEs (EXPSEQ (e, ge')))
            in normalize rho' buildEs bind_seq ge
            end
       | (EXISTS (x, ge)) =>
            let val bind_exists = (fn ge' => buildEs (EXISTS (x, ge')))
                val rho''       = Env.bind (x, NONE, rho')
            in normalize rho'' bind_exists buildGEs ge 
            end
       | (EQN (y, e, ge)) =>
            let val () = checkBound e rho'
                val () = if not (binds rho' y) then raise NameNotBound y else ()
                val bind_binder = (fn gx => buildGEs (EQN (y, e, gx)))
            (* no need to add to rho' here: we're only checking if names
                are bound, not whether they're known. *)
            in normalize rho' buildEs bind_binder ge
            end
    in normalize rho (fn ge => ge) (fn ge => ge) gexp
    end

  fun moveIndependentsWith rho buildBinds buildLeftover changed gexpr = 
    case gexpr of 
      (ARROWALPHA a) => 
          (buildBinds, changed, buildLeftover (ARROWALPHA a), rho)
      | (EXPSEQ (NAME n, ge)) => 
          let val (buildBinds', buildLeftover', changed') = 
            if   exists_in n rho
            then ((fn gexp => buildBinds (EXPSEQ (NAME n, gexp))), 
                  buildLeftover, 
                  true)
            else (buildBinds, 
                (fn gexp => buildLeftover (EXPSEQ (NAME n, gexp))), 
                changed)
          in moveIndependentsWith rho buildBinds' buildLeftover' changed' ge
          end 
      | (EXPSEQ (IF_FI ges, ge)) =>
        (* EXPSEQ (IF_FI (map (sort_guard rho) ges), ge)*)
        raise Todo "sort nested guarded exps"
      | (EXPSEQ (e, ge)) =>
              moveIndependentsWith rho buildBinds buildLeftover changed ge
      | (EXISTS _) => 
        raise Impossible.impossible ("moveIndependentsWith should only be "
                                    ^ "called after floatExists")
      | (EQN (x, y as NAME y', ge)) =>  
            (* val () = print ("in moveIndependentsWith equation: \n rho: " 
                  ^ Env.toString optExpString rho
                  ^ "\n current ge: " 
                  ^ gexpString (EQN (x, y, ge))
                  ^ "\n") *)
        let val (buildBinds', buildLeftover', changed', rho') = 
            if exists_in x rho then 
              if exists_in y rho then 
                if 

              (* if exists_in x rho orelse exists_in y' rho
              then 
                ((fn gexp => buildBinds (EQN (x, y, gexp))),
                buildLeftover, 
                true, 
                Env.bind (y', SOME (NAME x), 
                                          Env.bind (x, SOME (NAME y'), rho)))
              else (buildBinds, 
                  (fn gexp => buildLeftover (EQN (x, y, gexp))), 
                  changed, 
                  rho)
          in moveIndependentsWith rho' buildBinds' buildLeftover' changed' ge
          end  *)
      | (EQN (x, e, ge)) =>
        let val (buildBinds', buildLeftover', changed', rho') = 
              ((fn gexp => EQN (x, e, gexp)), 
                  buildLeftover, 
                  true, 
                  Env.bind (x, SOME e, rho))
          in moveIndependentsWith rho' buildBinds' buildLeftover' changed' ge
          end  *)
(* 
  and sortBindings rho gexpr = 
    let fun sortBindings' (EXISTS (e, ge)) = EXISTS (e, sortBindings' ge)
          | sortBindings' ge = 
      let fun moveAll rho_ binder_acc gex = 
          let val (bind_builder, changed, leftover, rho') = 
            moveIndependentsWith rho_ binder_acc (fn gexp => gexp) false gex
          (* val () = print ("intermediate sort: \n"
                          ^ "lhs: " 
                          ^ gexpString (bind_builder (ARROWALPHA (NAME "")))
                          ^ "\n rhs: " ^ gexpString leftover
                          ^ "\n rho: " ^ Env.toString optExpString rho'
                          ^ "\n") *)
          in case leftover 
              of ar as ARROWALPHA a => bind_builder ar
                | nontrivial_gex  => 
                if not changed 
                then raise Cycle ("cannot sort " ^ gexpString gexpr 
                                  ^ " because it contains a cycle"
                                  ^ " of logical variables.")
                else moveAll rho' bind_builder leftover
          end 
      in moveAll rho (fn gexp => gexp) ge 
      end 
    in sortBindings' gexpr
    end

  and sort_guard rho ge = sortBindings rho (floatExists rho ge) *)

(* story: parse in an exp. eval it. if it has if-fi, sort each guarded exp and solve it. *)
(* story: parse in an exp. eval it. if it has if-fi, solve it sortingly. *)

 fun map f = Impossible.unimp "change alpha"
 fun gmap f = Impossible.unimp "change alpha"
 (* fun gmap f g = 
  case g of 
      ar as ARROWALPHA e   => ar
    | EXPSEQ (e, g') => Impossible.unimp "not yet"  
    | EXISTS (n, g') => _
    | EQN (n, e, g') => _ *)

end
