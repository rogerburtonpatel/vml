structure VMinus :> sig 
  type name = string 
  datatype 'a vcon = K of name * 'a value list | TRUE | FALSE 
  and 'a value = VALPHA of 'a | VCON of 'a vcon (* expressions return values *)
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)

  exception NameNotBound of name 


  type core_exp = Core.core_exp

  datatype 'a exp = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp
      and 'a sugared_guarded_exp = S_ARROWALPHA of 'a
                      | S_EXPSEQ of 'a exp * 'a sugared_guarded_exp 
                      | S_EXISTS of name * 'a sugared_guarded_exp
                      | S_EQN    of 'a exp * 'a exp * 'a sugared_guarded_exp
      and 'a guarded_exp = ARROWALPHA of 'a
                      | EXPSEQ of 'a exp * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp
end 
  = 
struct 
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
  datatype 'a vcon = K of name * 'a value list | TRUE | FALSE 
  and 'a value = VALPHA of 'a | VCON of 'a vcon (* expressions return values *)
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)

  exception NameNotBound of name 
  exception Todo of string 
  
  type core_exp = Core.core_exp
  datatype 'a exp = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of Core.vcon * 'a exp list
              | FUNAPP  of 'a exp * 'a exp
      and 'a sugared_guarded_exp = S_ARROWALPHA of 'a
                      | S_EXPSEQ of 'a exp * 'a sugared_guarded_exp 
                      | S_EXISTS of name * 'a sugared_guarded_exp
                      | S_EQN    of 'a exp * 'a exp * 'a sugared_guarded_exp
      and 'a guarded_exp = ARROWALPHA of 'a
                      | EXPSEQ of 'a exp * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp

  fun boolOfValue (VCON FALSE) = false 
    | boolOfValue _              = true

  fun eqval (VALPHA a, VALPHA a')  = raise Impossible.unimp "compare two alphas"
    | eqval (VCON v1, VCON v2)     = 
      (case (v1, v2)
       of (TRUE, TRUE)             => true 
        | (FALSE, FALSE)           => true 
        | (K (n, vs), K (n', vs')) => 
            n = n' andalso ListPair.all eqval (vs, vs')
        | (_, _)   => false)
    | eqval (_, _) =  false 



  fun solve (rho : 'a value option Env.env) g = 
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
      | FUNAPP (fe, es) => raise Todo "eval function application"

  fun strOfValue (VALPHA a) = "alpha"
    | strOfValue (VCON v) = (case v of   
       (K (n, vcs)) => 
         let val vcss = foldl (fn (vc, acc) => strOfValue vc ^ " " ^ acc) "" vcs
         in n ^ " " ^ vcss
         end 
    | TRUE  => "true"
    | FALSE => "false")

    fun gexpString (ARROWALPHA a) = "'a"
    | gexpString (EXPSEQ (e, ge)) = expString e ^ "; " ^ gexpString ge
    | gexpString (EXISTS (x, ge)) = "∃" ^ x ^ ". " ^ gexpString ge
    | gexpString (EQN (x, e, ge)) = 
                    x ^ " = " ^ expString e ^ "; " ^ gexpString ge 
    and expString (NAME n) = n
    | expString (IF_FI ges) = "if " ^ ListUtil.join gexpString "[]" ges ^ " fi"
    | expString (VCONAPP (v, es)) = Core.strBuilderOfVconApp expString v es
    | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
    and optExpString (SOME e) = "SOME " ^ expString e 
    | optExpString NONE       = "NONE"


  (* sorting and solving *)

  type 'a lvar_env = 'a value option Env.env

  fun binds (rho: 'a lvar_env) n = Env.binds (rho, n)

  fun exists_in n (rho: 'a lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))


(* stuck says: can I solve this with the information I have now? 
i.e. do I have all the names I need to evaluate this expression? 
f is a function 'a -> bool, which lets us see if the final 'a is stuck. *)
val stuck : 'a lvar_env -> ('a -> bool) -> 'a exp ->  bool = 
  fn rho => fn f => fn ex => 
    let fun unknown n = not ((Env.binds (rho, n))
                        andalso (isSome (Env.find (n, rho))))
        fun has_unbound_names e = 
          case e of NAME name => unknown name 
           | VCONAPP (v, es) => List.exists has_unbound_names es
           | FUNAPP (e1, e2) => has_unbound_names e1 orelse has_unbound_names e2 
           | IF_FI gs => List.exists has_unbound_gexp gs
        and has_unbound_gexp g = 
          case g of ARROWALPHA a    => f a 
                  | EXISTS (_, g')  => has_unbound_gexp g'
                  | EXPSEQ (e', g') => has_unbound_names e' 
                                       orelse has_unbound_gexp g'
                  | EQN (n, e', g') => unknown n 
                                       orelse has_unbound_names e'
                                       orelse has_unbound_gexp g'
    in has_unbound_names ex 
  end 

  (* solve repeatedly calls chooseAndSolve until we're done or 
    until we reach a fixed point. if nothing changes and 
     we're not done, solve explodes. *)
  fun solve (rho_: 'a lvar_env) (stuckFn : 'a -> bool) gexpr = 
  (* chooseAndSolve reduces g and expands rho.  *)
    let fun chooseAndSolve rho g changed = 
      case g of ar as ARROWALPHA a   => (ar, rho, changed)
              | EXISTS (n, g') => (g', Env.bind (n, NONE, rho), true)
              (* if e is stuck, move on. if we can do e, do e. yes changed. *)
              | EXPSEQ (e, g') => if stuck rho stuckFn e
                                  then chooseAndSolve rho g' changed
                                  else (case eval rho e 
                                    of VCON FALSE => (g, rho, false) (* rejection *)
                                     | _ => (g', rho, true))
              | EQN (n, e, g') => if (stuck rho stuckFn (NAME n)) 
                                   orelse stuck rho stuckFn e
                                  then chooseAndSolve rho g' changed 
                                  else let val rhs = SOME (eval rho e) 
                                       in (g', Env.bind (n, rhs, rho), true)
                                       end 
    fun solve' rho g = 
    let 
    val (g', rho', changed) = chooseAndSolve rho g false 
    in case g' of ARROWALPHA a => (VAL (VALPHA a), rho')
       | nontrivial_gex  => 
                if not changed 
                then raise Cycle ("cannot sort " ^ gexpString gexpr 
                                  ^ " because it contains a cycle"
                                  ^ " of logical variables.")
                else solve' rho' g'
    end 
    in solve' rho_ gexpr
    end 

  (* and sortBindings rho gexpr = 
    let fun sortBindings' (EXISTS (e, ge)) = EXISTS (e, sortBindings' ge)
          | sortBindings' ge = 
      let fun moveAll rho_ binder_acc gex = 
          let val (bind_builder, changed, leftover, rho') = 
            moveIndependentsWith rho_ binder_acc (fn gexp => gexp) false gex
          (* val () = print ("intermediate sort: \n"
                          ^ "lhs: " 
                          ^ gexpString (bind_builder (ARROWEXP (NAME "")))
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
                          ^ gexpString (bind_builder (ARROWEXP (NAME "")))
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

end
