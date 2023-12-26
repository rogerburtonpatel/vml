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

  fun strOfValue (VALPHA a) = raise Impossible.unimp "print alpha"
    | strOfValue (VCON v) = (case v of   
       (K (n, vcs)) => 
         let val vcss = foldl (fn (vc, acc) => strOfValue vc ^ " " ^ acc) "" vcs
         in n ^ " " ^ vcss
         end 
    | TRUE  => "true"
    | FALSE => "false")
end
