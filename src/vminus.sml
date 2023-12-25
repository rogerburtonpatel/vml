structure VMinus :> sig 
  type name = string 
  datatype 'a vcon = K of name * 'a vcon list | ALPHA of 'a | TRUE | FALSE 
  datatype 'a value = VALPHA of 'a vcon (* expressions return values *)
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)

  exception NameNotBound of name 

  datatype exp = E of exp exp'
  and 'a exp' = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of 'a vcon * 'a exp' list (* where we get 'a *)
              | FUNAPP  of 'a exp' * 'a exp' list 
      and 'a guarded_exp = ARROWALPHA of 'a exp' 
                      | EXPSEQ of 'a exp' * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp' * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp'
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
  datatype 'a vcon = K of name * 'a vcon list | ALPHA of 'a | TRUE | FALSE 
  datatype 'a value = VALPHA of 'a vcon (* expressions return values *)
  datatype 'a result = VAL of 'a value | REJECT (* guarded_exps return results *)

  exception NameNotBound of name 
  exception Todo of string 
  
  datatype exp = E of exp exp'
  and 'a exp' = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of 'a vcon * 'a exp' list 
              | FUNAPP  of 'a exp' * 'a exp' list 
      and 'a guarded_exp = ARROWALPHA of 'a exp'
                      | EXPSEQ of 'a exp' * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp' * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp'

  fun boolOfValue (VALPHA FALSE) = false 
    | boolOfValue _              = true

  fun eqval (VALPHA a, VALPHA a') = 
      (case (a, a')
       of (ALPHA a1, ALPHA a2) => a1 = a2
        | (TRUE, TRUE)         => true 
        | (FALSE, FALSE)         => true 
        | (K (n, vs), K (n', vs')) => 
            n = n' andalso ListPair.all eqval (map VALPHA vs, map VALPHA vs')
        | (_, _) => false)

  fun solve rho g = 
    case g of ARROWALPHA a => VAL (eval rho a)
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
  and eval rho e = 
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
      | VCONAPP (con, []) => VALPHA con
      | VCONAPP (K (n, []), es) => 
          VALPHA (K (n, List.map ((fn VALPHA vc => vc) o (eval rho)) 
                                        es))
      | VCONAPP _ => 
              raise Impossible.impossible "erroneous vcon argument application"
      | FUNAPP (fe, es) => raise Todo "eval function application"

  fun strOfVcon (K (n, vcs)) = 
        let val vcss = List.foldl (fn (vc, acc) => strOfVcon vc ^ acc) "" vcs
        in "(n " ^ vcss ^ ")"
        end 
  | strOfVcon (ALPHA a) = raise Todo "print an alpha"
  | strOfVcon TRUE =  "true"
  | strOfVcon FALSE = "false"
end
