structure VMinus :> sig 
  type name = string 
  datatype 'a vcon = CONS | NIL | USERDEFINED of name | ALPHA of 'a
  datatype exp = E of exp exp'
  and 'a exp' = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of 'a vcon * 'a exp' list 
              | FUNAPP  of 'a exp' * 'a exp' list 
      and 'a guarded_exp = ARROWALPHA of 'a
                      | EXPSEQ of 'a exp' * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp' * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp'
end 
  = 
struct 
  (* type name = string
  datatype vcon = CONS | NIL | USERDEFINED of name | INT of int
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
  datatype 'a vcon = CONS | NIL | USERDEFINED of name | ALPHA of 'a
  datatype exp = E of exp exp'
  and 'a exp' = NAME of name 
              | IF_FI of 'a guarded_exp list 
              | VCONAPP of 'a vcon * 'a exp' list 
              | FUNAPP  of 'a exp' * 'a exp' list 
      and 'a guarded_exp = ARROWALPHA of 'a
                      | EXPSEQ of 'a exp' * 'a guarded_exp 
                      | EXISTS of name * 'a guarded_exp
                      | EQN    of name * 'a exp' * 'a guarded_exp
  datatype 'a def = DEF of name * 'a exp'
end
