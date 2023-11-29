structure PPlus :> sig 
  type name = string 
  datatype vcon = CONS | NIL | USERDEFINED of name | INT of int
  datatype exp = NAME of name 
               | CASE of exp * (pattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and pattern =     PNAME of name
                      | CONAPP of pattern list 
                      | WHEN   of pattern * exp
  datatype def = DEF of name * exp
end 
  = 
struct 
  type name = string 
  datatype vcon = CONS | NIL | USERDEFINED of name | INT of int
  datatype exp = NAME of name 
               | CASE of exp * (pattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and pattern =     PNAME of name
                      | CONAPP of pattern list 
                      | WHEN   of pattern * exp
  datatype def = DEF of name * exp

end 