structure PPlus :> sig 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (pattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
                      (* | WHEN   of pattern * exp *)
  datatype def = DEF of name * exp
end 
  = 
struct 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (pattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
                      (* | WHEN   of pattern * exp *)
  datatype def = DEF of name * exp

end 