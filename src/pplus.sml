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

  val expString : exp -> string
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

  fun expString (NAME n) = n
    | expString (CASE (e, branches)) = 
      let fun patString (PNAME n) = n 
            | patString (CONAPP (n, ps)) = 
                                Core.strBuilderOfVconApp patString (Core.K n) ps
          fun branchString (p, ex) = 
                                     patString p ^ " => " ^ expString ex
          in "case " ^ expString e ^ " of " ^ 
          (if null branches 
          then "" 
          else branchString (hd branches) ^ 
                (foldr (fn (br, acc) => "\n| " ^ branchString br ^ acc) "\n" 
                 (tl branches)))
          end
      | expString (VCONAPP (v, es)) = Core.strBuilderOfVconApp expString v es
      | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2

end 