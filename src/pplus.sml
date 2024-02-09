structure PPlus :> sig 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (toplevelpattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and toplevelpattern =   PAT of pattern 
                            (* | WHEN   of toplevelpattern * exp *)
                            | ORPAT of pattern list 
                            | PATGUARD of toplevelpattern * (pattern * exp list) * exp
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
  datatype def = DEF of name * exp

  val expString : exp -> string
end 
  = 
struct 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (toplevelpattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
      and toplevelpattern =   PAT of pattern 
                            (* | WHEN   of toplevelpattern * exp *)
                            | ORPAT of pattern list 
                            | PATGUARD of toplevelpattern * (pattern * exp list) * exp
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
  datatype def = DEF of name * exp

  (* fun eval rho e = 
    case e 
      of NAME n => Env.find rho n 
       | VCONAPP (Core.TRUE,  []) => Core.TRUE 
       | VCONAPP (Core.FALSE, []) => Core.FALSE 
       | VCONAPP (Core.K n, es)   => Core.K (n, map (eval rho) es)
       | VCONAPP _ => 
               raise Impossible.impossible "erroneous vcon argument application" *)

  fun expString (NAME n) = n
    | expString (CASE (e, branches)) = 
      let 
          fun tlpatString (PAT p) = patString p
            | tlpatString (ORPAT []) = Impossible.impossible "empty orpat"
            | tlpatString (ORPAT [_]) = Impossible.impossible "singleton orpat"
            | tlpatString (ORPAT ps) = 
                        patString (hd ps) ^ 
                            (foldr (fn (p, acc) => "| " ^ patString p ^ acc) "" 
                            (tl ps))
            | tlpatString (PATGUARD (tlp, steps, res)) = Impossible.unimp "todo"
          and patString (PNAME n) = n 
            | patString (CONAPP (n, ps)) = 
                                Core.strBuilderOfVconApp patString (Core.K n) ps
          fun branchString (p, ex) = 
                                     tlpatString p ^ " => " ^ expString ex
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