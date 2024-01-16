structure Core :> sig 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype core_value = VCON of vcon * core_value list

  exception NameNotBound of name 

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | IF_THEN_ELSE of core_exp * core_exp * core_exp 
                  | LAMBDA of name * core_exp 
                  | FUNAPP of core_exp * core_exp 
  val evalcore        : core_value Env.env -> core_exp -> core_value
  val boolOfCoreValue : core_value -> bool 
  val strOfCoreExp    : core_exp -> string 
  val strOfCoreValue  : core_value -> string 
  val strBuilderOfVconApp : ('a -> string) -> vcon -> 'a list -> string
end 
  = 
struct 
  type name = string 
  datatype vcon = TRUE | FALSE | K of name 
  datatype core_value = VCON of vcon * core_value list

  exception NameNotBound of name 

  datatype core_exp = NAME of name 
                    | VCONAPP of vcon * core_exp list
                    | IF_THEN_ELSE of core_exp * core_exp * core_exp 
                    | LAMBDA of name * core_exp 
                    | FUNAPP of core_exp * core_exp 

  fun boolOfCoreValue (VCON (FALSE, [])) = false
    | boolOfCoreValue _                  = true

  fun evalcore rho (NAME n)  = if not (Env.binds (rho, n))
                              then raise NameNotBound n
                              else Env.find (n, rho)
    | evalcore rho (VCONAPP (v, es)) = let val vals = map (evalcore rho) es
                                   in VCON (v, vals)
                                   end 
    | evalcore rho (IF_THEN_ELSE (e1, e2, e3)) = 
                   (case evalcore rho e1
                    of VCON (FALSE, []) => evalcore rho e3
                     | _                => evalcore rho e2)
    | evalcore rho (LAMBDA (n, body)) = raise Impossible.unimp "lambda"
    | evalcore rho (FUNAPP (e1, e2))  = raise Impossible.unimp "funapp"
                     

  fun strBuilderOfVconApp f n args = 
      case (n, args)
      of (K n, vs) =>
        let val vcss = foldr (fn (vc, acc) => " " ^ f vc ^ acc) "" vs
        in n ^ vcss
        end 
    | (TRUE, [])  =>  "true"
    | (FALSE, []) =>  "false"
    | (TRUE, _)   =>  Impossible.impossible "true applied to args"
    | (FALSE, _)  =>  Impossible.impossible "false applied to args"

  fun strOfCoreExp (NAME n) = n
    | strOfCoreExp (VCONAPP (n, es)) = 
     strBuilderOfVconApp strOfCoreExp n es 
    | strOfCoreExp (IF_THEN_ELSE (e1, e2, e3)) = 
        "if " ^ strOfCoreExp e1 ^ "then " ^ strOfCoreExp e2 ^ "else " ^ strOfCoreExp e3
    | strOfCoreExp (LAMBDA (n, body)) = 
        Char.toString (chr 92) ^ n ^ "." ^ (strOfCoreExp body) (* backslash *)
    | strOfCoreExp (FUNAPP (e1, e2)) = strOfCoreExp e1 ^ " " ^ strOfCoreExp e2

  fun strOfCoreValue (VCON (v, vals)) = strBuilderOfVconApp strOfCoreValue v vals 


end
