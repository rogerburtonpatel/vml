structure OldCore :> sig 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'a core_value = VCON of vcon   * 'a core_value list 
                         | LAMBDA of name * 'a

  exception NameNotBound of name 
  exception BadFunApp of string 

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | IF_THEN_ELSE of core_exp * core_exp * core_exp 
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  val evalcore        : 'a core_value Env.env -> core_exp -> 'a core_value
  val eqval           : 'a core_value * 'a core_value -> bool
  val boolOfOldCoreValue : 'a core_value -> bool 
  val strOfOldCoreExp    : core_exp -> string 
  val valString  : 'a core_value -> string 
  val vconAppStr : ('a -> string) -> vcon -> 'a list -> string
end 
  = 
struct 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'a core_value = VCON of vcon * 'a core_value list | LAMBDA of name * 'a

  exception NameNotBound of name 
  exception BadFunApp of string 

  

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | IF_THEN_ELSE of core_exp * core_exp * core_exp 
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  fun boolOfOldCoreValue (VCON (FALSE, [])) = false
    | boolOfOldCoreValue _                  = true

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
    | evalcore rho (LAMBDAEXP (n, body)) = raise Impossible.unimp "lambda"
    | evalcore rho (FUNAPP (e1, e2))  = raise Impossible.unimp "funapp"
                     

  fun vconAppStr f n args = 
      case (n, args)
      of (K n, vs) =>
        let val vcss = foldr (fn (vc, acc) => " " ^ f vc ^ acc) "" vs
        in n ^ vcss
        end 
    | (TRUE, [])  =>  "true"
    | (FALSE, []) =>  "false"
    | (TRUE, _)   =>  Impossible.impossible "true applied to args"
    | (FALSE, _)  =>  Impossible.impossible "false applied to args"

  fun strOfOldCoreExp (NAME n) = n
    | strOfOldCoreExp (VCONAPP (n, es)) = 
     vconAppStr strOfOldCoreExp n es 
    | strOfOldCoreExp (IF_THEN_ELSE (e1, e2, e3)) = 
        "if " ^ strOfOldCoreExp e1 ^ "then " ^ strOfOldCoreExp e2 ^ "else " ^ strOfOldCoreExp e3
    | strOfOldCoreExp (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (strOfOldCoreExp body) (* backslash *)
    | strOfOldCoreExp (FUNAPP (e1, e2)) = strOfOldCoreExp e1 ^ " " ^ strOfOldCoreExp e2

  fun valString (VCON (v, vals)) = 
          vconAppStr valString v vals 
    | valString (LAMBDA (n, e)) = 
      Impossible.impossible 
      "stringifying core lambda- client code must handle this case"

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 
end
