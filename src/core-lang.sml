signature CORE = sig
  type name = string 
  type vcon
  type 'exp exp'  (* all the expressions we don't care about *)

  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp exp'  (* everything else *)
end

functor MkCore(type 'a exp'
               type vcon) :> CORE where type 'a exp' = 'a exp'
                                    and type vcon = vcon
  =
struct
  type name = string 
  type vcon = vcon
  type 'a exp' = 'a exp'
  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp exp'  (* everything else *)
end

structure NewPPlus =
  MkCore(type name = string
         datatype vcon = VCON of string
         datatype pat = NAME of name | APP of vcon * pat list
         datatype 'a exp' = CASE of 'a * (pat * 'a) list)


structure Core :> sig 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'exp core_value = VCON of vcon   * 'exp core_value list 
                         | LAMBDA of name * 'exp

  exception NameNotBound of name 
  exception BadFunApp of string 

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | IF_THEN_ELSE of core_exp * core_exp * core_exp 
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  val evalcore        : 'a core_value Env.env -> core_exp -> 'a core_value
  val eqval           : 'a core_value * 'a core_value -> bool
  val boolOfCoreValue : 'a core_value -> bool 
  val strOfCoreExp    : core_exp -> string 
  val strOfCoreValue  : 'a core_value -> string 
  val strBuilderOfVconApp : ('a -> string) -> vcon -> 'a list -> string
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
    | evalcore rho (LAMBDAEXP (n, body)) = raise Impossible.unimp "lambda"
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
    | strOfCoreExp (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (strOfCoreExp body) (* backslash *)
    | strOfCoreExp (FUNAPP (e1, e2)) = strOfCoreExp e1 ^ " " ^ strOfCoreExp e2

  fun strOfCoreValue (VCON (v, vals)) = 
          strBuilderOfVconApp strOfCoreValue v vals 
    | strOfCoreValue (LAMBDA (n, e)) = 
      Impossible.impossible 
      "stringifying core lambda- client code must handle this case"

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 
end
