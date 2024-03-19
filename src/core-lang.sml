structure Core :> sig 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'exp core_value = VCON of vcon   * 'exp core_value list 
                           | LAMBDA of name * 'exp

  exception NameNotBound of name 
  exception BadFunApp of string 

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  val eqval               : 'a core_value * 'a core_value -> bool
  val boolOfCoreValue     : 'a core_value -> bool 
  val expString           : core_exp -> string 
  val valString      : 'a core_value -> string 
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
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  fun boolOfCoreValue (VCON (FALSE, [])) = false
    | boolOfCoreValue _                  = true


                     

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

  fun expString (NAME n) = n
    | expString (VCONAPP (n, es)) = 
     vconAppStr expString n es 
    | expString (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
    | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2

  fun valString (VCON (v, vals)) = 
          vconAppStr valString v vals 
    | valString (LAMBDA (n, e)) = 
      Impossible.impossible 
      "stringifying core lambda- client code must handle this case"

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 
end

structure Core' :> sig
    type name = string 
    datatype vcon = K of string
    datatype 'a t = NAME of name 
                  | VCONAPP of vcon * 'a list
                  | LAMBDAEXP of name * 'a 
                  | FUNAPP of 'a * 'a 
  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp

  val map                 : ('a -> 'b) -> 'a t -> 'b t
  
  val eqval               : 'a value * 'a value -> bool

  val expString           : ('a -> string) -> 'a t -> string
  val valString           : ('a -> string) -> 'a value -> string 
  val vconAppStr : ('a -> string) -> vcon -> 'a list -> string

  end 

  = struct
    type name = string 
    datatype vcon = K of string
    datatype 'a t = NAME of name 
                  | VCONAPP of vcon * 'a list
                  | LAMBDAEXP of name * 'a 
                  | FUNAPP of 'a * 'a 

  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp

  fun map (f : ('a -> 'b)) t = 
      case t of NAME n       => NAME n  
          | VCONAPP (vc, ts) => VCONAPP (vc, List.map f ts)
          | LAMBDAEXP (n, t) => LAMBDAEXP (n, f t)
          | FUNAPP (t1, t2)  => FUNAPP (f t1, f t2)

  fun eqval (VCON (v1, vs), VCON (v2, vs')) = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 

  fun vconAppStr f (K vc) args = 
      String.concatWith " " (vc::(List.map f args))

  fun expString f (NAME n)              = n
    | expString f (VCONAPP (vc, es))     = vconAppStr f vc es 
    | expString f (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
    | expString f (FUNAPP (e1, e2)) = f e1 ^ " " ^ f e2

  fun valString f (VCON (vc, vals))   = 
          vconAppStr (valString f) vc vals 
    | valString f (LAMBDA (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
    
end