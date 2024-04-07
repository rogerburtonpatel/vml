structure Core :> sig
    type name = string 
    datatype vcon = K of string
    datatype 'a t = LITERAL of 'a value
                  | NAME of name 
                  | VCONAPP of vcon * 'a list
                  | LAMBDAEXP of name * 'a 
                  | FUNAPP of 'a * 'a 
    and 'exp value = VCON of vcon   * 'exp value list 
                   | LAMBDA of name * 'exp

  exception NameNotBound of name 
  exception BadFunApp of string 
  exception NoMatch
  val map                 : ('a -> 'b) -> 'a t -> 'b t
  
  val eqval               : 'a value * 'a value -> bool

  val expString           : ('a -> string) -> 'a t -> string
  val valString           : ('a -> string) -> 'a value -> string 
  val vconAppStr : ('a -> string) -> vcon -> 'a list -> string

  end 

  = struct
    type name = string 
    datatype vcon = K of string
    datatype 'a t = LITERAL of 'a value
                  | NAME of name 
                  | VCONAPP of vcon * 'a list
                  | LAMBDAEXP of name * 'a 
                  | FUNAPP of 'a * 'a 
    and 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp

  exception NameNotBound of name 
  exception BadFunApp of string 
  exception NoMatch

  fun map (f : ('a -> 'b)) t = 
      case t of 
            LITERAL v => LITERAL (vmap f v)
          | NAME n           => NAME n  
          | VCONAPP (vc, ts) => VCONAPP (vc, List.map f ts)
          | LAMBDAEXP (n, t) => LAMBDAEXP (n, f t)
          | FUNAPP (t1, t2)  => FUNAPP (f t1, f t2) 
  and vmap (f : ('a -> 'b)) v = 
    case v of LAMBDA (n, e) => LAMBDA (n, f e)
            | VCON (vc, vs) => VCON (vc, List.map (vmap f) vs)

  fun eqval (VCON (v1, vs), VCON (v2, vs')) = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"

  fun vconAppStr f (K vc) args = 
      String.concatWith " " (vc::(List.map f args))

  fun vconAppExpStr f (K vc) args = 
      String.concatWith " " (vc::(List.map f args))

  fun expString f (LITERAL v)           = valString f v
    | expString f (NAME n)              = n
    | expString f (VCONAPP (vc, es))    = vconAppStr f vc es 
    | expString f (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
    | expString f (FUNAPP (e1, e2)) = f e1 ^ " " ^ f e2
  and valString f (VCON (vc, vals))   = 
          vconAppStr (valString f) vc vals 
    | valString f (LAMBDA (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
end
