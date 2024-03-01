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

  val eqval           : 'a core_value * 'a core_value -> bool
  val boolOfCoreValue : 'a core_value -> bool 
  val expString    : core_exp -> string 
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
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  fun boolOfCoreValue (VCON (FALSE, [])) = false
    | boolOfCoreValue _                  = true


                     

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

  fun expString (NAME n) = n
    | expString (VCONAPP (n, es)) = 
     strBuilderOfVconApp expString n es 
    | expString (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
    | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2

  fun strOfCoreValue (VCON (v, vals)) = 
          strBuilderOfVconApp strOfCoreValue v vals 
    | strOfCoreValue (LAMBDA (n, e)) = 
      Impossible.impossible 
      "stringifying core lambda- client code must handle this case"

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 
end


signature EXTENDED = sig
  type name = string 
  type vcon  = Core.vcon
    datatype 'exp value = VCON of vcon   * 'exp value list 
                         | LAMBDA of name * 'exp
  type 'exp extension  (* all the expressions we don't care about *)

  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp extension  (* everything else *)

  val expString    : exp -> string 

end

functor MkExtended(type 'a extension) :> EXTENDED where type 'a extension = 'a extension
  =
struct
  type name = string 
  type vcon = Core.vcon
  type 'a extension = 'a extension
  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp
  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp extension  (* everything else *)


  fun strBuilderOfVconApp f vc args = 
  let val name = 
      (case vc 
        of Core.K n => n 
         | Core.TRUE => "true" 
         | Core.FALSE => "false")
      val vcss = foldr (fn (v, acc) => " " ^ f v ^ acc) "" args
        in name ^ vcss
    end 

  fun expString (NAME n) = n
  | expString (VCONAPP (n, es)) = 
    strBuilderOfVconApp expString n es 
  | expString (LAMBDAEXP (n, body)) = 
      StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
  | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
  | expString (E e) = Impossible.unimp "print an extended expression with a helper"

end



structure NewPPlus =
  MkExtended(type name = string
         datatype pat = NAME of name | APP of Core.vcon * pat list
         datatype 'a extension = CASE of 'a * (pat * 'a) list)


