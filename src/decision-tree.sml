signature DECISION_TREE = sig
  type name = Core.name 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of name   * ('e, 'a) tree * ('e, 'a) tree 
              | LET of name  * 'e * ('e, 'a) tree 

  datatype exp = C of exp Core.t 
               | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  val emitTree  : ('a -> string) -> ('b -> string) -> ('b, 'a) tree -> string
  val expString : exp -> string

  val progString : def list -> string
  
end

structure D :> DECISION_TREE 
  = 
struct
  type name = Core.name 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of name   * ('e, 'a) tree * ('e, 'a) tree 
              | LET of name  * 'e * ('e, 'a) tree 

  datatype exp = C of exp Core.t 
             | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  fun emitTree f_a f_e t = 
    let fun emitCase [] default = Impossible.impossible "no patterns to match on"
           | emitCase (x::xs) default = 
           let fun emitBranch ((Core.K vc, i), tr) = "(" ^ vc ^ ", " ^ Int.toString i ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => "| " ^ emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "| _ => " ^ emitTree' (valOf default) else "")
        end 
    and emitTree' (MATCH a) = f_a a
          | emitTree' (TEST (n, pats, default)) = "case " ^ n ^ " of " ^ emitCase pats default
          | emitTree' (IF (n, left, right)) = "if " ^ n ^ " then " ^ emitTree' left ^ " else " ^ emitTree' right
          | emitTree' (LET (n, e, child)) = "let val " ^ n ^ " = " ^ f_e e ^ " in " ^ emitTree' child ^ " end"
    in emitTree' t ^ "\n"
    end 

  fun br' input = "(" ^ input ^ ")"

  structure C = Core 

  fun mlconstring argstring (C.K vc, args) = 
    "CON (" ^ vc ^  "[" ^ String.concatWith "," (map argstring args) ^ "]"

  fun expString (C ce) = 
    (case ce of 
      C.LITERAL v => valString v
    | C.NAME n => n
    | C.VCONAPP conapp => br' (mlconstring expString conapp)
    | C.LAMBDAEXP (n, body) => br' ("fn " ^ n ^ " => " ^ expString body)
    | C.FUNAPP (e1, e2) => expString e1 ^ " " ^ expString e2)
    | expString (I tr) = emitTree expString expString tr

  and valString v = 
  (case v of C.VCON conapp => 
        br' (mlconstring valString conapp)
          | C.LAMBDA (n, body) => br' ("fn " ^ n ^ " => " ^ expString body))

    fun id x = x 

    (* val testTree = TEST ("r1", [((C.K "C1", 2), MATCH "foo"), ((C.K "C1", 2), LET ("x", "C1/2", IF ("x", MATCH "foo", MATCH "bar")))], SOME (MATCH "Foo")) 
    val () = print (emitTree id id testTree) *)

  fun defString (DEF (n, e)) = "val rec " ^ n ^ " = " ^ expString e

  fun progString (ds : def list) = 
    ( "exception NoMatch \n" 
    ^ "type vcon = string \n"
    ^ "datatype data = CON of vcon * data list \n"
    ^ String.concatWith "\n" (map defString ds))

end
