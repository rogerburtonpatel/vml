signature DECISION_TREE = sig
  type name = Core.name 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of 'e   * ('e, 'a) tree * ('e, 'a) tree 
              | TRY_LET of name  * 'e * ('e, 'a) tree * ('e, 'a) tree option
              | CMP of name  * 'e * ('e, 'a) tree * ('e, 'a) tree * ('e, 'a) tree 
              | EXTRACT of name * name list * ('e, 'a) tree 
              | FAIL

  datatype exp = C of exp Core.t 
               | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  val emitTree  : (exp, exp) tree -> string
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
              | IF of 'e   * ('e, 'a) tree * ('e, 'a) tree 
              | TRY_LET of name  * 'e * ('e, 'a) tree * ('e, 'a) tree option
              | CMP of name  * 'e * ('e, 'a) tree * ('e, 'a) tree * ('e, 'a) tree 
              | EXTRACT of name * name list * ('e, 'a) tree 
              | FAIL

  datatype exp = C of exp Core.t 
             | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  fun br' input = "(" ^ input ^ ")"

  structure C = Core 


  fun expString (C ce) = 
  (case ce of C.FUNAPP (e1, e2)  => 
                          maybeparenthesize e1 ^ " " ^ maybeparenthesize e2
            | C.VCONAPP (vc, es) => C.vconAppStr maybeparenthesize vc es
            | _ => C.expString expString ce)
    | expString   (I tree) = emitTree tree
  and valString v = C.valString expString v
  and maybeparenthesize (C e) = C.maybeparenthesize expString e
    | maybeparenthesize other = br' (expString other)
  and emitTree t = 
    let fun emitCase [] default = Impossible.impossible "no patterns to match on"
           | emitCase (x::xs) default = 
           let fun emitBranch ((Core.K vc, i), tr) = "(" ^ vc ^ ", " ^ Int.toString i ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => "| " ^ emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "| _ => " ^ emitTree' (valOf default) else "")
        end 
    and emitTree' (MATCH a) = expString a
          | emitTree' (TEST (n, pats, default)) = "test " ^ n ^ ":\n " ^ emitCase pats default
          | emitTree' (IF (e, left, right)) = "if " ^ expString e ^ " then " ^ emitTree' left ^ " else " ^ emitTree' right
          | emitTree' (TRY_LET (n, e, t1, NONE)) = "let " ^ n ^ " = " ^ expString e ^ " in " ^ emitTree' t1 
          | emitTree' (TRY_LET (n, e, t1, SOME t2)) = "try let " ^ n ^ " = " ^ expString e ^ " in " ^ emitTree' t1 ^ ", \n otherwise \n" ^ emitTree' t2
          | emitTree' (CMP (n, e, t1, t2, t3)) = n ^ " = " ^ expString e ^ "? \n ->" ^ emitTree' t1 ^ "\n -> " ^ emitTree' t2 ^ "\n -> " ^ emitTree' t3
          | emitTree' (EXTRACT (n, [], t)) = emitTree' t
          | emitTree' (EXTRACT (n, ns, t)) = "extract " ^ n ^ " into " ^ String.concatWith ", " ns ^ " in " ^ emitTree' t
          | emitTree' FAIL = "fail"
    in emitTree' t ^ "\n"
    end 

  (* and emitTree f_a f_e t = 
    let fun emitCase [] default = Impossible.impossible "no patterns to match on"
           | emitCase (x::xs) default = 
           let fun emitBranch ((Core.K vc, i), tr) = "(" ^ vc ^ ", " ^ Int.toString i ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => "| " ^ emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "| _ => " ^ emitTree' (valOf default) else "")
        end 
    and emitTree' (MATCH a) = f_a a
          | emitTree' (TEST (n, pats, default)) = "test " ^ n ^ ":\n " ^ emitCase pats default
          | emitTree' (IF (e, left, right)) = "if " ^ f_e e ^ " then " ^ emitTree' left ^ " else " ^ emitTree' right
          | emitTree' (TRY_LET (n, e, t1, NONE)) = "let " ^ n ^ " = " ^ f_e e ^ " in " ^ emitTree' t1 
          | emitTree' (TRY_LET (n, e, t1, SOME t2)) = "try let " ^ n ^ " = " ^ f_e e ^ " in " ^ emitTree' t1 ^ ", \n otherwise \n" ^ emitTree' t2
          | emitTree' (CMP (n, e, t1, t2, t3)) = n ^ " = " ^ f_e e ^ "? \n ->" ^ emitTree' t1 ^ "\n -> " ^ emitTree' t2 ^ "\n -> " ^ emitTree' t3
          | emitTree' FAIL = "fail"
    in emitTree' t ^ "\n"
    end  *)


  fun mlconstring argstring (C.K vc, args) = 
    "CON (" ^ vc ^  "[" ^ String.concatWith "," (map argstring args) ^ "]"

  (* fun expString (C ce) = 
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


  fun defString (DEF (n, e)) = "val rec " ^ n ^ " = " ^ expString e *)

    

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

    (* val testTree = TEST ("r1", [((C.K "C1", 2), MATCH "foo"), ((C.K "C1", 2), LET ("x", "C1/2", IF ("x", MATCH "foo", MATCH "bar")))], SOME (MATCH "Foo")) 
    val () = print (emitTree id id testTree) *)
  fun progString (ds : def list) = 
     (* "exception NoMatch \n" 
    ^ "type vcon = string \n"
    ^ "datatype data = CON of vcon * data list \n"
    ^  *)
    String.concatWith "\n" (map defString ds)
    

  exception Fail of string 

  fun println s = print (s ^ "\n")

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, v, rho)
  fun eqval (e1, e2) = Core.eqval (e1, e2)


  fun find_or_die n rho = 
        if Env.binds (rho, n) then lookup n rho else raise C.NameNotBound n

  exception Unsolvable

  fun eval rho (C ce) = 
    (case ce of
      C.LITERAL v => v
    | C.NAME n    => find_or_die n rho
    | C.VCONAPP (vc, es)    => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, body)
    | C.FUNAPP (C (C.NAME "print"), param)  => 
    (* dirty trick to print values *)
                    ( println (C.valString expString (eval rho param)) 
                          ; C.VCON (C.K "unit", [])
                    ) 
    | C.FUNAPP (fe, param)  => 
              (case eval rho fe 
                of C.LAMBDA (n, b) => 
                  let val arg  = eval rho param
                      val rho' = bind n arg rho
                    in 
                     eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
    | eval rho (I tree) = evalTree rho tree

    and evalTree rho tree = 
      case tree of MATCH e => eval rho e
        | TEST (x, [], NONE) => 
              raise Fail ("No match found while testing \"" ^ x ^ "\"")
        | TEST (x, [], SOME default) => evalTree rho default
        | TEST (x, (vc_arity, t)::options, default) => 
          (case lookup x rho 
            of C.VCON (vc, vs) => 
              let val me = (vc, length vs)
              in if me = vc_arity 
                 then evalTree rho t 
                 else evalTree rho (TEST (x, options, default))
              end
             | _ => Impossible.impossible "cannot test non-vcon")
        | IF (e, t1, t2) => 
          ((eval rho e 
            handle Fail _ => evalTree rho t2)
          ; evalTree rho t1)
        | TRY_LET (n, e, t1, NONE) => 
          let val v = eval rho e 
          in evalTree (bind n v rho) t1
          end 
        | TRY_LET (n, e, t1, SOME t2) => 
          (let val v = eval rho e 
          in evalTree (bind n v rho) t1
          end 
            handle Fail _ => evalTree rho t2)
        | CMP (n, e, t1, t2, t3) => 
            (let val v1 = lookup n rho 
                 val v2 = eval rho e
             in if eqval (v1, v2) then evalTree rho t1 else evalTree rho t2
             end 
            handle Fail _ => evalTree rho t3)
        | EXTRACT (n, ns, t) => 
          (case lookup n rho 
            of C.VCON (_, vs) => 
              let val rho' = ListPair.foldlEq Env.bind rho (ns, vs)
              in evalTree rho' t
              end 
             | _ => Impossible.impossible "extracting a non-vcon- bug in MC")
        | FAIL => raise Fail "reached a fail node in a decision tree"


end
