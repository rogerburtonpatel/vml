signature DECISION_TREE = sig
  type name = Core.name 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * name list 

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | LET_UNLESS of name  * 'e * ('e, 'a) tree * ('e, 'a) tree option
              | IF_THEN_ELSE of name * name * ('e, 'a) tree * ('e, 'a) tree
              | EXISTS of name * ('e, 'a) tree
              | FAIL

  datatype exp = C of exp Core.t 
               | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  val emitTree  : (exp, exp) tree -> string
  val expString : exp -> string

  val progString : def list -> string

  type value = exp Core.value

  val eval : value option Env.env -> exp -> value  

end

structure D :> DECISION_TREE 
  = 
struct
  type name = Core.name 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * name list

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | LET_UNLESS of name  * 'e * ('e, 'a) tree * ('e, 'a) tree option
              | IF_THEN_ELSE of name  * name * ('e, 'a) tree * ('e, 'a) tree
              | EXISTS of name * ('e, 'a) tree
              | FAIL

  datatype exp = C of exp Core.t 
             | I of (exp, exp) tree

  datatype def = DEF of name * exp 

  type value = exp Core.value

  fun br' input = "(" ^ input ^ ")"

  structure C = Core 
  val member = ListUtil.member
  infix 6 <+>
  val op <+> = Env.<+>


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
    let fun emitBranches [] default = Impossible.impossible "no patterns to match on"
           | emitBranches (x::xs) default = 
           let fun emitBranch ((Core.K vc, ys), tr) = "(" ^ vc ^ ", " ^ String.concatWith "," ys ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "else " ^ emitTree' (valOf default) else "")
        end 
    and emitTree'     (MATCH a) = expString a
          | emitTree' (TEST (n, branches, default)) = "test " ^ n ^ "\n " ^ emitBranches branches default
          | emitTree' (LET_UNLESS (n, e, t1, NONE)) = "let " ^ n ^ " = " ^ expString e ^ " in " ^ emitTree' t1 
          | emitTree' (LET_UNLESS (n, e, t1, SOME t2)) = "let " ^ n ^ " = " ^ expString e ^ " in " ^ emitTree' t1 ^ "\n unless fail => " ^ emitTree' t2
          | emitTree' (IF_THEN_ELSE (x, y, t1, t2)) = "if " ^ x ^ " = " ^ y ^ "\n then " ^ emitTree' t1 ^ "\n else " ^ emitTree' t2
          | emitTree' (EXISTS (n, t)) = "E " ^ n ^ ". " ^ emitTree' t
          | emitTree' FAIL = "fail"
    in emitTree' t ^ "\n"
    end 


  fun mlconstring argstring (C.K vc, args) = 
    "CON (" ^ vc ^  "[" ^ String.concatWith "," (map argstring args) ^ "]"

  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

    (* val testTree = TEST ("r1", [((C.K "C1", 2), MATCH "foo"), ((C.K "C1", 2), LET ("x", "C1/2", IF ("x", MATCH "foo", MATCH "bar")))], SOME (MATCH "Foo")) 
    val () = print (emitTree id id testTree) *)
  fun progString (ds : def list) = 
    String.concatWith "\n" (map defString ds)
    

  exception Fail of string 

  fun uncurry f (x, y) = f x y
  fun uncurry3 f (x, y, z) = f x y z
  fun println s = print (s ^ "\n")

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, v, rho)
  fun eqval (e1, e2) = Core.eqval (e1, e2)

  type lvar_env = value option Env.env

  infix 6 <+>
  val op <+> = Env.<+>

  infix 9 binds
  fun rho binds n = Env.binds (rho, n)

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, SOME v, rho)
  fun introduce x rho = Env.bind (x, NONE, rho)
  fun lookupv x rho = valOf (lookup x rho)
  val empty = Env.empty

  infix 9 exists_in
  fun n exists_in (rho: lvar_env) = 
    rho binds n andalso isSome (lookup n rho)

  infix 9 unknown_in 
  fun n unknown_in (rho: lvar_env) = 
    rho binds n andalso not (isSome (lookup n rho))
  fun find_or_die n rho = 
      if n exists_in rho then lookupv n rho else raise C.NameNotBound n

  fun check_let_name_bot n e rho = 
  if not (rho binds n)
          then raise Core.NameNotBound ("name " ^ n ^ " in \"let " ^ n ^ " = " ^ expString e ^"\" not bound")
          else if not (n unknown_in rho)
          then raise Core.NameNotBound ("name " ^ n ^ " in \"let " ^ n ^ " = " ^ expString e 
                                        ^"\" bound to prior value " ^ C.valString expString (find_or_die n rho))
          else ()

  exception Unsolvable

  val predefs = ["print"]

  fun embed rho = Env.map SOME rho
  fun project rho = Env.mapPartial (fn x => x) rho

  fun captureVal rho (C.LAMBDA (n, captured, body)) = 
        C.LAMBDA (n, project (rho <+> embed captured), body)
    | captureVal rho (C.VCON (vc, vs)) = C.VCON (vc, map (captureVal rho) vs)

  fun eval rho (C ce) = 
    (case ce of
      (* C.LITERAL (C.LAMBDA (n, captured, body)) =>  *)
      C.LITERAL v => captureVal rho v
    | C.NAME n    => find_or_die n rho
    | C.VCONAPP (vc, es)    => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, project rho, body)
    | C.FUNAPP (C (C.NAME n), arg)  => 
      if member n predefs 
      then runpredef n (rho, arg) 
      else let val v = eval rho (C (C.NAME n))
            in eval rho (C (C.FUNAPP (C (C.LITERAL v), arg)))
            end 
    | C.FUNAPP (fe, arg) => 
              (case eval rho fe 
                of C.LAMBDA (n, captured, b) => 
                    let val v_arg = eval rho arg
                        val rho' = (bind n v_arg rho <+> embed captured)
                    in eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
    | eval rho (I tree) = evalTree rho tree

    and evalTree rho tree = 
      case tree of MATCH e => eval rho e
        | TEST (x, [], NONE) => 
              raise Fail ("No match found while testing \"" ^ x ^ "\"")
        | TEST (x, [], SOME default) => evalTree rho default
        | TEST (x, ((k, ys), t)::options, default) => 
          (case find_or_die x rho 
            of C.VCON (vc, vs) => 
              let val me   = (vc, length vs)
                  val them = (k, length ys)
              in if me = them
                 then evalTree (ListPair.foldl (uncurry3 bind) rho (ys, vs)) t 
                 else evalTree rho (TEST (x, options, default))
              end
             | _ => Impossible.impossible "cannot test non-vcon")
        | LET_UNLESS (n, e, t1, NONE) => 
            (check_let_name_bot n e rho ; 
            let val v = eval rho e 
            in evalTree (bind n v rho) t1
            end)
        | LET_UNLESS (n, e, t1, SOME t2) => 
          (check_let_name_bot n e rho ; 
          let val v = eval rho e 
          in evalTree (bind n v rho) t1
          end 
            handle Fail _ => evalTree rho t2)
        | IF_THEN_ELSE (x, y, t1, t2) => 
            let val v1 = find_or_die x rho 
                val v2 = find_or_die y rho
             in if eqval (v1, v2) then evalTree rho t1 else evalTree rho t2
             end
        | EXISTS (n, t) => evalTree (introduce n rho) t 
        | FAIL => raise Fail "reached a fail node in a decision tree"

  and runpredef which (rho, arg) = 
    case which of 
      "print" => ( println (C.valString expString (eval rho arg)) 
                  ; C.VCON (C.K "unit", [])
                 )
      | _ => Impossible.impossible "runtime bug: running non-predef function"


end
