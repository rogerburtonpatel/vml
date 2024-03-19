structure FinalD :> sig
  type name = Core'.name 
  type vcon = Core'.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype 'e multi = MULTI of 'e list

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of name   * ('e, 'a) tree * ('e, 'a) tree 
              | LET of name  * 'e * ('e, 'a) tree 

  datatype exp = C of exp Core'.t 
             | I of (exp, exp multi) tree

  val emitTree  : ('a -> string) -> ('b -> string) -> ('b, 'a) tree -> string
  val expString : exp -> string
  
end
  = 
struct
  type name = Core'.name 
  type vcon = Core'.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype 'e multi = MULTI of 'e list

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of name   * ('e, 'a) tree * ('e, 'a) tree 
              | LET of name  * 'e * ('e, 'a) tree 

  datatype exp = C of exp Core'.t 
             | I of (exp, exp multi) tree

  fun multiString (f : 'e -> string) (MULTI es) = String.concat (map f es)

  fun emitTree f_a f_e t = 
    let fun emitCase [] default = Impossible.impossible "no patterns to match on"
           | emitCase (x::xs) default = 
           let fun emitBranch ((vc, i), tr) = "(" ^ vc ^ ", " ^ Int.toString i ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => "| " ^ emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "| _ => " ^ emitTree' (valOf default) else "")
        end 
    and emitTree' (MATCH a) = f_a a
          | emitTree' (TEST (n, pats, default)) = "case " ^ n ^ " of " ^ emitCase pats default
          | emitTree' (IF (n, left, right)) = "if " ^ n ^ " then " ^ emitTree' left ^ " else " ^ emitTree' right
          | emitTree' (LET (n, e, child)) = "let val " ^ n ^ " = " ^ f_e e ^ " in " ^ emitTree' child ^ " end"
    in emitTree' t ^ "\n"
    end 

  fun expString (C ce) = Core'.expString expString ce
    | expString (I tr) = emitTree (multiString expString) expString tr

    fun id x = x 

    (* val testTree = TEST ("r1", [(("C1", 2), MATCH "foo"), (("C1", 2), LET ("x", "C1/2", IF ("x", MATCH "foo", MATCH "bar")))], SOME (MATCH "Foo")) 
    val () = print (emitTree id id testTree) *)


end


signature DECISION_TREE = sig
  type name = string 
  type 'a exp
  type vcon = string 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype data = CON of vcon * data list
                  (* ^ arity *)
  datatype pattern = VCONAPP of data * name option 
  datatype 'a tree =  MATCH of 'a exp
                    | TEST of name * (labeled_constructor * 'a tree) list * 'a tree option
                    | IF of name   * 'a tree * 'a tree 
                    | LET of name  * 'a exp * 'a tree 

  val emitTree : 'a tree -> string 
end

functor DecisionTree(type 'a exp
                    val expString : 'a exp -> string) :>
        DECISION_TREE where type 'a exp = 'a exp
  = 
struct
  type name = string 
  datatype path = PATH of name * int  (* child of a named value constructor *)

  type 'a exp = 'a exp

  fun pathString (PATH (p, i)) = p ^ "." ^ Int.toString i

  type vcon = string 
  type arity = int
  type labeled_constructor = vcon * arity


  datatype data = CON of vcon * data list
  datatype pattern = VCONAPP of data * name option 
  datatype 'a tree =  MATCH of 'a exp
                    | TEST of name * (labeled_constructor * 'a tree) list * 'a tree option
                    | IF of name   * 'a tree * 'a tree 
                    | LET of name  * 'a exp * 'a tree 
  exception Todo of string 

  fun alphaString a = "'a"

  fun emitTree t = 
    let fun emitCase [] default = Impossible.impossible "no patterns to match on"
           | emitCase (x::xs) default = 
           let fun emitBranch ((vc, i), tr) = "(" ^ vc ^ ", " ^ Int.toString i ^ ") => " ^ emitTree' tr ^ "\n"
           val emittedBranches = foldr (fn (b, acc) => "| " ^ emitBranch b ^ acc) "" xs
        in emitBranch x ^ emittedBranches ^ (if isSome default then "| _ => " ^ emitTree' (valOf default) else "")
        end 
    and emitTree' (MATCH a) = alphaString a
          | emitTree' (TEST (n, pats, default)) = "case " ^ n ^ " of " ^ emitCase pats default
          | emitTree' (IF (n, left, right)) = "if " ^ n ^ " then " ^ emitTree' left ^ " else " ^ emitTree' right
          | emitTree' (LET (n, e, child)) = "let val " ^ n ^ " = " ^ expString e ^ " in " ^ emitTree' child
    in emitTree' t ^ "\n"
    end 


    (* val testTree = TEST ("r1", [(("C1", 2), MATCH "foo"), (("C1", 2), MATCH "foo")], SOME (MATCH "Foo")) *)
    (* val () = print (emitTree testTree) *)

end


