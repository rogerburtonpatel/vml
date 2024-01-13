structure MicroVerse :> sig 
  (* There are two differences from verse: 
     1. Names are expressions, not values. 
     2. Choice returns its last successful branch or fail. *)

  type name = string 
  datatype exp = VAL of value 
               | NAME of name 
               | EXPSEQ of eq * exp 
               | EXISTS of name * exp 
               | FAIL 
               | CHOICE of exp * exp 
               | APP of value * value 
               | ONE of exp 
               | ALL of exp 
  and eq    = EQEXP of exp | VALASSIGN of value * exp | NAMEASSIGN of name * exp
  and value =    INT of int 
               | PRIMOP of primop 
               | SEQ of value list 
               | LAMBDA of name * exp  
  and primop = ADD | GT 

  exception Stuck

end 
  =
struct 
  type name = string 
  datatype exp = VAL of value 
               | NAME of name 
               | EXPSEQ of eq * exp 
               | EXISTS of name * exp 
               | FAIL 
               | CHOICE of exp * exp 
               | APP of value * value 
               | ONE of exp 
               | ALL of exp 
  and eq    = EQEXP of exp | VALASSIGN of value * exp | NAMEASSIGN of name * exp
  and value =    INT of int 
               | PRIMOP of primop 
               | SEQ of value list 
               | LAMBDA of name * exp  
  and primop = ADD | GT 

  exception Stuck
  exception Fail 

  val la = "⟨"
  val ra = "⟩"
  val lam = "𝜆"
  val exists = "∃"

  fun stringSeq f seq = 
  let fun stringSeq' []  = ""
    | stringSeq' [x] = f x 
    | stringSeq' (x::xs) = f x ^ ", " ^ stringSeq' xs
    in la ^ stringSeq' seq ^ ra
    end 
  
  fun unparse (VAL v)  = unparseVal v
    | unparse (NAME n) = n
    | unparse (EXPSEQ ((EQEXP e), e')) = unparse e ^ "; " ^ unparse e'
    | unparse (EXPSEQ ((VALASSIGN (v, e)), e')) = unparseVal v ^ " = " ^ unparse e ^ "; " ^ unparse e'
    | unparse (EXPSEQ ((NAMEASSIGN (n, e)), e')) = n ^ " = " ^ unparse e ^ "; " ^ unparse e'
    | unparse (EXISTS (n, e)) = exists ^ n ^ ". " ^ unparse e
    | unparse FAIL = "fail"
    | unparse (CHOICE (e1, e2)) = unparse e1 ^ " | " ^ unparse e2
    | unparse (APP (v1, v2)) =  unparseVal v1 ^ " " ^ unparseVal v2 
    | unparse (ONE e) = "one {" ^ unparse e ^ "}"
    | unparse (ALL e) = "all {" ^ unparse e ^ "}"
  and unparseVal v = 
      (case v 
           of INT i => Int.toString i
            | PRIMOP ADD => "add "
            | PRIMOP GT  =>  "g " 
            | SEQ vs => stringSeq unparseVal vs
            | LAMBDA (n, body) => lam ^ n ^ ". " ^ unparse body)

  fun curry   f x y    = f (x, y) 
  fun uncurry f (x, y) = f x y

  fun eqval (INT i1) (INT i2)         = i1 = i2 
    | eqval (PRIMOP ADD) (PRIMOP ADD) = true 
    | eqval (PRIMOP GT) (PRIMOP GT)   = true 
    | eqval (SEQ s1)    (SEQ s2)      = ListPair.all (uncurry eqval) (s1, s2)
    | eqval _ _                       = false 


  (* assumes all is in good order - sorted. next challenge is for unsorted. *)
  fun eval (rho : value option Env.env) e =
    case e of VAL v => v
            | NAME n => if not (isSome (Env.find (n, rho)))
                        then raise Env.NotFound n
                        else valOf (Env.find (n, rho))
            | EXPSEQ (EQEXP e1, e2) => 
              (eval rho e1 ; (* should this fail, the program fails *) 
              eval rho e2)
            | EXPSEQ (NAMEASSIGN (n, e'), e2) => 
              if Env.binds (rho, n)
              then  let val nval  = Env.find (n, rho) 
                        val e'val = eval rho e'
                    in if isSome nval andalso not (eqval (valOf nval) e'val) 
                       then raise Fail 
                       else eval (Env.bind (n, SOME e'val, rho)) e2
                    end 
              else raise Env.NotFound n
              | EXPSEQ (VALASSIGN (v, e'), e2) => 
                let val e'val = eval rho e'
                in if not (eqval v e'val) then raise Fail else 
                eval rho e2
                end 
            | EXISTS (n, e') => eval (Env.bind (n, NONE, rho)) e'
            | FAIL => raise Fail 
            | CHOICE (e1, e2) => 
              (eval rho e1 ; (* should this fail, the program fails. we return the last result. *) 
                eval rho e2)
            | APP (PRIMOP ADD, SEQ [INT i1, INT i2]) => INT (i1 + i2)
            | APP (PRIMOP ADD, _) => raise Stuck
            | APP (PRIMOP GT, SEQ [INT i1, INT i2]) =>  if i1 > i2 
                                                        then INT i1 
                                                        else raise Fail
            | APP (PRIMOP GT, _) => raise Stuck
            | APP (LAMBDA (n, body), v) => eval (Env.bind (n, SOME v, rho)) body
            | APP _ => raise Stuck 
            | ONE (CHOICE (e1, e2)) => (eval rho e1 handle Fail => eval rho e2)
            | ONE e' => eval rho e'
            | ALL (CHOICE (e1, e2)) => SEQ [eval rho e1, eval rho e2]
            | ALL e' => eval rho e'
end 