structure Verse :> sig 
  type name = string 
  datatype exp = VAL of value 
               | EXPSEQ of eq * exp 
               | EXISTS of name * exp 
               | FAIL 
               | CHOICE of exp * exp 
               | APP of value * value 
               | ONE of exp 
               | ALL of exp 
  and eq    = EQEXP of exp | ASSIGN of value * exp 
  and value = NAME of name | HNF of hnf 
  and hnf   =    INT of int 
               | PRIMOP of primop 
               | SEQ of value list 
               | LAMBDA of name * exp  
  and primop = ADD of int * int | GT of int * int 
end 
  =
struct 
  type name = string 
  datatype exp = VAL of value 
               | EXPSEQ of eq * exp 
               | EXISTS of name * exp 
               | FAIL 
               | CHOICE of exp * exp 
               | APP of value * value 
               | ONE of exp 
               | ALL of exp 
  and eq    = EQEXP of exp | ASSIGN of value * exp 
  and value = NAME of name | HNF of hnf 
  and hnf   =    INT of int 
               | PRIMOP of primop 
               | SEQ of value list 
               | LAMBDA of name * exp  
  and primop = ADD of int * int | GT of int * int 

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
  
  fun unparse (VAL v) = unparseVal v
    | unparse (EXPSEQ ((EQEXP e), e')) = unparse e ^ "; " ^ unparse e'
    | unparse (EXPSEQ ((ASSIGN (v, e)), e')) = unparse e ^ "; " ^ unparse e'
    | unparse (EXISTS (n, e)) = exists ^ n ^ ". " ^ unparse e
    | unparse FAIL = "fail"
    | unparse (CHOICE (e1, e2)) = unparse e1 ^ " | " ^ unparse e2
    | unparse (APP (v1, v2)) =  unparseVal v1 ^ " " ^ unparseVal v2 
    | unparse (ONE e) = "one {" ^ unparse e ^ "}"
    | unparse (ALL e) = "all {" ^ unparse e ^ "}"
  and unparseVal v = 
      (case v 
        of NAME n => n
        | HNF h   => 
          (case h 
            of INT i => Int.toString i
            | PRIMOP (ADD (i1, i2)) => "add " ^ stringSeq Int.toString [i1, i2]
            | PRIMOP (GT (i1, i2))  =>  "g "  ^ stringSeq Int.toString [i1, i2]
            | SEQ vs => stringSeq unparseVal vs
            | LAMBDA (n, body) => lam ^ n ^ ". " ^ unparse body))

end
