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
               | APP of exp * exp 
               | ONE of exp 
               | ALL of exp 
               | ESEQ of exp list 
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
               | APP of exp * exp 
               | ONE of exp 
               | ALL of exp 
               | ESEQ of exp list 
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
    | unparse (APP (e1, e2)) =  unparse e1 ^ " " ^ unparse e2 
    | unparse (ONE e) = "one {" ^ unparse e ^ "}"
    | unparse (ALL e) = "all {" ^ unparse e ^ "}"
    | unparse (ESEQ es) = stringSeq unparse es
  and unparseVal v = 
      (case v 
           of INT i => Int.toString i
            | PRIMOP ADD => "add"
            | PRIMOP GT  =>  "g" 
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
            | APP (VAL (PRIMOP ADD), ESEQ [e1, e2]) => 
              (case (eval rho e1, eval rho e2)
                of (INT i1, INT i2) => INT (i1 + i2) | _ => raise Stuck )
            | APP (VAL (PRIMOP ADD), ex) => 
            let val _ = print ("could not add " ^ (unparse ex) ^ "\n")
            in raise Stuck 
            end 
            | APP (VAL (PRIMOP GT), ESEQ [e1, e2]) => 
            (case (eval rho e1, eval rho e2)
                of (INT i1, INT i2) => if i1 > i2 
                                       then INT i1 
                                       else raise Fail | _ => raise Stuck ) 
            | APP (VAL (PRIMOP GT), _) => raise Stuck
            | APP (VAL (lam as LAMBDA (n, body)), e') => 
                eval (Env.bind (n, SOME (eval rho e'), rho)) body
            | APP _ => raise Stuck 
            | ONE (CHOICE (e1, e2)) => (eval rho e1 handle Fail => eval rho e2)
            | ONE e' => eval rho e'
            | ALL (CHOICE (e1, e2)) => SEQ [eval rho e1, eval rho e2]
            | ALL e'  => eval rho e'
            | ESEQ es => SEQ (map (eval rho) es)

(* E x y. x = (7 | 22); y = (31 | 5); PAIR (x, y) *)
val choiceexp = EXISTS ("x", 
                EXISTS ("y", 
                EXPSEQ (NAMEASSIGN ("x", 
                        CHOICE (VAL (INT 7), VAL (INT 22))), 
                 EXPSEQ (NAMEASSIGN ("y", 
                        CHOICE (VAL (INT 31), VAL (INT 5))), 
                ESEQ [NAME "x", NAME "y"]))))

val failexp = EXISTS ("x", 
              EXPSEQ (NAMEASSIGN ("x", FAIL), 
              VAL (INT 33)))

val lamexp = EXISTS ("y", 
              EXPSEQ (NAMEASSIGN ("y", APP (VAL (PRIMOP ADD), ESEQ [VAL (INT 3), VAL (INT 4)])),
              APP (VAL (LAMBDA ("x", APP (VAL (PRIMOP ADD), ESEQ [NAME "x", VAL (INT 1)]))), 
              NAME "y")))


(* val _ = (eval Env.empty failexp handle Fail => (print "fail\n" ; INT 0))
val _ = print ((unparse choiceexp) ^ "\n")
val _ = print ((unparseVal (eval Env.empty choiceexp)) ^ "\n")
val _ = print ((unparse lamexp) ^ "\n")
val _ = print ((unparseVal (eval Env.empty lamexp)) ^ "\n") *)
end 