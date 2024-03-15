structure Guard :> sig 

    type name = string 
    datatype logical_variable = LV of name 

    datatype exp = INT of int | NAME of name | IF_FI of guarded_exp list
    and guarded_exp = ARROWEXP of exp 
                    | EXPSEQ of exp * guarded_exp 
                    | EXISTS of logical_variable * guarded_exp
                    | EQN    of logical_variable * exp * guarded_exp

    type lvar_env = exp option Env.env

    val gexpString : guarded_exp -> string 
    val expString  : exp -> string 
    val optExpString : exp option -> string 

    exception NameNotBound of name 
    exception SortFailure of string
    exception Cycle of string

    datatype var_status = NOT_BOUND | NOT_KNOWN | VAR of name

end 
    = 
struct 

    type name = string 
    datatype logical_variable = LV of name 
    exception Todo of string 



    datatype exp = INT of int | NAME of name | IF_FI of guarded_exp list
    and guarded_exp = ARROWEXP of exp 
                    | EXPSEQ of exp * guarded_exp 
                    | EXISTS of logical_variable * guarded_exp
                    | EQN    of logical_variable * exp * guarded_exp


    exception NameNotBound of name 
    exception SortFailure of string
    exception Cycle of string

    type lvar_env = exp option Env.env

    datatype var_status = NOT_BOUND | NOT_KNOWN | VAR of name

    fun binds (rho: lvar_env) n = Env.binds (rho, n)

    fun gexpString (ARROWEXP e) = expString e 
    | gexpString (EXPSEQ (e, ge)) = expString e ^ "; " ^ gexpString ge
    | gexpString (EXISTS (LV x, ge)) = "∃" ^ x ^ ". " ^ gexpString ge
    | gexpString (EQN (LV x, e, ge)) = 
                    x ^ " = " ^ expString e ^ "; " ^ gexpString ge 
    and expString (INT i)  = Int.toString i
    | expString (NAME n) = n
    | expString (IF_FI ges) = "if " ^ ListUtil.join gexpString "[]" ges ^ " fi"
    and optExpString (SOME e) = "SOME " ^ expString e 
    | optExpString NONE     = "NONE"


    val exist_unordered       = EXISTS (LV "x", EQN (LV "x", INT 3, EXISTS (LV "y", EQN (LV "y", NAME "x", ARROWEXP (NAME "x")))))
    val exist_unordered_cmplx = EXISTS (LV "x", EQN (LV "x", INT 3, EXISTS (LV "y", EQN (LV "y", NAME "x", EXISTS (LV "z", EQN (LV "z", NAME "x", EXPSEQ (NAME "z", EXISTS (LV "w", EQN (LV "y", NAME "w", EXPSEQ (NAME "z", EXISTS (LV "a", EQN (LV "y", NAME "x", ARROWEXP (NAME "x")))))))))))))

    (* val () = print (gexpString exist_unordered) 
    val () = print ("\nnormalizes to: \n" ^ ((gexpString o (floatExists Env.empty)) exist_unordered) ^ "\n\n") 
    val () = print (gexpString exist_unordered_cmplx) 
    val () = print ("\nnormalizes to: \n" ^ ((gexpString o (floatExists Env.empty)) exist_unordered_cmplx) ^ "\n")  *)

end 