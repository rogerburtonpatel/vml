structure DofVMinus :> sig 


end 
  = 
struct 

  structure D = DecisionTree
  structure VM = VMFn(Alpha)
  (* fun translate  *)
  (* need to sort first. *)

  exception Todo of string 

  val counter = ref 0

  fun fresh_name () = (counter := !counter + 1 ; "__x" ^ Int.toString (!counter))

  fun translateExp (e : 'a VM.exp) = let val (e' : D.exp) = raise Todo "translate exps" in e' end 

  fun treeOfGuardedExp (VM.ARROWALPHA e)   = D.MATCH (translateExp e)
    | treeOfGuardedExp (VM.EXISTS (n, g')) = treeOfGuardedExp g'
    | treeOfGuardedExp (VM.EXPSEQ (e, g')) = 
        let val freshname = fresh_name () 
            val (fail : D.exp) = raise Todo "failure"
        in 
        D.LET (freshname, translateExp e, D.IF (freshname, treeOfGuardedExp g', D.MATCH fail))
        end 
    | treeOfGuardedExp (VM.EQN (n, e, g')) = treeOfGuardedExp g'
end 