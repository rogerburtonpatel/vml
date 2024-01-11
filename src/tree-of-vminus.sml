structure DofVMinus :> sig 


end 
  = 
struct 

  structure D = DecisionTree
  structure VM = VMFn(Alpha)
  exception Todo of string 
  (* fun translate  *)
  (* need to sort first. *)
  fun translateExp (e : 'a VM.exp) = let val (e' : D.exp) = raise Todo "translate exps" in e' end 


  fun treeOfGs [] = D.MATCH (raise Match)
    | treeOfGs (g::gs) = 
    let fun treeOfGuardedExp (VM.ARROWALPHA e)   = D.MATCH (translateExp e)
          | treeOfGuardedExp (VM.EXISTS (n, g')) = treeOfGuardedExp g'
          | treeOfGuardedExp (VM.EXPSEQ (e, g')) = 
              let val freshname = FreshName.freshname () 
                  val (fail : D.exp) = raise Todo "failure"
              in 
              D.LET (freshname, translateExp e, D.IF (freshname, treeOfGuardedExp g', treeOfGs gs))
              end 
          | treeOfGuardedExp (VM.EQN (n, VM.VCONAPP (Core.K vc, es), g')) = 
            let val arity = List.length es 
                val lcon = (vc, arity)
            (* Big todo: match compile es *)
            (* ask if n is a vc/arity. if so, ask if each of es is matched to the corresponding part of vc.
            normalization helps here, and notably functions can appear within patterns.
            how do we normalize? well, we could put everything in a vconapp into a name. then we get something easier. *)
            (* or, we could normalize beforehand so vcons are only applied to names *)
            in D.TEST (n, [(lcon, treeOfGuardedExp g')], SOME (treeOfGs gs))
            end 
    in treeOfGuardedExp g 
    end 
end 