structure VMinusOfP :> sig 

end 
  =
struct 

  structure P = PPlus 
  structure VM = VMFn(Alpha)
  exception Todo of string 


  fun translate (rho: 'a option Env.env) (e : P.exp) = 
    case e of P.NAME n => VM.NAME n 
            | P.VCONAPP (vc, es) => VM.VCONAPP (vc, List.map (translate rho) es)
            | P.FUNAPP (e1, e2)  => VM.FUNAPP (translate e1, translate e2)
            | P.CASE (scrutinee, branches) => 
              let val (pats, rhss) = ListPair.unzip branches 
                  val e' = translate scrutinee 
                  val (alreadyName, name) = (case e' of VM.NAME n => (true, n) | _ => (false, FreshName.freshname ()))
                  (* depends on future invariant of lhs == a name *)
                  (* introduce existentials *)
                  (* bind them *)
                  fun gexpOfPat (P.PNAME n) = VM.NAME n
                    | gexpOfPat (P.CONAPP (n, ps)) = VM.VCONAPP (Core.K n, map gexpOfPat ps)
                  val internal = List.foldl (fn ((pat, rhs), gs) => (VM.EQN (name, (expOfPat pat), VM.ARROWALPHA (translate rhs)))::gs) [] branches
              in  if alreadyName 
                  then VM.IF_FI internal
                  else VM.IF_FI [VM.EXISTS (name, 
                                     VM.ARROWALPHA (VM.IF_FI internal))] 
              end 
 
end
