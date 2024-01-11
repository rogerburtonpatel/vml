structure VMinusOfP :> sig 

end 
  =
struct 

  structure P = PPlus 
  structure VM = VMFn(Alpha)
  exception Todo of string 


  fun translate (expr : P.exp) = 
    let fun translate' (rho: string Set.set) (e : P.exp) = 
      case e of P.NAME n => VM.NAME n 
              | P.VCONAPP (vc, es) => VM.VCONAPP (vc, List.map (translate' rho) es)
              | P.FUNAPP (e1, e2)  => VM.FUNAPP (raise Todo "function must bind names from p to vminus")
              | P.CASE (scrutinee, branches) => 
                let val e' = translate scrutinee 
                        val _ = print ((VM.expString e') ^ "\n")
                    val (pats, rhss) = ListPair.unzip branches 
                    val (alreadyName, name) = 
                          (case e' of VM.NAME n => (true, n) 
                                    | _ => (false, FreshName.freshname ()))
                    (* simply make a pattern look like an equation *)
                    fun translatePat (P.PNAME n)        = VM.NAME n 
                      | translatePat (P.CONAPP (n, ps)) = 
                                      VM.VCONAPP (Core.K n, map translatePat ps)
                    (* find unbound names in a pattern *)
                    fun patFreeNames (P.PNAME n) = 
                                         if Set.member (n, rho) then [n] else []
                      | patFreeNames (P.CONAPP (vc, ps)) = 
                                         List.concat (List.map patFreeNames ps)
                    (* introduce them as necessary with existentials *)
                    (* bind them - ns comes from patFreeNames *)
                    fun introduceExistentials ns g = List.foldl VM.EXISTS g ns
                    (* todo check if fold direction is right *)
                    (* depends on future invariant of lhs == a name *)
                    fun gexpOfPat p e' = 
                      let val freenames = patFreeNames p
                          val rho' = Set.union' [Set.fromList freenames, rho]
                          val lhs' = translatePat p
                          val rhs' = VM.ARROWALPHA (translate' rho e')
                          val bind = VM.EQN (name, lhs', rhs')
                      in introduceExistentials freenames bind
                      end 
                    val internal =   (List.foldr 
                                     (fn ((pat, rhs), gs) => 
                                         (gexpOfPat pat rhs)::gs) 
                                    [] branches)
                in  if alreadyName 
                    then VM.IF_FI internal
                    else VM.IF_FI [VM.EXISTS (name, VM.EQN (name, e', 
                                   VM.ARROWALPHA (VM.IF_FI internal)))] 
                end 
    in translate' Set.empty expr 
    end 

  val pempty = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [])
  (* val _ = print ((VM.expString (translate pempty)) ^ "\n") *)
  val psome = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [
    (P.CONAPP ("cons", [P.PNAME "x", P.PNAME "xs"]), P.NAME "x")
  ])
  val _ = print ((VM.expString (translate psome)) ^ "\n")


end
