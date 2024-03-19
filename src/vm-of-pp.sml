structure VMofPP :> sig

  val translate : FinalPPlus.exp -> FinalVMinus.exp
  val def : FinalPPlus.def -> FinalVMinus.def

end 
 = 
struct

  structure P = FinalPPlus
  structure V = FinalVMinus
  structure C = Core'


  fun typecheck () = Impossible.unimp "typecheck"
(* get all pattern names 
   introduce them all at the top
   then translate each pattern accordingly: 
   (pattern, name) goes to equation. nesting preserved. 

    *)
  fun uncurry f (x, y) = f x y

  fun patFreeNames (P.PATNAME n) = [n]
            | patFreeNames (P.PATCONAPP (_, ps)) = 
                                List.concat (List.map patFreeNames ps)
            | patFreeNames (P.WHEN _) = [] 
            | patFreeNames (P.ORPAT (p1, p2)) = 
                        List.concat [patFreeNames p1, patFreeNames p2] 
            | patFreeNames (P.PATGUARD (p, _)) = patFreeNames p 
            | patFreeNames (P.PATSEQ (p1, p2)) =  
                        List.concat [patFreeNames p1, patFreeNames p2] 

  fun translate (P.C ce) = V.C (Core'.map translate ce)
    | translate (P.I (P.CASE (scrutinee, branches))) = 
        let val freshNameGen = FreshName.freshNameGenGen ()
            val e'           = translate scrutinee
            val (pats, rhss) = ListPair.unzip branches 
            val (scrutinee_already_a_name, name) = 
                  (case e' of V.C (C.NAME n) => (true, n) 
                            | _ => (false, freshNameGen ()))
            val ns_gs    = map (translatePatWith name) pats
            val rhss'    = map (fn rhs => V.MULTI [translate rhs]) rhss
            val options  = ListPair.map (fn ((ns, gs), rhs) => (ns, gs, rhs)) 
                                        (ns_gs, rhss')
            val internal = V.IF_FI options
            val final    =
             if scrutinee_already_a_name 
             then internal
             else V.IF_FI [([name], [V.EQN (name, e')], V.MULTI [V.I internal])]
        in V.I final
        end
  and translatePatWith n (p : P.exp P.pattern) = 
    let val _ = translatePatWith 
          : P.name -> P.exp P.pattern -> V.name list * V.exp V.guard list
        val freshNameGen = FreshName.freshNameGenGen ()
        val freenames    = patFreeNames p
        fun translateTwo f p1 p2 = 
            let val (names1, guards1) = translatePatWith n p1 
                val (names2, guards2) = translatePatWith n p2
            in (names1 @ names2, f (guards1, guards2))
            end 
        val (local_names, local_guards) = 
          case p of P.PATNAME n'   => ([], [V.EQN (n, V.C (C.NAME n'))])
            | P.WHEN e             => ([], [V.CONDITION (translate e)])
            | P.PATCONAPP (_, ps) => 
            (* introduce one fresh per ps  *)
            let val fresh_names = map (fn _ => freshNameGen ()) ps
                val ns_gs = ListPair.map (uncurry translatePatWith) 
                            (fresh_names, ps)
                val (names, guards) = ListPair.unzip ns_gs
            in (List.concat names @ fresh_names, List.concat guards)
            (* final form is n = vc (n1 ... nm); 
               translatePatWith n1 p1; ...; translatePatWith nm pm *)
            end
            | P.ORPAT (p1, p2)   => translateTwo (fn gs => [V.CHOICE gs]) p1 p2
            | P.PATGUARD (p', e) => 
              let val n'              = freshNameGen ()
                  val (names, guards) = translatePatWith n' p'
              in (n'::names, V.EQN (n, translate e)::guards)
              end
            | P.PATSEQ (p1, p2)  => translateTwo (op @) p1 p2
      in (freenames @ local_names, local_guards)
      end

  val _ = translate : FinalPPlus.exp -> FinalVMinus.exp

  fun def (P.DEF (n, e)) = V.DEF (n, translate e)

end