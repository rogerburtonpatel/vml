structure VMofPP :> sig

  val translate : PPlus.exp -> VMinus.exp
  val def : PPlus.def -> VMinus.def

end 
 = 
struct

  structure P = PPlus
  structure V = VMinus
  structure C = Core

  (* utilities *)

  fun uncurry f (x, y) = f x y
  fun nub xs = Set.elems (Set.fromList xs)

  (* translation and friends *)

  fun translate e = 
    let 
      val freshNameGen = FreshName.freshNameGen
      
      fun translate' (P.C ce) = V.C (Core.map translate' ce)
        | translate' (P.I (P.CASE (scrutinee, branches))) = 
          let 
            val e'           = translate scrutinee
            val (pats, rhss) = ListPair.unzip branches 
            val (scrutinee_already_a_name, name) = 
                  (case e' of V.C (C.NAME n) => (true, n) 
                            | _ => (false, freshNameGen ()))
            val ns_gs    = map (guardofPatWith name) pats
            val uniqs    = map (fn (ns, gs) => (nub ns, gs)) ns_gs
            val rhss'    = map translate rhss
            val options  = ListPair.map (fn ((ns, gs), rhs) => (ns, (gs, rhs))) 
                                        (uniqs, rhss')
            val internal = V.IF_FI options
            val final    =
              if scrutinee_already_a_name 
              then internal
              else V.IF_FI [([name], ([V.EQN (name, e')], V.I internal))]
        in V.I final
        end
(* get all pattern names, introduce them all at the top, 
   then translate each pattern accordingly: (pattern, name) goes to equation. 
   nesting preserved. *)
      and guardofPatWith n (p : P.exp P.pattern) = 
        let 
          val _ = guardofPatWith 
            : P.name -> P.exp P.pattern -> V.name list * V.exp V.guard list
          fun coreEq (n, ce) = V.EQN (n, V.C ce)
          fun translateTwo f p1 p2 = 
              let val (names1, guards1) = guardofPatWith n p1 
                  val (names2, guards2) = guardofPatWith n p2
              in (names1 @ names2, f (guards1, guards2))
              end 
          val (local_names, local_guards) = 
            case p of P.PNAME n'   => ([n'], 
                                  (* prune duplicate bindings *)
                                  [coreEq (n, C.NAME n')])
              | P.WILDCARD             => ([], [])
              | P.WHEN e             => ([], [V.CONDITION (translate e)])
              | P.CONAPP (vc, ps) => 
                  (* introduce one fresh per ps  *)
                  let val fresh_names = FreshName.genOfList freshNameGen ps
                      val ns_gs = ListPair.map (uncurry guardofPatWith) 
                                  (fresh_names, ps)
                      val (names, guards) = ListPair.unzip ns_gs
                      val embedded_names  = map (V.C o C.NAME) fresh_names
                      val vconConstraint  = 
                          coreEq (n, C.VCONAPP (vc, embedded_names))
                  in (* final form is n = vc (n1 ... nm); 
                        guardofPatWith n1 p1; ...; guardofPatWith nm pm *)
                    (List.concat names @ fresh_names, 
                      vconConstraint::List.concat guards)
                  end
              | P.ORPAT (p1, p2)   => 
                      translateTwo (fn gs => [V.CHOICE gs]) p1 p2
              | P.PATGUARD (p', e) => 
                let val n' = (case p' of (P.PNAME n_) => n_
                                      | _ => freshNameGen ())
                    val (names, guards) = guardofPatWith n' p'
                in (n'::names, V.EQN (n', translate e)::guards)
                end
              | P.PATSEQ (p1, p2)  => translateTwo (op @) p1 p2
        in (local_names, local_guards)
        end
    in translate' e 
    end 

  val _ = translate : PPlus.exp -> VMinus.exp

  fun def (P.DEF (n, e)) = V.DEF (n, translate e)

end