structure Renaming :> sig 

end 
  =
struct 
  structure P = FinalPPlus
  structure E = Env
  structure C = Core'
  type name = FinalPPlus.name
  type 'a env = 'a Env.env
  infix 6 <+>
  fun rho1 <+> rho2 = Env.<+>
  val freshNameGen = FreshName.freshNameGen
  fun add x v rho = Env.bind (x, v, rho)
  fun fst (x, y) = x
  infix 6 inEnv 
  fun x inEnv rho = Env.binds (rho, x)

  fun patFreeNames (P.PATNAME n) = [n]
              | patFreeNames (P.PATCONAPP (_, ps)) = 
                                  List.concat (List.map patFreeNames ps)
              | patFreeNames (P.WHEN _) = [] 
              | patFreeNames (P.ORPAT (p1, p2)) = 
                          List.concat [patFreeNames p1, patFreeNames p2] 
              | patFreeNames (P.PATGUARD (p, _)) = patFreeNames p 
              | patFreeNames (P.PATSEQ (p1, p2)) =  
                          List.concat [patFreeNames p1, patFreeNames p2] 

  fun pplus (renamings : name env) (P.C ce) = 
        (case ce of 
          C.NAME n => 
          if n inEnv renamings 
          then (P.C (C.NAME (Env.find (n, renamings))), renamings)
          else let val fresh = freshNameGen ()
               in (P.C (C.NAME fresh), add n fresh renamings) 
               end  
      | C.VCONAPP (vc, es)    => 
        let val es' = map (fst o (pplus renamings)) es
        in (P.C (C.VCONAPP (vc, es')), renamings)
        end 
      | C.LAMBDAEXP (n, body) => 
            let val fresh = freshNameGen ()
                val (n', renamings') = 
                    (fresh, add n fresh renamings) 
              val body' = fst (pplus renamings' body)
          in (P.C (C.LAMBDAEXP (n', body')), renamings')
          end
      | C.FUNAPP (e1, e2)     => 
        let val e1' = fst (pplus renamings e1)
            val e2' = fst (pplus renamings e2)
            in (P.C (C.FUNAPP (e1', e2')), renamings)
            end)
    | pplus renamings (P.I (P.CASE (scrutinee, branches))) = 
      let val scrutinee' = fst (pplus renamings scrutinee)
          fun renamePat patrenamings p = 
            (* TODO: WRONG. Need to rename across sequences, 
              patseq introduces new bindings *)
            case p 
              of P.PATNAME n => 
                  let val fresh = freshNameGen ()
                      val (n', patrenamings') = 
                          (fresh, add n fresh patrenamings)
                  in (P.PATNAME fresh, patrenamings')
                  end
               | P.WHEN e => 
                  let val (e', _) = (pplus patrenamings e) 
                  in (P.WHEN e', patrenamings)
                  end 
               | P.PATGUARD (p', e) => 
                  let val (e', _)              = pplus patrenamings e 
                      val (p'', patrenamings') = renamePat patrenamings p' 
                  in (P.PATGUARD (p'', e'), patrenamings')
                  end 
               | P.ORPAT (p1, p2) => Impossible.unimp "tricky"
               (* (P.ORPAT (renamePat p1, renamePat p2), renamings) *)
               | P.PATSEQ (p1, p2) => 
                  let val (p1', patrenamings')  = renamePat patrenamings p1
                      val (p2', patrenamings'') = renamePat patrenamings' p2
                  in (P.PATSEQ (p1', p2'), patrenamings'')
                  end 
               | P.PATCONAPP (vc, ps) => Impossible.unimp "tricky"
                (* P.PATCONAPP (vc, map renamePat ps) *)

          fun renameBranches [] = []
            | renameBranches ((pat, e)::rest) =
               let val freenames  = patFreeNames pat
                   val freshnames = FreshName.genOfList freshNameGen freenames
                   val patrenamings = 
                       ListPair.foldl Env.bind renamings (freenames, freshnames) 
                   val pat' = renamePat patrenamings pat 
                in Impossible.unimp""
                end 
          val branches' = renameBranches branches
      in Impossible.unimp ""
      end 

end
