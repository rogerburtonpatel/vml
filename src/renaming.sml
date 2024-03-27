structure Renaming :> sig 

end 
  =
struct 
  structure P = PPlus
  structure E = Env
  structure C = Core'
  type name = PPlus.name
  type 'a env = 'a Env.env
  infix 6 <+>
  fun rho1 <+> rho2 = Env.<+>
  val freshNameGen = FreshName.freshNameGen
  fun add x v rho = Env.bind (x, v, rho)
  fun fst (x, y) = x
  infix 6 inEnv 
  fun x inEnv rho = Env.binds (rho, x)

  fun patFreeNames (P.PNAME n) = [n]
              | patFreeNames (P.CONAPP (_, ps)) = 
                                  List.concat (List.map patFreeNames ps)
              | patFreeNames (P.WHEN _) = [] 
              | patFreeNames (P.ORPAT (p1, p2)) = 
                          List.concat [patFreeNames p1, patFreeNames p2] 
              | patFreeNames (P.PATGUARD (p, _)) = patFreeNames p 
              | patFreeNames (P.PATSEQ (p1, p2)) =  
                          List.concat [patFreeNames p1, patFreeNames p2] 

(* identity *)
  val rec x = fn x => case x of x => x
  (* renamed *)
  val rec x = fn y => case y of z => y

(* algorithm: 
for binding sites: 
  if not in env, add binding of self to self. 
  if in env, add binding of self to fresh name. 
  how to make the name distinct from all others? 
  start by gathering a set of all names used, and generate distinct. 
for used names, look them up in the environment *)

  fun pplus (renamings : name env) (P.C ce) = 
        (case ce of 
        (* used location - should always have been priorly subjected to a rename. otherwise, error. *)
        C.LITERAL v => (P.C (C.LITERAL v), renamings)
      | C.NAME n => (P.C (C.NAME (Env.find (n, renamings))), renamings)
          (* if n inEnv renamings 
          then (P.C (C.NAME (Env.find (n, renamings))), renamings)
          else let val fresh = freshNameGen ()
               in (P.C (C.NAME fresh), add n fresh renamings) 
               end   *)
      | C.VCONAPP (vc, es)    => 
      (* used locations- rename all *)
        let val es' = map (fst o (pplus renamings)) es
        in (P.C (C.VCONAPP (vc, es')), renamings)
        end 
      | C.LAMBDAEXP (n, body) => 
      (* if n is already in use, 
         rename it and everything in the body with the renaming. *)
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
              of P.PNAME n => 
                  let val fresh = freshNameGen ()
                      val (n', patrenamings') = 
                          (fresh, add n fresh patrenamings)
                  in (P.PNAME fresh, patrenamings')
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
               | P.CONAPP (vc, ps) => Impossible.unimp "tricky"
                (* P.CONAPP (vc, map renamePat ps) *)

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
