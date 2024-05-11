structure Renaming :> sig 

end 
  =
struct 
  structure P = PPlus
  structure E = Env
  structure C = Core
  type name = PPlus.name
  type 'a env = 'a Env.env
  infix 6 <+>
  fun rho1 <+> rho2 = Env.<+>
  val freshNameGen = FreshName.freshNameGen
  fun fst (x, y) = x
  infix 6 binds 
  fun rho binds x = Env.binds (rho, x)
  fun add x v rho = Env.bind (x, v, rho)
  fun lookup x rho = Env.find (x, rho)
  val empty = Env.empty

  fun patFreeNames (P.PNAME n) = [n]
              | patFreeNames (P.CONAPP (_, ps)) = 
                                  List.concat (List.map patFreeNames ps)
              | patFreeNames (P.WHEN _) = [] 
              | patFreeNames P.WILDCARD = [] 
              | patFreeNames (P.ORPAT (p1, p2)) = 
                          List.concat [patFreeNames p1, patFreeNames p2] 
              | patFreeNames (P.PATGUARD (p, _)) = patFreeNames p 
              | patFreeNames (P.PATSEQ (p1, p2)) =  
                          List.concat [patFreeNames p1, patFreeNames p2] 

(* identity *)
  (* val rec x = fn x => case x of x => x *)
  (* renamed *)
  (* val rec x = fn y => case y of z => y *)

(* algorithm: 
for binding sites: 
  if not in env, add binding of self to self. 
  if in env, add binding of self to fresh name. 
  how to make the name distinct from all others? 
  start by gathering a set of all names used, and generate distinct. 
for used names, look them up in the environment *)

  fun uncurryFlip f (x, y) = f y x

  fun pplus (renamings : name env) (P.C ce) = 
        (case ce of 
        (* used location - should always have been priorly subjected to a rename. otherwise, error. *)
        C.LITERAL v => P.C (C.LITERAL (renameLiteral renamings v))
      | C.NAME n => P.C (C.NAME (Env.find (n, renamings)))
          (* if n inEnv renamings 
          then (P.C (C.NAME (Env.find (n, renamings))), renamings)
          else let val fresh = freshNameGen ()
               in (P.C (C.NAME fresh), add n fresh renamings) 
               end   *)
      | C.VCONAPP (vc, es)    => 
      (* used locations- rename all *)
        let val es' = map (pplus renamings) es
        in P.C (C.VCONAPP (vc, es'))
        end 
      | C.LAMBDAEXP (n, body) => 
            let val fresh = freshNameGen ()
                val (n', renamings') = 
                    (fresh, add n fresh renamings) 
              val body' = pplus renamings' body
          in P.C (C.LAMBDAEXP (n', body'))
          end
      | C.FUNAPP (e1, e2)     => 
        let val e1' = pplus renamings e1
            val e2' = pplus renamings e2
            in P.C (C.FUNAPP (e1', e2'))
            end)
    | pplus renamings (P.I (P.CASE (scrutinee, branches))) = 
      let val scrutinee' = pplus renamings scrutinee
          fun renamePat patrenamings p = 
            case p 
              of P.PNAME n => 
                  let val fresh = freshNameGen ()
                      val (n', patrenamings') = 
                          (fresh, add n fresh patrenamings)
                  in (P.PNAME n', patrenamings')
                  end
               | P.WHEN e => 
                  let val e' = (pplus patrenamings e) 
                  in (P.WHEN e', patrenamings)
                  end 
               | P.WILDCARD => (P.WILDCARD, patrenamings)
               | P.PATGUARD (p', e) => 
                  let val e'             = pplus patrenamings e 
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
               | P.CONAPP (vc, ps) => 
                    let val (patrenamings', ps') = 
                       ListUtil.foldlmap (uncurryFlip renamePat) patrenamings ps
                  in (P.CONAPP (vc, ps'), patrenamings')
                  end 
          fun renameBranches [] = []
            | renameBranches ((pat, e)::rest) =
                   let val (pat', patrenamings) = renamePat renamings pat
                       val rhs' = pplus patrenamings e
                in (pat', rhs')::renameBranches rest
                end 
          val branches' = renameBranches branches
      in P.I (P.CASE (scrutinee', branches')) 
      end 
  and renameLiteral renamings (v : P.value) = 
    case v of 
        C.LAMBDA (n, _, body) => 
          let val fresh = freshNameGen ()
              val (n', renamings') = (fresh, add n fresh renamings) 
              val body' = pplus renamings' body
          in (C.LAMBDA (n', empty, body'))
          (* does not rename names in closures, nor should it *)
          end
      | C.VCON (vc, vs) => C.VCON (vc, map (renameLiteral renamings) vs)

(* fun renameOrPat lhsrenamings patrenamings p = 
            case p 
              of P.PNAME n => 
                  let val (n', patrenamings') = 
                  if lhsrenamings binds n 
                  then    (lookup n lhsrenamings, patrenamings)
                  else let val fresh = freshNameGen () 
                       in (fresh, add n fresh patrenamings) 
                       end
                  in (P.PNAME n', patrenamings')
                  end
               | P.WHEN e => 
                  let val e' = (pplus patrenamings e) 
                  in (P.WHEN e', patrenamings)
                  end 
               | P.WILDCARD => (P.WILDCARD, patrenamings)
               | P.PATGUARD (p', e) => 
                  let val e'             = pplus patrenamings e 
                      val (p'', patrenamings') = renameOrPat lhsrenamings patrenamings p' 
                  in (P.PATGUARD (p'', e'), patrenamings')
                  end 
               | P.ORPAT (p1, p2) => Impossible.unimp "tricky"
               (* (P.ORPAT (renamePat p1, renamePat p2), renamings) *)
               | P.PATSEQ (p1, p2) => 
                  let val (p1', patrenamings')  = renameOrPat lhsrenamings patrenamings p1
                      val (p2', patrenamings'') = renameOrPat lhsrenamings patrenamings' p2
                  in (P.PATSEQ (p1', p2'), patrenamings'')
                  end 
               | P.CONAPP (vc, ps) => 
                    let val (patrenamings', ps') = 
                       ListUtil.foldlmap (uncurryFlip renamePat) patrenamings ps
                  in (P.CONAPP (vc, ps'), patrenamings')
                  end  *)

end
