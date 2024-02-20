structure Translation : sig
  type 'a vmFnType
  val vmOfP : PPlus.exp -> 'a vmFnType
  val vmSimpleOfP : PPlus.exp -> VMinusSimple.exp 
  structure VM : VMinus
end 
  =
struct 
  structure P  = PPlus 
  structure VM = VMFn(Alpha)
  structure VMS = VMinusSimple
  structure V  = Verse 
  type 'a vmFnType = 'a VM.exp


  exception Todo of string 

  fun vmOfP (e : P.exp) = 
      case e of P.NAME n => VM.NAME n 
              | P.VCONAPP (vc, es) => VM.VCONAPP (vc, List.map vmOfP es)
              | P.FUNAPP (e1, e2)  => VM.FUNAPP (vmOfP e1, vmOfP e2)
              | P.LAMBDAEXP (n, b)  => VM.LAMBDAEXP (n, vmOfP b)
              | P.CASE (scrutinee, branches) => 
                let val freshNameGen = FreshName.freshNameGenGen ()
                    val e' = vmOfP scrutinee 
                        (* val _ = print ((VM.expString e') ^ "\n") *)
                    val (pats, rhss) = ListPair.unzip branches 
                    val (alreadyName, name) = 
                          (case e' of VM.NAME n => (true, n) 
                                    | _ => (false, freshNameGen ()))
                    (* simply make a pattern look like an equation *)
                    fun translateTlPat (P.PAT p) = translatePat p
                      | translateTlPat _ = Impossible.unimp "todo"
                    and translatePat (P.PNAME n)        = VM.NAME n 
                      | translatePat (P.CONAPP (n, ps)) = 
                                      VM.VCONAPP (Core.K n, map translatePat ps)
                    (* find unbound names in a pattern *)
                    fun tlpatFreeNames (P.PAT p) = patFreeNames p
                      | tlpatFreeNames _ = Impossible.unimp "todo"
                    and patFreeNames (P.PNAME n) = [n]
                      | patFreeNames (P.CONAPP (vc, ps)) = 
                                         List.concat (List.map patFreeNames ps)
                    (* introduce them as necessary with existentials *)
                    (* bind them - ns comes from patFreeNames *)
                    fun introduceExistentials ns g = List.foldr VM.EXISTS g ns
                    (* gexpOfPat depends on future invariant of lhs == a name *)
                    fun gexpOfPat p e' = 
                      let val freenames = tlpatFreeNames p
                          val rhs' = VM.ARROWALPHA (vmOfP e')
                          (* Would call translatePat p "lhs'", but 
                             the language server calls it a 
                             value-restriction error. *)
                          val bind = VM.EQN (name, translateTlPat p, rhs')
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

  fun vmSimpleOfP (e : P.exp) = 
      case e of P.NAME n => VMS.NAME n 
              | P.VCONAPP (vc, es) => VMS.VCONAPP (vc, List.map vmSimpleOfP es)
              | P.FUNAPP (e1, e2)  => VMS.FUNAPP (vmSimpleOfP e1, vmSimpleOfP e2)
              | P.LAMBDAEXP (n, b)  => VMS.LAMBDAEXP (n, vmSimpleOfP b)
              | P.CASE (scrutinee, branches) => 
                let val freshNameGen = FreshName.freshNameGenGen ()
                    val e' = vmSimpleOfP scrutinee 
                        (* val _ = print ((VMS.expString e') ^ "\n") *)
                    val (pats, rhss) = ListPair.unzip branches 
                    val (alreadyName, name) = 
                          (case e' of VMS.NAME n => (true, n) 
                                    | _ => (false, freshNameGen ()))
                    (* simply make a pattern look like an equation *)
                    fun translateTlPat (P.PAT p) = translatePat p
                      | translateTlPat _ = Impossible.unimp "todo"
                    and translatePat (P.PNAME n)        = VMS.NAME n 
                      | translatePat (P.CONAPP (n, ps)) = 
                                      VMS.VCONAPP (Core.K n, map translatePat ps)
                    fun tlpatFreeNames (P.PAT p) = patFreeNames p
                      | tlpatFreeNames _ = Impossible.unimp "todo"
                    (* find unbound names in a pattern *)
                    and patFreeNames (P.PNAME n) = [n]
                      | patFreeNames (P.CONAPP (vc, ps)) = 
                                         List.concat (List.map patFreeNames ps)
                    (* introduce them as necessary with existentials *)
                    (* bind them - ns comes from patFreeNames *)
                    fun introduceExistentials ns g = List.foldr VMS.EXISTS g ns
                    (* gexpOfPat depends on future invariant of lhs == a name *)
                    fun gexpOfPat p e' = 
                      let val freenames = tlpatFreeNames p
                          val rhs' = VMS.ARROWEXP (vmSimpleOfP e')
                          (* Would call translatePat p "lhs'", but 
                             the language server calls it a 
                             value-restriction error. *)
                          val bind = VMS.EQN (name, translateTlPat p, rhs')
                      in introduceExistentials freenames bind
                      end 
                    val internal =   (List.foldr 
                                     (fn ((pat, rhs), gs) => 
                                         (gexpOfPat pat rhs)::gs) 
                                    [] branches)
                in  if alreadyName 
                    then VMS.IF_FI internal
                    else VMS.IF_FI [VMS.EXISTS (name, VMS.EQN (name, e', 
                                   VMS.ARROWEXP (VMS.IF_FI internal)))] 
                end 


  val pempty = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [])
  (* val _ = print ((VM.expString (vmOfP pempty)) ^ "\n") *)
  val psome = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [
    (P.PAT (P.CONAPP ("cons", [P.PNAME "x", P.PNAME "xs"])), P.NAME "x")
  ])
  (* val _ = print ((VM.expString (vmOfP psome)) ^ "\n") *)

  (* val _ = print ((VM.valString (VM.eval Env.empty (vmOfP psome))) ^ "\n") *)



  structure D = DecisionTree
  (* fun translate  *)
  (* need to sort first. big todo, but can adapt old sorting code. *)
  fun dexpOfVmExp (e : 'a VM.exp) = let val (e' : D.exp) = raise Todo "translate exps" in e' end 
  fun dexpOfVmSimpleExp (e : VMS.exp) = let val (e' : D.exp) = raise Todo "translate exps" in e' end 


(* this is a match compiler. *)
  fun treeOfGs [] = D.MATCH (raise Match)
    | treeOfGs (g::gs) = 
    let fun treeOfGuardedExp (VM.ARROWALPHA e)   = D.MATCH (dexpOfVmExp e)
          | treeOfGuardedExp (VM.EXISTS (n, g')) = treeOfGuardedExp g'
          | treeOfGuardedExp (VM.EXPSEQ (e, g')) = 
              let val freshname = FreshName.freshNameGenGen () ()
                  val (fail : D.exp) = raise Todo "failure"
              in 
              D.LET (freshname, dexpOfVmExp e, D.IF (freshname, treeOfGuardedExp g', treeOfGs gs))
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
        | treeOfGuardedExp _ = raise Todo "finish match compilation"
    in treeOfGuardedExp g 
    end 


(* this is a match compiler. *)
  fun treeOfSimpleGs [] = D.MATCH (raise Match)
    | treeOfSimpleGs (g::gs) = 
    let fun treeOfGuardedExp (VMS.ARROWEXP e)   = D.MATCH (dexpOfVmSimpleExp e)
          | treeOfGuardedExp (VMS.EXISTS (n, g')) = treeOfGuardedExp g'
          | treeOfGuardedExp (VMS.EXPSEQ (e, g')) = 
              let val freshname = FreshName.freshNameGenGen () ()
                  val (fail : D.exp) = raise Todo "failure"
              in 
              D.LET (freshname, dexpOfVmSimpleExp e, D.IF (freshname, treeOfGuardedExp g', treeOfSimpleGs gs))
              end 
          | treeOfGuardedExp (VMS.EQN (n, VMS.VCONAPP (Core.K vc, es), g')) = 
            let val arity = List.length es 
                val lcon = (vc, arity)
            (* Big todo: match compile es *)
            (* ask if n is a vc/arity. if so, ask if each of es is matched to the corresponding part of vc.
            normalization helps here, and notably functions can appear within patterns.
            how do we normalize? well, we could put everything in a vconapp into a name. then we get something easier. *)
            (* or, we could normalize beforehand so vcons are only applied to names *)
            in D.TEST (n, [(lcon, treeOfGuardedExp g')], SOME (treeOfSimpleGs gs))
            end 
        | treeOfGuardedExp _ = raise Todo "finish match compilation"
    in treeOfGuardedExp g 
    end 


(* for each e: introduce a fresh name *)
(* fold: acc is existential and sequence *)
  (* fun vOfVMinus ve = 
    case ve of VM.ALPHA a => raise Impossible.impossible "no alphas in verse"
             | VM.NAME n => V.VAL (V.NAME n)
             | VM.VCONAPP (Core.K vc, es) => 
                V.VAL (V.HNF (V.SEQ (V.NAME vc::(map vOfVMinus es)))) *)
             (* existentially introduce all es *)
             (* give a sequence of all of them *)


end
