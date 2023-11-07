structure GuardSort :> sig 

  type name = Guard.name
  type logical_variable = Guard.logical_variable

  type exp = Guard.exp 
  type guarded_exp = Guard.guarded_exp 

  type lvar_env = Guard.lvar_env

  type var_status = Guard.var_status

  val sort_guard : lvar_env 
                   -> Guard.guarded_exp
                   -> Guard.guarded_exp

end 
  = 
struct 

  structure G = Guard 

  exception Todo of string 

  type name = G.name
  type logical_variable = G.logical_variable

  type exp = G.exp 
  type guarded_exp = G.guarded_exp 

  type lvar_env = G.lvar_env


  exception NameNotBound of name 
  exception SortFailure of string
  exception Cycle of string

  type var_status = Guard.var_status

  fun binds (rho: lvar_env) n = Env.binds (rho, n)

  fun exists_in n (rho: lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))

  fun floatExists rho gexp = 
    let fun checkBound e rho_ = 
          case e of G.NAME n => if not (binds rho_ n)
                                      then raise NameNotBound n
                                      else ()
                                |    _ =>  ()
    fun normalize rho' buildEs buildGEs gexpr = 
      case gexpr of 
        ar as (G.ARROWEXP e) =>
            let val () = checkBound e rho'
            in buildEs (buildGEs ar)
            end
       | (G.EXPSEQ (e, ge)) =>
            let val () = checkBound e rho'
                val bind_seq = (fn ge' => buildGEs (G.EXPSEQ (e, ge')))
            in normalize rho' buildEs bind_seq ge
            end
       | (G.EXISTS (G.LV x, ge)) =>
            let val bind_exists = (fn ge' => buildEs (G.EXISTS (G.LV x, ge')))
                val rho''       = Env.bind (x, NONE, rho')
            in normalize rho'' bind_exists buildGEs ge 
            end
       | (G.EQN (G.LV y, e, ge)) =>
            let val () = checkBound e rho'
                val () = if not (binds rho' y) then raise NameNotBound y else ()
                val bind_binder = (fn gx => buildGEs (G.EQN (G.LV y, e, gx)))
            (* no need to add to rho' here: we're only checking if names
                are bound, not whether they're known. *)
            in normalize rho' buildEs bind_binder ge
            end
    in normalize rho (fn ge => ge) (fn ge => ge) gexp
    end

  (* napkin algorithm: *)
  (* make a pass, find and gather all independent parts *)
  (* move ind. parts to front, rest to back- done using thunks *)
  (* update env *)
  (* repeat *)
  (* stop if: rest is just ARROWEXP == success
            : rest is unchanged after a pass (indicate with param) == failure *)

  (* captures all independent (i.e. no-dependencies, i.e. one side is found in
    the environment rho) bindings and expressions in a continuation buildBinds
    and returns it, along with whether any new bindings were captured on this
    pass (changed), the leftover guarded-exp with the independent bindings
    stripped (computed with buildLeftover), and the possibly-updated
    environment rho'. *)
  fun moveIndependentsWith rho buildBinds buildLeftover changed gexpr = 
    case gexpr of 
      (G.ARROWEXP e) => 
          (buildBinds, changed, buildLeftover (G.ARROWEXP e), rho)
      | (G.EXPSEQ (G.NAME n, ge)) => 
          let val (buildBinds', buildLeftover', changed') = 
            if   exists_in n rho
            then ((fn gexp => buildBinds (G.EXPSEQ (G.NAME n, gexp))), 
                  buildLeftover, 
                  true)
            else (buildBinds, 
                (fn gexp => buildLeftover (G.EXPSEQ (G.NAME n, gexp))), 
                changed)
          in moveIndependentsWith rho buildBinds' buildLeftover' changed' ge
          end 
      | (G.EXPSEQ (G.IF_FI ges, ge)) =>
        raise Todo "sort sub guarded-exps"
      | (G.EXPSEQ (e, ge)) =>
              moveIndependentsWith rho buildBinds buildLeftover changed ge
      | (G.EXISTS _) => 
        raise Impossible.impossible ("moveIndependentsWith should only be "
                                    ^ "called after floatExists")
      | (G.EQN (x as G.LV x', y as G.NAME y', ge)) =>  
            (* val () = print ("in moveIndependentsWith equation: \n rho: " 
                  ^ Env.toString G.optExpString rho
                  ^ "\n current ge: " 
                  ^ G.gexpString (G.EQN (x, y, ge))
                  ^ "\n") *)
        let val (buildBinds', buildLeftover', changed', rho') = 
              if exists_in x' rho orelse exists_in y' rho
              then 
                ((fn gexp => buildBinds (G.EQN (x, y, gexp))),
                buildLeftover, 
                true, 
                Env.bind (y', SOME (G.NAME x'), 
                                          Env.bind (x', SOME (G.NAME y'), rho)))
              else (buildBinds, 
                  (fn gexp => buildLeftover (G.EQN (x, y, gexp))), 
                  changed, 
                  rho)
          in moveIndependentsWith rho' buildBinds' buildLeftover' changed' ge
          end 
      | (G.EQN (x as G.LV x', e, ge)) =>
        let val (buildBinds', buildLeftover', changed', rho') = 
              ((fn gexp => G.EQN (x, e, gexp)), 
                  buildLeftover, 
                  true, 
                  Env.bind (x', SOME e, rho))
          in moveIndependentsWith rho' buildBinds' buildLeftover' changed' ge
          end 

  fun sortBindings rho gexpr = 
    let fun sortBindings' (G.EXISTS (e, ge)) = G.EXISTS (e, sortBindings' ge)
          | sortBindings' ge = 
      let fun moveAll rho_ binder_acc gex = 
          let val (bind_builder, changed, leftover, rho') = 
            moveIndependentsWith rho_ binder_acc (fn gexp => gexp) false gex
          (* val () = print ("intermediate sort: \n"
                          ^ "lhs: " 
                          ^ G.gexpString (bind_builder (G.ARROWEXP (G.NAME "")))
                          ^ "\n rhs: " ^ G.gexpString leftover
                          ^ "\n rho: " ^ Env.toString G.optExpString rho'
                          ^ "\n") *)
          in case leftover 
              of ar as G.ARROWEXP e => bind_builder ar
                | nontrivial_gex  => 
                if not changed 
                then raise Cycle ("cannot sort " ^ G.gexpString gexpr 
                                  ^ " because it contains a cycle"
                                  ^ " of logical variables.")
                else moveAll rho' bind_builder leftover
          end 
      in moveAll rho (fn gexp => gexp) ge 
      end 
    in sortBindings' gexpr
    end

  fun sort_guard rho ge = sortBindings rho (floatExists rho ge)

  (* cool line from back when i used a list of thunks : *)
  (* foldl (fn (k, gex) => k gex) leftover bind_builders *)

  val gexpString   = G.gexpString
  val expString    = G.expString
  val optExpString = G.optExpString

  val exist_unordered       = G.EXISTS (G.LV "x", G.EQN (G.LV "x", G.INT 3, G.EXISTS (G.LV "y", G.EQN (G.LV "y", G.NAME "x", G.ARROWEXP (G.NAME "x")))))
  val exist_unordered_cmplx = G.EXISTS (G.LV "x", G.EQN (G.LV "x", G.INT 3, G.EXISTS (G.LV "y", G.EQN (G.LV "y", G.NAME "x", G.EXISTS (G.LV "z", G.EQN (G.LV "z", G.NAME "x", G.EXPSEQ (G.NAME "z", G.EXISTS (G.LV "w", G.EQN (G.LV "y", G.NAME "w", G.EXPSEQ (G.NAME "z", G.EXISTS (G.LV "a", G.EQN (G.LV "y", G.NAME "x", G.ARROWEXP (G.NAME "x")))))))))))))

  val unsorted1 = (G.EXISTS (G.LV "x", G.EXISTS (G.LV "y", G.EQN (G.LV "x", G.NAME "y", G.EQN (G.LV "y", G.INT 7, G.ARROWEXP (G.NAME "x"))))))

(* val () = print (gexpString unsorted1 ^ " \nsorts to " ^ ((gexpString o sort_guard Env.empty) unsorted1 ^ "\n")) *)

  (* val () = print (gexpString exist_unordered) 
  val () = print ("\nnormalizes to: \n" ^ ((gexpString o (floatExists Env.empty)) exist_unordered) ^ "\n\n") 
  val () = print (gexpString exist_unordered_cmplx) 
  val () = print ("\nnormalizes to: \n" ^ ((gexpString o (floatExists Env.empty)) exist_unordered_cmplx) ^ "\n")  *)

end 