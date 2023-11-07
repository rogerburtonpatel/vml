open Guard

(* hack for tests  *)

fun binds (rho: lvar_env) n = Env.binds (rho, n)

fun exists_in n (rho: lvar_env) = 
    Env.binds (rho, n) andalso isSome (Env.find (n, rho))

fun var_status n rho = 
    if not (binds rho n) then NOT_BOUND
    else if not (exists_in n rho) then NOT_KNOWN
    else VAR n 



(* val (x, y, z) = ("x", "y", "z") *)
exception NameNotBound of name 
exception SortFailure of string
exception Cycle of string
exception Todo of string

structure E = Error

(* fun tsort rho exp = 
(* builds a guarded_exp with a binding of the form "x = y", where y is 
   bound but not known, after the point where y becomes known, or fails
   by reaching the end of guarded-exps or finding a cycle.*)
 let fun insert_binding (ARROWEXP _) x y = 
           raise SortFailure ("failed to insert binding name " ^ y)
           (* note that this case catches cycles- TODO TEST TO BE *)
       | insert_binding (EXPSEQ (ex, ge)) x y  = 
              let val (e_final, ge_final) = insert_binding ge x y 
              in (e_final, EXPSEQ (ex, ge_final))
              end 
       | insert_binding (EXISTS (lv, ge)) x y  =
              let val (e_final, ge_final) = insert_binding ge x y 
              in (e_final, EXISTS (lv, ge_final))
              end 
       | insert_binding (EQN (LV y', e', ge)) x y  = 
        let fun isBindingName (NAME name) name' = name = name'
              | isBindingName _           _     = false 
        val () = print ("INSERTING INTO EQN: \n" ^ 
                            "y' = " ^ y' ^ ", " ^
                            "e' = " ^ expString e' ^ ", " ^
                            "ge = " ^ gexpString ge ^ ", " ^
                            "x = "  ^ x ^ ", " ^
                            "y = "  ^ y ^ ", " ^
                            "\n")
        in 
         (case  (y' = y, isBindingName e' x)
         of (true, false) => (e', EQN (LV y', e', EQN (LV x, NAME y, ge))) (* money case- bind later *)
          | _             => let val (e_final, ge_final) = insert_binding ge x y 
                              in (e_final, EQN (LV y', e', ge_final))
                              end)
         end 
  (* sorts a guarded exp or raises Failure *)
  fun tsort' (ARROWEXP e ) = ARROWEXP e (* check for lvars in e *)
    | tsort' (EXPSEQ (e, ge)) = EXPSEQ (e, tsort' ge)
    | tsort' (EXISTS (LV n, ge)) = 
                  EXISTS (LV n, tsort (Env.bind (n, NONE, rho)) ge)
    | tsort' (EQN (LV x, e, ge)) = 
       if not (binds rho x)
       then raise NameNotBound x
       else (case e 
               of NAME y => 
                 (case var_status y rho 
                    of NOT_BOUND => raise NameNotBound y
                     | VAR z     => 
                     let val () = print ("Found val " ^ z ^ "\n")
                     in 
                     
                     EQN (LV x, e, tsort (Env.bind (x, SOME e, rho)) ge)
                     end 
                     | NOT_KNOWN => 
                              let val (e_final, ge_final) = insert_binding ge x y
                                  val rho' = Env.bind (y, SOME e_final, rho)
                                  val () = print ("Sorting " ^ gexpString ge_final ^ " with rho' " ^ Env.toString optExpString rho' ^ "\n")
                              in tsort rho' ge_final
                              end)
                                    (* ^ sort with insertion*)
                 | _ => EQN (LV x, e, tsort' ge))
  in tsort' exp 
  end  *)


fun floatExists rho gexp = 
  let fun normalize rho' buildEs buildGEs (ARROWEXP e) =
          let val final_bindings =  (fn () => buildEs (buildGEs (ARROWEXP e)))
          in (case e of NAME n => if not (binds rho' n)
                                  then raise NameNotBound n
                                  else final_bindings ()
                             |    _ => final_bindings ())
          end
        | normalize rho' buildEs buildGEs (EXPSEQ (e, ge)) = 
          let val bind_seq = (fn ge' => buildGEs (EXPSEQ (e, ge')))
          in (case e of NAME n =>  
            if not (binds rho' n) 
            then raise NameNotBound n
            else normalize rho' buildEs bind_seq ge 
          | _ => normalize rho' buildEs bind_seq ge)
          end
        | normalize rho' buildEs buildGEs (EXISTS (LV x, ge)) = 
            let val bind_exists = (fn ge' => buildEs (EXISTS (LV x, ge')))
                val rho''     = (Env.bind (x, NONE, rho'))
            in normalize rho'' bind_exists buildGEs ge 
            end
        | normalize rho' buildEs buildGEs (EQN (LV y, e, ge)) = 
            let val bind_binder = (fn ge' => buildGEs (EQN (LV y, e, ge')))
            in (case e of NAME n => 
                  if not (binds rho' n) andalso not (binds rho' y)
                  then raise NameNotBound n
                  else normalize rho' buildEs bind_binder ge
                | _ => normalize rho' buildEs bind_binder ge)
            end
  in normalize rho (fn ge => ge) (fn ge => ge) gexp
  end

fun tsort rho gexp = 
(* builds a guarded_exp with a binding of the form "x = y", where y is 
   bound but not known, after the point where y becomes known, or fails
   by reaching the end of guarded-exps or finding a cycle.*)
 let fun insert_binding (ARROWEXP _) x y = 
           raise SortFailure ("failed to insert binding name " ^ y)
           (* note that this case catches cycles- TODO TEST TO BE *)
       | insert_binding (EXPSEQ (ex, ge)) x y  = 
              let val (e_final, ge_final) = insert_binding ge x y 
              in (e_final, EXPSEQ (ex, ge_final))
              end 
       | insert_binding (EXISTS (lv, ge)) x y  =
              let val (e_final, ge_final) = insert_binding ge x y 
              in (e_final, EXISTS (lv, ge_final))
              end 
       | insert_binding (EQN (LV y', e', ge)) x y  = 
        let fun isBindingName (NAME name) name' = name = name'
              | isBindingName _           _     = false 
        val () = print ("INSERTING INTO EQN: \n" ^ 
                            "y' = " ^ y' ^ ", " ^
                            "e' = " ^ expString e' ^ ", " ^
                            "ge = " ^ gexpString ge ^ ", " ^
                            "x = "  ^ x ^ ", " ^
                            "y = "  ^ y ^ ", " ^
                            "\n")
        in 
         (case  (y' = y, isBindingName e' x)
         of (true, false) => (e', EQN (LV y', e', EQN (LV x, NAME y, ge))) (* money case- bind later *)
          | _             => let val (e_final, ge_final) = insert_binding ge x y 
                              in (e_final, EQN (LV y', e', ge_final))
                              end)
         end 
  (* sorts a guarded exp or raises Failure *)
  fun tsort' (ARROWEXP e ) = ARROWEXP e (* check for lvars in e *)
    | tsort' (EXPSEQ (e, ge)) = EXPSEQ (e, tsort' ge)
    | tsort' (EXISTS (LV n, ge)) = 
                  EXISTS (LV n, tsort (Env.bind (n, NONE, rho)) ge)
    | tsort' (EQN (LV x, e, ge)) = 
       if not (binds rho x)
       then raise NameNotBound x
       else (case e 
               of NAME y => 
                 (case var_status y rho 
                    of NOT_BOUND => raise NameNotBound y
                     | VAR z     => 
                     let val () = print ("Found val " ^ z ^ "\n")
                     in 
                     
                     EQN (LV x, e, tsort (Env.bind (x, SOME e, rho)) ge)
                     end 
                     | NOT_KNOWN => 
                              let val (e_final, ge_final) = insert_binding ge x y
                                  val rho' = Env.bind (y, SOME e_final, rho)
                                  val () = print ("Sorting " ^ gexpString ge_final ^ " with rho' " ^ Env.toString optExpString rho' ^ "\n")
                              in tsort rho' ge_final
                              end)
                                    (* ^ sort with insertion*)
                 | _ => EQN (LV x, e, tsort' ge))
  in tsort' gexp 
  end 



val sort_guard = tsort Env.empty

(* true if e has unbound logical variables, false otherwise. *)
val rec has_unbound_lvars : exp -> exp option Env.env -> bool = 
  fn e => fn rho => 
    case e of INT _ => false 
            | NAME name => 
              not ((Env.binds (rho, name))
                    andalso (isSome (Env.find (name, rho))))
            | IF_FI gs => raise Todo "find unbound lvars in nested IF-FI"
            (* | GUARDED_EXP (ARROWEXP ex) => has_unbound_lvars ex rho 
            | GUARDED_EXP (EXPSEQ (ex, ge)) => 
                                  has_unbound_lvars ex rho
                                  orelse has_unbound_lvars (GUARDED_EXP ge) rho
            | (GUARDED_EXP (EXISTS (LV lv, ge))) => 
                              has_unbound_lvars (GUARDED_EXP ge) 
                                                    (Env.bind (lv, NONE, rho))
                                  (* bind a name to itself to indicate it 
                                  exists in the environment without a binding *)
            | GUARDED_EXP (EQN (LV lv, ex, ge)) => 
                  has_unbound_lvars ex rho 
                  orelse 
                  has_unbound_lvars (GUARDED_EXP ge) 
                                        (Env.bind (lv, SOME ex, rho)) *)


exception Must_be_sorted
(* Traverses a guard, determining if the order it's in is the order needed 
to bind all logical variables to expressions that contain no unsolved logical
variables. If it fails, it raises an exception: eventually will sort it. *)
val rec order_guard : exp option Env.env -> guarded_exp -> guarded_exp = 
  fn rho => fn gex => 
    case gex of ARROWEXP e => ARROWEXP e
      | EXPSEQ (e, ge) => EXPSEQ (e, order_guard rho ge)
      | EXISTS (LV lv, ge) => EXISTS (LV lv, 
                                      order_guard (Env.bind (lv, NONE, rho)) ge)
      | (EQN (LV x, e, ge)) => if has_unbound_lvars e rho 
                                  orelse not (Env.binds (rho, x))
                               then 
                                let val () = print ("failed to find name: " ^ 
                                                        x ^ " in order_guard\n") 
                                in 
                                  raise Must_be_sorted 
                                end
                               else 
                                EQN (LV x, e, order_guard 
                                               (Env.bind (x, SOME e, rho)) ge)


(* val () = ignore (order_guard Env.empty (ARROWEXP (INT 3)))
val () = ignore (order_guard Env.empty unbound_x_lhs)
val () = ignore (order_guard Env.empty unbound_y_rhs) *)


(* Traverses a guard, determining if the order it's in is the order needed 
to bind all logical variables to expressions that contain no unsolved logical
variables. If it fails, returns false. *)
val rec is_guard_ordered : exp option Env.env -> guarded_exp -> bool = 
  fn rho => fn gex => 
    case gex of ARROWEXP e => true
      | EXPSEQ (e, ge) => is_guard_ordered rho ge 
      | EXISTS (LV lv, ge) =>  is_guard_ordered (Env.bind (lv, NONE, rho)) ge
      | (EQN (LV x, e, ge)) => (not (has_unbound_lvars e rho)
                                andalso (Env.binds (rho, x))) 
                                andalso
                                is_guard_ordered (Env.bind (x, SOME e, rho)) ge

(* val rec sort_guard : exp option Env.env -> guarded_exp -> guarded_exp = 
  fn rho => fn gex => 
    case gex of ARROWEXP e => ARROWEXP e
      | EXPSEQ (e, ge) => EXPSEQ (e, sort_guard rho ge)
      | EXISTS (LV lv, ge) => EXISTS (LV lv, 
                                      order_guard (Env.bind (lv, NONE, rho)) ge)
      | (EQN (LV x, e, ge)) => if has_unbound_lvars e rho 
                                  orelse not (Env.binds (rho, x))
                               then 
                                let val () = print ("failed to find name: " ^ 
                                                        x ^ " in order_guard\n") 
                                in 
                                  raise Must_be_sorted 
                                end
                               else 
                                EQN (LV x, e, order_guard 
                                               (Env.bind (x, SOME e, rho)) ge) *)

(************************ TESTING ************************)

datatype test_status = UNBOUND | UNSORTED | UNSORTABLE | SORTED

fun statusString UNBOUND    = "unbound"
  | statusString UNSORTED   = "unsorted"
  | statusString UNSORTABLE = "unsortable"
  | statusString SORTED     = "sorted"

fun fst (x, y) = x
fun snd (x, y) = y

val unbound_x_lhs = (EQN (LV "x", INT 3, ARROWEXP (INT 4)), UNBOUND)

val unbound_y_rhs = (EXISTS (LV "x", EQN (LV "x", NAME "y", ARROWEXP (INT 4))), UNBOUND)

val late_y_rhs = (EXISTS (LV "x", EQN (LV "x", NAME "y", EXISTS (LV "y", EQN (LV "y", INT 3, ARROWEXP (NAME "x"))))), UNBOUND)
val late_y_rhs2 = (EXISTS (LV "x", EXISTS (LV "y", EQN (LV "x", NAME "y", EQN (LV "y", INT 7, ARROWEXP (NAME "x"))))), UNSORTED)

val good_y_rhs  = (EXISTS (LV "x", EXISTS (LV "y", EQN (LV "y", INT 3, EQN (LV "x", NAME "y", ARROWEXP (NAME "x"))))), SORTED)
val good_y_rhs2 = (EXISTS (LV "x", EXISTS (LV "y", EQN (LV "y", INT 7, EQN (LV "x", NAME "y", ARROWEXP (NAME "x"))))), SORTED)

val exist_unordered       = (EXISTS (LV "x", EQN (LV "x", INT 3, EXISTS (LV "y", EQN (LV "y", NAME "x", ARROWEXP (NAME "x"))))), UNBOUND)
val exist_unordered_cmplx = (EXISTS (LV "x", EQN (LV "x", INT 3, EXISTS (LV "y", EQN (LV "y", NAME "x", EXISTS (LV "z", EQN (LV "y", NAME "x", EXISTS (LV "w", EQN (LV "y", NAME "x", EXISTS (LV "a", EQN (LV "y", NAME "x", ARROWEXP (NAME "x"))))))))))), UNBOUND)


(* val () = print ((gexpString o (GuardSort.floatExists Env.empty)) (fst exist_unordered)) *)
(* val () = print ((gexpString o (floatExists Env.empty)) (fst exist_unordered_cmplx)) *)




val cycle_ge = (EXISTS (LV "x", EXISTS (LV "y", EQN (LV "x", NAME "y", EQN (LV "y", NAME "x", ARROWEXP (NAME "x"))))), UNSORTED)
val cycle_but_good_ge = (EXISTS (LV "x", EXISTS (LV "y", EQN (LV "x", NAME "y", EQN (LV "y", NAME "x", EQN (LV "y", INT 3, ARROWEXP (NAME "x")))))), UNSORTED)


(* COMMENT TESTS BACK IN *)

val () = print ((gexpString (fst cycle_ge)) ^ " sorts to " ^ (gexpString o sort_guard o fst) cycle_ge ^ "\n")
(* val () = print (gexpString (fst cycle_but_good_ge) ^ "\n")
val () = print ( " sorts to " ^ (gexpString o sort_guard o fst) cycle_but_good_ge ^ "\n") *)


fun make_sorted_test ge_test_tuple = 
        (sort_guard (fst ge_test_tuple), SORTED)

(* val sorted_late_y_rhs = make_sorted_test late_y_rhs *)
(* val sorted_late_y_rhs2 = make_sorted_test late_y_rhs2 *)


(* val tests = [unbound_x_lhs, unbound_y_rhs, late_y_rhs, 
             late_y_rhs2, sorted_late_y_rhs2, good_y_rhs, good_y_rhs2, cycle_ge, cycle_but_good_ge] *)

fun curry f x y = f (x, y)

fun ListPrint converter xs = 
    print ("[" ^ (ListUtil.join converter ", " xs) ^ "]\n")

(* val () = ListPrint (fn s => s) (String.tokens (fn c =>  List.exists (fn c' => c' = c) [#".", #";"]) "∃x. ∃y. x = 3; y = x; x") *)


(* fun check_ordered (test, expected) = 
            let val check = is_guard_ordered Env.empty
            val passed = 
              (case expected 
                of UNBOUND    => check test handle NameNotBound n => true 
                 | UNSORTED   => check test 
                 | UNSORTABLE => check test handle Failure s      => true 
                 | SORTED     => check test
                 )
            in if passed
             then "Passed" else "\n Test" ^ gexpString test ^ "Failed."
            end  *)

(* fun check_sortable (test, expected) = 
            let val check = is_guard_ordered Env.empty
            val passed = 
              (case expected 
                of UNBOUND    => check test handle NameNotBound n => true 
                 | UNSORTED   => check test 
                 | UNSORTABLE => check test handle Failure s      => true 
                 | SORTED     => check test
                 )
            in if passed
             then "Passed" else "\n Test" ^ gexpString test ^ "Failed."
            end 
             *)
(* run tests *)

(* val () = Unit.checkExpectWith gexpString "sorting late_y_rhs2"
         (fn () => sort_guard (fst late_y_rhs2))
         (fst good_y_rhs2)
         
val () = Unit.checkExnWith gexpString "sorting unbound_x_lhs"
         (fn () => sort_guard (fst unbound_x_lhs))
         
val () = Unit.checkExnWith gexpString "sorting unbound_y_rhs"
         (fn () => sort_guard (fst unbound_y_rhs))

val () = Unit.checkExnWith gexpString "sorting late_y_rhs"
         (fn () => sort_guard (fst late_y_rhs))

val () = Unit.checkExpectWith gexpString "sorting good_y_rhs"
         (fn () => sort_guard (fst good_y_rhs))
         (fst good_y_rhs)

val () = Unit.checkExpectWith gexpString "sorting good_y_rhs2"
         (fn () => sort_guard (fst good_y_rhs2))
         (fst good_y_rhs2) *)

val () = Unit.report ()


fun checkSort sorted_check test' = 
  let val (test, test_status) = test' 
  in 
  (if (sorted_check test) then 
    (case test_status 
       of SORTED   => "Passed"
        | UNSORTED => "Passed" 
        | wrong  => "Failed: expected test " ^ gexpString test ^ "to be " 
                                             ^ statusString test_status 
                                             ^ ", but it's sorted.")
    else "Failed")
  handle NameNotBound n => (case test_status
                              of UNBOUND => "Passed"
                              | _        => "Failed: \n" ^ 
                                             "could not sort \n" ^
                                             gexpString test ^
                                             "\n: name " ^ n ^ " is not bound.")
       | SortFailure s => (case test_status
                              of UNSORTABLE => "Passed"
                              | _        => "Failed: \n" ^ 
                                             "could not sort \n" ^
                                             gexpString test ^
                                             "\n: " ^ s)
end 

(* val () = ListPrint (fn s => s) 
        (List.map (checkSort (is_guard_ordered Env.empty o sort_guard)) tests) *)


(* old version with environments and multple returns for swapping - 
doesn't work because names can go out of scope.  *)
(* fun tsort exp rho = 
let fun insert_binding (ARROWEXP _) e (LV n) rho = 
          raise Failure ("failed to insert binding name " ^ n)
      | insert_binding (EXPSEQ (ex, ge)) e n rho = 
          let val (n', e', ge') = insert_binding ge e n rho 
          in      (n', e', EXPSEQ (ex, ge'))
          end 
      | insert_binding (EXISTS (lv, ge)) e n rho =
          let val (n', e', ge') =      insert_binding ge e n rho 
          in      (n', e', EXISTS (lv, ge'))
          end
      | insert_binding (EQN (LV n', e', ge)) e (LV n) rho = 
        if    n = n'
        then  (LV n', e', EQN (LV n, e, ge))
        else 
          let val (n'', e'', ge') =      insert_binding ge e (LV n) rho 
          in      (n'', e'', EQN (LV n', e', ge))
          end
 fun tsort (ARROWEXP e ) = ARROWEXP e (*check for lvars in e *)
  | tsort (EXPSEQ (e, ge)) = EXPSEQ (e, tsort ge)
  | tsort (EXISTS (LV n, ge)) = 
                EXISTS (LV n, tsort ge (Env.bind (n, NONE, rho)))
  | tsort (EQN (LV n, e, ge)) = 
      if not (binds rho n) 
      then raise NameNotBound n 
      else let val (n_final, e_final, ge_final) = 
            (case e 
              of NAME n' => 
                (case var_status n' rho 
                   of NOT_BOUND => raise NameNotBound n'
                    | VAR _ => (LV n, e, ge)
                    | NOT_KNOWN => raise Todo 
                      (* let ge'  *)
                      )
                | _ => (LV n, e, ge))
                in EQN (n_final, e_final, ge_final)
                end 
  in tsort exp 
  end  *)

(* old cycle-detection code *)
          (* (* takes a name, a gen-exp, and a cycling name (the name nm is already bound to)
           and finds if the gen-exp makes  *)
          let fun known_in_with nm (ARROWEXP _)  cnm = false 
                | known_in_with nm (EXPSEQ _, gex) cnm = known_in nm gex 
                | known_in_with nm (EXISTS _, gex) cnm = known_in nm gex
                | known_in_with nm (EQN (nm', ex, gex)) cnm = 
                  if nm = nm' then 
                  case 
        
        
        raise Cycle ("names \"" ^ x ^ "\" and \"" 
                                     ^ y ^ "\" depend on each other;" 
                          ^ " the guarded expression cannot be ordered.") *)
