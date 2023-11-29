local open Guard
local open GuardSort

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

structure E = Error (* aspirational *)

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

(* val () = print ((gexpString (fst cycle_ge)) ^ " sorts to " ^ (gexpString o sort_guard Env.empty o fst) cycle_ge ^ "\n") *)
(* val () = print (gexpString (fst cycle_but_good_ge) ^ "\n")
val () = print ( " sorts to " ^ (gexpString o sort_guard Env.empty o fst) cycle_but_good_ge ^ "\n") *)


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


fun check_ordered (test, expected) = 
            let val check = is_guard_ordered Env.empty
            val passed = 
              (case expected 
                of UNBOUND    => (check test handle NameNotBound n => true)
                 | UNSORTED   => check test 
                 | UNSORTABLE => (check test handle SortFailure s      => true)
                 | SORTED     => check test
                 )
            in if passed
             then "Passed" else "\n Test" ^ gexpString test ^ "Failed."
            end 

(* fun check_sortable (test, expected) = 
            let val check = is_guard_ordered Env.empty
            val passed = 
              (case expected 
                of UNBOUND    => (check test handle NameNotBound n => true)
                 | UNSORTED   => check test 
                 | UNSORTABLE => check test handle Failure s      => true 
                 | SORTED     => check test
                 )
            in if passed
             then "Passed" else "\n Test" ^ gexpString test ^ "Failed."
            end  *)
            
(* run tests *)

val sort_guard = sort_guard Env.empty

val () = Unit.checkExpectWith gexpString "sorting late_y_rhs2"
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
         (fst good_y_rhs2)

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
