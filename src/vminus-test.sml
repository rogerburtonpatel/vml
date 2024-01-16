structure VMTest = struct 

  structure P = PPlus 

  structure T = Translation
  structure A = Translation.VM

  (* val _ = print (valString (eval Env.empty (IF_FI [(A.EXISTS ("x", A.EXISTS ("y", A.EQN ("y", A.VCONAPP (Core.TRUE, []), A.EQN ("x", A.NAME "y", A.ARROWALPHA (A.NAME "x"))))))])) ) *)

  (* val _ = print (valString (eval Env.empty (IF_FI [(A.EXISTS ("x", A.EQN ("x", A.VCONAPP (Core.TRUE, []), A.EXISTS ("y", A.EQN ("y", A.NAME "x", A.EXISTS ("z", A.EQN ("y", A.NAME "x", A.EXISTS ("w", A.EQN ("y", A.NAME "x", A.EXISTS ("a", A.EQN ("y", A.NAME "x", A.ARROWALPHA (A.NAME "x"))))))))))))]))) *)
  
  (* oh for a parser *)
  val cycle_ge = (A.EXISTS ("x", A.EXISTS ("y", A.EQN ("x", A.NAME "y", A.EQN ("y", A.NAME "x", A.ARROWALPHA (A.NAME "x"))))))

  val cycle_but_good_ge = (A.EXISTS ("x", A.EXISTS ("y", A.EQN ("x", A.NAME "y", A.EQN ("y", A.NAME "x", A.EQN ("y", (A.VCONAPP (Core.K "3", [])), A.ARROWALPHA (A.NAME "x")))))))
  val unbound_x_lhs = (A.EQN ("x", (A.VCONAPP (Core.K "3", [])), A.ARROWALPHA (A.VCONAPP (Core.K "4", []))))
  
  val unbound_y_rhs = (A.EXISTS ("x", A.EQN ("x", A.NAME "y", A.ARROWALPHA (A.VCONAPP (Core.K "4", [])))))
  
  val late_y_rhs = (A.EXISTS ("x", A.EQN ("x", A.NAME "y", A.EXISTS ("y", A.EQN ("y", (A.VCONAPP (Core.K "3", [])), A.ARROWALPHA (A.NAME "x"))))))
  val late_y_rhs2 = (A.EXISTS ("x", A.EXISTS ("y", A.EQN ("x", A.NAME "y", A.EQN ("y", (A.VCONAPP (Core.K "7", [])), A.ARROWALPHA (A.NAME "x"))))))
  
  val good_y_rhs  = (A.EXISTS ("x", A.EXISTS ("y", A.EQN ("y", (A.VCONAPP (Core.K "3", [])), A.EQN ("x", A.NAME "y", A.ARROWALPHA (A.NAME "x"))))))
  val good_y_rhs2 = (A.EXISTS ("x", A.EXISTS ("y", A.EQN ("x", A.NAME "y", A.EQN ("y", (A.VCONAPP (Core.K "7", [])), A.ARROWALPHA (A.NAME "x"))))))
  
  val exist_unordered       = (A.EXISTS ("x", A.EQN ("x", (A.VCONAPP (Core.K "3", [])), A.EXISTS ("y", A.EQN ("y", A.NAME "x", A.ARROWALPHA (A.NAME "x"))))))
  val exist_unordered_cmplx = (A.EXISTS ("x", A.EQN ("x", (A.VCONAPP (Core.K "3", [])), A.EXISTS ("y", A.EQN ("y", A.NAME "x", A.EXISTS ("z", A.EQN ("y", A.NAME "x", A.EXISTS ("w", A.EQN ("y", A.NAME "x", A.EXISTS ("a", A.EQN ("y", A.NAME "x", A.ARROWALPHA (A.NAME "x"))))))))))))

  fun solveempty g = A.eval Env.empty (A.IF_FI [g])
  fun evalempty  e = A.eval Env.empty e


  val () = Unit.checkExpectWith A.valString "solving late_y_rhs2"
         (fn () => solveempty late_y_rhs2)
         (A.VCON (A.K ("7", [])))

  val _ = solveempty late_y_rhs2
         
  val () = Unit.checkExnWith A.valString "solving unbound_x_lhs"
          (fn () => solveempty unbound_x_lhs)
          
  val () = Unit.checkExnWith A.valString "solving unbound_y_rhs"
          (fn () => solveempty unbound_y_rhs)

  val () = Unit.checkExnWith A.valString "solving late_y_rhs"
          (fn () => solveempty late_y_rhs)

  val () = Unit.checkExpectWith A.valString "solving good_y_rhs"
          (fn () => solveempty good_y_rhs)
         (A.VCON (A.K ("3", [])))

  val () = Unit.checkExpectWith A.valString "solving good_y_rhs2"
          (fn () => solveempty good_y_rhs2)
         (A.VCON (A.K ("7", [])))

  val pempty = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [])
  (* val _ = print ((A.A.EXpString (vmOfP pempty)) ^ "\n") *)
  val psome = P.CASE (P.VCONAPP (Core.K "cons", [P.VCONAPP (Core.K "1", []), P.VCONAPP (Core.K "nil", [])]), [
    (P.CONAPP ("cons", [P.PNAME "x", P.PNAME "xs"]), P.NAME "x")
  ])

    val () = Unit.checkExpectWith A.expString "translating psome"
          (fn () => T.vmOfP psome)
         (T.vmOfP psome)
(* 
    val () = Unit.checkA.EXpectWith valString "translating psome"
          (fn () => evalempty (vmOfP psome))
         (A.VCON (K ("1", []))) *)



  (* val _ = print ((A.EXpString (vmOfP psome)) ^ "\n") *)

  (* val _ = print ((valString (eval Env.empty (vmOfP psome))) ^ "\n") *)


  end 
