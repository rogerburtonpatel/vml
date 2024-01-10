local open VMinus in 


  (* val _ = print (strOfValue (eval Env.empty (IF_FI [(EXISTS ("x", EXISTS ("y", EQN ("y", VCONAPP (Core.TRUE, []), EQN ("x", NAME "y", ARROWALPHA (NAME "x"))))))])) ) *)

  (* val _ = print (strOfValue (eval Env.empty (IF_FI [(EXISTS ("x", EQN ("x", VCONAPP (Core.TRUE, []), EXISTS ("y", EQN ("y", NAME "x", EXISTS ("z", EQN ("y", NAME "x", EXISTS ("w", EQN ("y", NAME "x", EXISTS ("a", EQN ("y", NAME "x", ARROWALPHA (NAME "x"))))))))))))]))) *)
  val cycle_ge = (EXISTS ("x", EXISTS ("y", EQN ("x", NAME "y", EQN ("y", NAME "x", ARROWALPHA (NAME "x"))))))

  val cycle_but_good_ge = (EXISTS ("x", EXISTS ("y", EQN ("x", NAME "y", EQN ("y", NAME "x", EQN ("y", (VCONAPP (Core.K "3", [])), ARROWALPHA (NAME "x")))))))
  val unbound_x_lhs = (EQN ("x", (VCONAPP (Core.K "3", [])), ARROWALPHA (VCONAPP (Core.K "4", []))))
  
  val unbound_y_rhs = (EXISTS ("x", EQN ("x", NAME "y", ARROWALPHA (VCONAPP (Core.K "4", [])))))
  
  val late_y_rhs = (EXISTS ("x", EQN ("x", NAME "y", EXISTS ("y", EQN ("y", (VCONAPP (Core.K "3", [])), ARROWALPHA (NAME "x"))))))
  val late_y_rhs2 = (EXISTS ("x", EXISTS ("y", EQN ("x", NAME "y", EQN ("y", (VCONAPP (Core.K "7", [])), ARROWALPHA (NAME "x"))))))
  
  val good_y_rhs  = (EXISTS ("x", EXISTS ("y", EQN ("y", (VCONAPP (Core.K "3", [])), EQN ("x", NAME "y", ARROWALPHA (NAME "x"))))))
  val good_y_rhs2 = (EXISTS ("x", EXISTS ("y", EQN ("x", NAME "y", EQN ("y", (VCONAPP (Core.K "7", [])), ARROWALPHA (NAME "x"))))))
  
  val exist_unordered       = (EXISTS ("x", EQN ("x", (VCONAPP (Core.K "3", [])), EXISTS ("y", EQN ("y", NAME "x", ARROWALPHA (NAME "x"))))))
  val exist_unordered_cmplx = (EXISTS ("x", EQN ("x", (VCONAPP (Core.K "3", [])), EXISTS ("y", EQN ("y", NAME "x", EXISTS ("z", EQN ("y", NAME "x", EXISTS ("w", EQN ("y", NAME "x", EXISTS ("a", EQN ("y", NAME "x", ARROWALPHA (NAME "x"))))))))))))

  fun solveempty g = eval Env.empty (IF_FI [g])


  val () = Unit.checkExpectWith strOfValue "solving late_y_rhs2"
         (fn () => solveempty late_y_rhs2)
         (VCON (K ("7", [])))

  val _ = solveempty late_y_rhs2
         
  val () = Unit.checkExnWith strOfValue "sorting unbound_x_lhs"
          (fn () => solveempty unbound_x_lhs)
          
  val () = Unit.checkExnWith strOfValue "sorting unbound_y_rhs"
          (fn () => solveempty unbound_y_rhs)

  val () = Unit.checkExnWith strOfValue "sorting late_y_rhs"
          (fn () => solveempty late_y_rhs)

  val () = Unit.checkExpectWith strOfValue "sorting good_y_rhs"
          (fn () => solveempty good_y_rhs)
         (VCON (K ("3", [])))

  val () = Unit.checkExpectWith strOfValue "sorting good_y_rhs2"
          (fn () => solveempty good_y_rhs2)
         (VCON (K ("7", [])))


end 