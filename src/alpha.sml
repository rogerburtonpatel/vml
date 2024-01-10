signature ALPHA = sig 
    val eqval : 'a -> 'a -> bool 
    val stuckFn : 'a -> bool 
    val alphaEvaluator: 'a -> 'b

end 

structure Alpha :> ALPHA 
  = 
struct 
    fun eqval a1 a2 = raise Impossible.unimp "compare two alphas"
    val stuckFn : 'a -> bool = fn x => raise Impossible.unimp "examine an alpha"
    val alphaEvaluator: 'a -> 'b = fn x => raise Impossible.unimp "evaluate an alpha"
end 