structure DofVminus :> sig
  structure D : DECISION_TREE
  val compile : VMinusSimple.guarded_exp list -> VMinusSimple.exp D.tree
end
  =
structure

  fun compile _ = Impossible.unimp "compile"

end
