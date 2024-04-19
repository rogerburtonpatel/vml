* ‹sets of free type variables in \tuscheme>= *) fun freetyvarsGamma Gamma =
ftvs)
foldl (fn ((x, tau), ftvs) = union (ftvs, freetyvars tau)) emptyset Gamma
（**
(*
(*
(*
（**
SHARED UTILITY FUNCTIONS ON SETS OF TYPE VARIABLES
〈**）
*)
*)
*)
* <shared utility functions on sets of type variables>= *) fun freshName (alpha, avoid) = let val basename = stripNumericSuffix alpha
val candidates =
streamMap (fn n => basename ^ "_"
intString n)
naturals
fun ok beta = not (member beta avoid)
in
case streamGet (streamFilter ok candidates)
of SOME (beta, _) = beta
NONE →> raise InternalError "ran out of natural numbers"
end