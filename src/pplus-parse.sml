structure PplusParse : sig
  val parse    :  PplusLex.token list -> PPlus.def list Error.error
end = struct
  fun parse tokens = Impossible.unimp "parser"
end
