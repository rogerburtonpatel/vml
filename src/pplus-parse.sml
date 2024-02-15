structure PplusParse : sig
  val parse    :  string -> PplusLex.token list Error.error
end = struct
  fun parse tokens = Impossible.unimp "parser"
end
