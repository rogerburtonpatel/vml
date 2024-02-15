structure VMinusParse : sig
  val parse    :  string -> VMinusLex.token list Error.error
end = struct
  fun parse tokens = Impossible.unimp "parser"
end
