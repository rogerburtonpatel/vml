structure VMinusParse : sig
  val parse    : string list -> PPlus.def list
end = struct
  fun parse tokens = Impossible.unimp "parser"
end
