structure PplusParse : sig
  val parse    :  PplusLex.token list -> PPlus.def list Error.error
end = struct

  structure L = PplusLex

  fun listShow _ [] = "[]"
    | listShow show xs = "[" ^ String.concatWith ", " (map show xs) ^ "]"

  structure P = MkListProducer(val species = "parser"
                               type input = L.token
                               val show = listShow L.tokenString)

  (* parsing-combinators boilerplate *)

  infix 3 <*>      val op <*> = P.<*>
  infixr 4 <$>     val op <$> = P.<$>
  infix 3 <~>      val op <~> = P.<~>
  infix 1 <|>      val op <|> = P.<|>
  infix 3 >>        val op >> = P.>>

  val succeed = P.succeed
  val curry = P.curry
  val curry3 = P.curry3
  val id = P.id
  val fst = P.fst
  val snd = P.snd
  val many = P.many
  val many1 = P.many1
  val sat = P.sat
  val one = P.one
  val notFollowedBy = P.notFollowedBy
  val eos = P.eos
  fun flip f x y = f y x

  (* utilities *)

  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type 'a parser = 'a P.producer



  fun parse tokens = Impossible.unimp "parser"
end
