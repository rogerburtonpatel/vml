structure PplusParse : sig
  val parse    :  PplusLex.token list -> PPlus.def list Error.error
end = struct

  structure L = PplusLex
  structure A = PPlus (* AST *)

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

  (* val int       = P.maybe (fn (L.INT   n)    => SOME n  | _ => NONE) one *)
  val name      = P.maybe (fn (L.NAME  n)    => SOME n  | _ => NONE) one
  val vcon      = P.maybe (fn (L.VCON  n)    => SOME n  | _ => NONE) one
  val left      = P.maybe (fn (L.LEFT s) => SOME s  | _ => NONE) one
  val right      = P.maybe (fn (L.RIGHT s) => SOME s  | _ => NONE) one
  fun reserved s = P.maybe (fn (L.RESERVED s') => if s = s' then SOME () else NONE | _ => NONE) one

  fun token t = sat (P.eq t) one >> succeed () (* parse any token *)

  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type 'a parser = 'a P.producer

  infix 5 *>
  fun p1 *> p2 = curry snd <$> p1 <*> p2
  val op *> : 'a parser * 'b parser -> 'b parser = op *>





  val exp =
    A.NAME <$> name

  val def = 
    reserved "val" *> (curry A.DEF <$> name <*> (reserved "=" *> exp))

  val parse = P.produce (many def)
end
