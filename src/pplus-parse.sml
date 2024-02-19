structure PPlusParse : sig
  val parse    :  PPlusLex.token list -> PPlus.def list Error.error
end = struct

  structure L = PPlusLex
  structure A = PPlus (* AST *)

  fun listShow _ [] = "[]"
    | listShow show xs = "[" ^ String.concatWith ", " (map show xs) ^ "]"

  val showTokens = listShow L.tokenString

  structure P = MkListProducer(val species = "parser"
                               type input = L.token
                               val show = showTokens)

  (* parsing-combinators boilerplate *)

  infix 3 <*>      val op <*> = P.<*>
  infixr 4 <$>     val op <$> = P.<$>
  infix 3 <~>      val op <~> = P.<~>
  infix 1 <|>      val op <|> = P.<|>
  infix 5 >>        val op >> = P.>>

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
  val peek = P.peek
  val notFollowedBy = P.notFollowedBy
  val eos = P.eos
  fun flip f x y = f y x

  (* utilities *)

  (* val int       = P.maybe (fn (L.INT   n)    => SOME n  | _ => NONE) one *)
  val name         = P.maybe (fn (L.NAME  n)    => SOME n  | _ => NONE) one
  val vcon         = P.maybe (fn (L.VCON  n)    => SOME n  | _ => NONE) one
  val left         = P.maybe (fn (L.LEFT s) => SOME s  | _ => NONE) one
  val right        = P.maybe (fn (L.RIGHT s) => SOME s  | _ => NONE) one
  val comma        = P.maybe (fn s as (L.SPECIAL L.COMMA) => SOME s  | _ => NONE) one
  val bslash       = P.maybe (fn s as (L.SPECIAL L.BACKSLASH) => SOME s  | _ => NONE) one
  val dot          = P.maybe (fn s as (L.SPECIAL L.DOT) => SOME s  | _ => NONE) one
  fun reserved s   = P.maybe (fn (L.RESERVED s') => if s = s' then SOME () 
                                                    else NONE | _ => NONE) one

  fun token t = sat (P.eq t) one >> succeed () (* parse any token *)

  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type 'a parser = 'a P.producer

  (* always-error parser; useful for messages *)
  fun expected what =
    let fun bads ts = Error.ERROR ("looking for " ^ what ^
                                   ", got this input: " ^ showTokens ts)
    in  P.check ( bads <$> many one )
    end

  fun bracketed p = left >> p <~> right  (* XXX TODO they need not match *)
(* XXX TODO case K of -> out of memory *)
  fun barSeparated p = curry op :: <$> p <*> many (reserved "|" >> p)
  fun barSeparatedMulti p = curry op :: <$> p <*> many1 (reserved "|" >> p)

  val pattern = P.fix (fn pattern =>
      curry A.CONAPP <$> vcon <*> many pattern <|>
      A.PNAME  <$> name <|> 
      bracketed pattern
      )


  fun lookfor s p = P.ofFunction (fn tokens => 
                  (app eprint ["looking for ", s, "! "]; P.asFunction p tokens))

  fun isVcon x =
    let val lastPart = List.last (String.fields (curry op = #".") x)
        val firstAfterdot = String.sub (lastPart, 0) handle Subscript => #" "
    in  Char.isUpper firstAfterdot orelse firstAfterdot = #"#" orelse
        String.isPrefix "make-" x
    end

  val vcon = 
    sat (fn s => s = "false") vcon >> succeed Core.FALSE <|>
    sat (fn s => s = "true" ) vcon >> succeed Core.TRUE  <|>
    Core.K <$> (sat isVcon vcon)


  (* turn any single- or multi-token string into a parser for that token *)
  fun the s =
        let fun matchtokens toks = 
        case toks
          of Error.OK (t::ts) => sat (P.eq t) one >> matchtokens (Error.OK ts)
           | _ => (app eprint ["fail: `", s, "`\n"]; 
                   Impossible.impossible "non-token in P+ parser")
        in matchtokens (PPlusLex.tokenize_line s)
        end


  val exp = P.fix (fn exp : A.exp P.producer => 
    let 
    fun guard (e : A.exp P.producer) = 
      P.pair <$> sat (fn tok => tok = L.SPECIAL L.COMMA) one (* better way to do this? *)
                 >> pattern <*> reserved "<-" >> e
        val topLevelPattern = 
        P.fix (fn topLevelPattern => 
          A.PATGUARD <$> bracketed (P.pair <$> topLevelPattern 
                                            <*> many (guard exp)) <|>
          A.WHEN <$> bracketed (P.pair <$> topLevelPattern 
                          <~> reserved "when" <*> exp)            <|>
          A.ORPAT <$> barSeparatedMulti pattern                   <|>
          A.PAT   <$> pattern                                     <|>
          bracketed topLevelPattern
  )
    fun choice e = P.pair <$> topLevelPattern <*> reserved "->" >> e
    in 
      reserved "pat" >> topLevelPattern >> succeed (A.NAME "x")   <|> 
      curry A.VCONAPP <$> vcon <*> many exp                       <|> 
      A.FUNAPP <$> bracketed (P.pair <$> exp <*> exp)             <|> 
      curry A.LAMBDAEXP <$> bslash >> name <~> dot <*> exp                          <|> 
      A.NAME <$> name                                             <|> 
      curry A.CASE <$> reserved "case" >> exp <*> 
                       reserved "of" >> barSeparated (choice exp) <|> 
      bracketed exp
     end )
    

  val def = 
        reserved "val"   >> (curry A.DEF <$> name <*> (reserved "=" >> exp)) <|>
        reserved "parse" >> exp >> P.succeed (A.DEF ("z", A.NAME "z"))       <|>
        peek one         >> expected "definition"
(*
     -- dirty trick for testing

*)
  val parse = 
  P.produce (curry fst <$> many def <*> eos)

  fun parse input = 
  let val () = 
  (
    ()
    (* ;app eprint ["reading from token stream: \n", String.concatWith ", " (map L.tokenString input), "\n"] *)
  )
  in P.produce (curry fst <$> many def <*> eos) input 
  end

end
