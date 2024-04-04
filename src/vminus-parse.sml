structure VMinusParse : sig
  val parse    :  VMinusLex.token list -> VMinus.def list Error.error
end = struct

    structure L = VMinusLex

    structure V = VMinus

    fun listShow _ [] = "[]"
    | listShow show xs = "[" ^ String.concatWith ", " (map show xs) ^ "]"

  val showTokens = listShow L.tokenString

  structure P = MkListProducer(val species = "parser"
                               type input = L.token
                               val show = showTokens)

  (* parsing-combinators boilerplate *)

  infix 3  <*>      val op <*> = P.<*>
  infixr 4 <$>      val op <$> = P.<$>
  infix 3  <~>      val op <~> = P.<~>
  infix 1  <|>      val op <|> = P.<|>  
  infix 5  >>       val op >>  = P.>>

  val succeed = P.succeed
  val curry   = P.curry
  val curry3  = P.curry3
  val id      = P.id
  val fst     = P.fst
  val snd     = P.snd
  val many    = P.many
  val many1   = P.many1
  val sat     = P.sat
  val one     = P.one
  val peek    = P.peek
  val notFollowedBy = P.notFollowedBy
  val eos     = P.eos
  
  fun flip f x y  = f y x
  fun member x xs = List.exists (fn y => y = x) xs
  fun uncurry f (x, y) = f x y
  val backslash = StringEscapes.backslash
  (* utilities *)

  (* val int       = P.maybe (fn (L.INT   n)    => SOME n  | _ => NONE) one *)
  val name         = P.maybe (fn (L.NAME  n)    => SOME n  | _ => NONE) one
  val vcon         = P.maybe (fn (L.VCON  n)    => SOME n  | _ => NONE) one
  val left         = P.maybe (fn (L.LEFT s) => SOME s      | _ => NONE) one
  val right        = P.maybe (fn (L.RIGHT s) => SOME s     | _ => NONE) one
  fun reserved s   = P.maybe (fn (L.RESERVED s') => if s = s' then SOME () 
                                                    else NONE | _ => NONE) one
  val semicolon    = reserved ";"
  val bslash       = reserved backslash
  val dot          = reserved "."
  val equalssign   = reserved "="
  val bar          = reserved "|"
  val rightarrow   = reserved "->"
  val exists       = reserved "E"

  val word = reserved
  
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

  val box =     sat (P.eq (L.LEFT L.SQUARE)) one 
             >> sat (P.eq (L.RIGHT L.SQUARE)) one

  fun tokSeparated t p = curry op :: <$> p <*> many (reserved t >> p)
                         <|> succeed []
                        (* parse a token-separated list; may be empty *)
  fun barSeparated p       = tokSeparated "|" p
  fun semicolonSeparated p = tokSeparated ";" p
  fun commaSep p           = tokSeparated "," p
  fun boxSeparated p       = curry op :: <$> p <*> many (box >> p)
  fun barSeparatedMulti p  = curry op :: <$> p <*> many1 (reserved "|" >> p)


  fun lookfor s p = P.ofFunction (fn tokens => 
                  (app eprint ["looking for ", s, "! "]; P.asFunction p tokens))


  val vcons = ["true", "false", "cons"]

  fun isVcon x =
    let val lastPart = List.last (String.fields (curry op = #".") x)
        val firstAfterdot = String.sub (lastPart, 0) handle Subscript => #" "
    in  Char.isUpper firstAfterdot orelse firstAfterdot = #"#" orelse
        String.isPrefix "make-" x orelse member x vcons
    end

  val vcon = 
    Core.K <$> (sat isVcon vcon)


  (* turn any single- or multi-token string into a parser for that token *)
  fun the s =
        let fun matchtokens toks = 
        case toks
          of Error.OK (t::ts) => sat (P.eq t) one >> matchtokens (Error.OK ts)
           | _ => (app eprint ["fail: `", s, "`\n"]; 
                   Impossible.impossible "non-token in P+ parser")
        in matchtokens (VMinusLex.tokenize_line s)
        end

  fun vname n = V.C (Core.NAME n)
  fun vvconapp vc es = V.C (Core.VCONAPP (vc, es))
  fun vlambdaexp n body = V.C (Core.LAMBDAEXP (n, body))
  fun vfunapp e1 e2 = V.C (Core.FUNAPP (e1, e2))
  fun viffi branches = V.I (V.IF_FI branches)

(* p ::= term [| term]
term ::= factor {, factor}
factor ::= atom [<- exp]
atom ::= x | K {atom} | when exp | ❨p❩ *)

  val optional = P.optional

  fun nullaryvcon vc = V.C (Core.VCONAPP (vc, []))


  val exp = P.fix (fn exp : V.exp P.producer => 
    let         
      val existentials = exists >> many name <~> dot
                          <|> succeed []
      
      val guard = P.fix (fn guard : V.exp V.guard P.producer =>
          let val baseguard = curry V.EQN <$> name <*> equalssign >> exp 
        <|>  V.CONDITION <$> exp                          
        <|>  bracketed guard 
          in curry V.CHOICE <$> many1 baseguard <~> bar <*> many1 baseguard 
        <|> baseguard
          end)  
      val guards = semicolonSeparated guard <|> succeed []
      (* val multi = Multi.MULTI <$> many1 exp  *)
      val rhs = rightarrow >> exp 
      val guarded_exp = P.pair <$> existentials <*> (P.pair <$> guards <*> rhs)

    val vconarg : V.exp P.producer =  vname <$> name 
                                  <|> nullaryvcon <$> vcon 
                                  <|> bracketed exp
    val subexp = P.fix (fn subexp =>
      vvconapp <$> vcon <*> many vconarg                                  
        <|> vlambdaexp  <$> bslash >> name <~> dot <*> exp                         
        <|> vname       <$> name                                                   
        <|> viffi       <$> word "if" 
                    >> boxSeparated guarded_exp 
                 <~> word "fi"
                                                                            
        <|>      bracketed exp)
    in 
      (* reserved "guard" >> name >> equalssign >> exp >> succeed (vname "x")  *)
        (* <|>  reserved "gexp" >> guarded_exp >> succeed (vname "x") <|> *)
      (* debugging *)
          uncurry vfunapp <$> (P.pair <$> subexp <*> subexp)                    
      <|> subexp
     end)
    

  val def = 
        word "val"       >> (curry V.DEF <$> name <*> (equalssign >> exp))   
        (* <|>        reserved "parse" >> exp >> P.succeed (V.DEF ("z", vname "z"))        *)
        <|>      (* debugging *)
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
