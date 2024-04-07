structure PPlusParse : sig
  val parse    :  PPlusLex.token list -> PPlus.def list Error.error
end = struct

  structure L = PPlusLex
  (* structure A = OldPPlus AST *)
  structure A = PPlus (* AST *)

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
  val comma        = reserved ","
  val bslash       = reserved backslash
  val dot          = reserved "."
  val equalssign   = reserved "="
  val bar          = reserved "|"
  val rightarrow   = reserved "->"
  val leftarrow    = reserved "<-"

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
  fun barSeparated p = curry op :: <$> p <*> many (reserved "|" >> p)
  fun commaSep p = curry op :: <$> p <*> many (reserved "," >> p)
  fun barSeparatedMulti p = curry op :: <$> p <*> many1 (reserved "|" >> p)


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

  fun ppname n = A.C (Core.NAME n)
  fun ppvconapp vc es = A.C (Core.VCONAPP (vc, es))
  fun pplambdaexp n body = A.C (Core.LAMBDAEXP (n, body))
  fun ppfunapp e1 e2 = A.C (Core.FUNAPP (e1, e2))
  fun ppcase e branches = A.I (A.CASE (e, branches))

(* p ::= term [| term]
term ::= factor {, factor}
factor ::= atom [<- exp]
atom ::= x | K {atom} | when exp | ❨p❩ *)

  fun nullaryvcon vc = A.C (Core.VCONAPP (vc, []))


  val exp = P.fix (fn exp : A.exp P.producer => 
    let         
    val pattern = P.fix (fn pattern => 
      let val atom = P.fix (fn atom =>
      curry A.CONAPP <$> vcon <*> many atom                               
      <|> A.WHEN     <$> (word "when" >> exp)                                    
      <|> A.PNAME    <$> name                                                    
      <|> bracketed pattern)
    val factor = A.PATGUARD <$> (P.pair <$> atom <*> leftarrow >> exp)       
        <|> atom 
    val term = A.PATSEQ <$> (P.pair <$> factor <~> comma <*> pattern)      
        <|> factor  
    in A.ORPAT <$> (P.pair <$> term  <~> bar <*> term)                       
        <|> term
    end)
    fun choice e = P.pair <$> pattern <*> rightarrow >> e

    val vconarg : A.exp P.producer =  ppname <$> name 
                                  <|> nullaryvcon <$> vcon 
                                  <|> bracketed exp
    val subexp = P.fix (fn subexp =>
      ppvconapp <$> vcon <*> many vconarg                                  
        <|> pplambdaexp  <$> bslash >> name <~> dot <*> exp                         
        <|> ppname       <$> name                                                   
        <|> ppcase       <$> word "case" >> exp <*> 
                      word "of"   >> barSeparated (choice exp)               
        <|> bracketed exp)
    in 
      (* reserved "pat" >> pattern >> succeed (ppname "x") <|>                       *)
              (* debugging *)
      uncurry ppfunapp <$> (P.pair <$> subexp <*> subexp)                    
      <|> subexp
     end)
    

  val def = 
        word "val"       >> (curry A.DEF <$> name <*> (equalssign >> exp))   
        (* <|>        reserved "parse" >> exp >> P.succeed (A.DEF ("z", ppname "z"))        *)
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
