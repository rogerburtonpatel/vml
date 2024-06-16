structure DParse : sig
  val parse    :  DLex.token list -> D.def list Error.error
end = struct

  structure L = DLex
  structure A = D (* AST *)

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
  val optional     = P.optional
  
  fun flip f x y  = f y x
  val member = ListUtil.member
  fun uncurry f (x, y) = f x y
  val backslash = StringEscapes.backslash
  (* utilities *)

  fun curry4 f x y z w = f (x, y, z, w)

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
  val wildcard     = reserved "_"

  val word = reserved
  
  fun token t = sat (P.eq t) one >> succeed () (* parse any token *)

  fun eprint s = TextIO.output (TextIO.stdErr, s)

  type 'a parser = 'a P.producer

  (* always-error parser; useful for messages *)
  fun expected what =
    let fun bads ts = Error.ERROR ("Parse error: looking for " ^ what ^
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

  val vcon = Core.K <$> (sat isVcon vcon)

  fun dname n = A.C (Core.NAME n)
  fun dvconapp vc es = A.C (Core.VCONAPP (vc, es))
  fun dlambdaexp n body = A.C (Core.LAMBDAEXP (n, body))
  fun dfunapp e1 e2 = A.C (Core.FUNAPP (e1, e2))
  fun dtree t = A.I t


  fun nullaryvcon vc = A.C (Core.VCONAPP (vc, []))
  fun branch a = succeed a

(* test 𝑥 {𝐾 {𝑦} ⇒ 𝑡 }[else 𝑡] node
| let 𝑥 = 𝑒 in 𝑡 [ unless fail => 𝑡]-unless node
| if 𝑥 = 𝑒 then 𝑡 else 𝑡 node
| ∃ 𝑥. 𝑡 node
| fail fail *)

  val exp = P.fix (fn exp : A.exp P.producer => 
    let         
    val tree = P.fix (fn tree : (D.exp, 'a) D.tree P.producer =>
      let val branch = P.fix (fn branch : ((Core.vcon * string list) * (D.exp, 'a) D.tree) P.producer
      =>  
      P.pair <$> (P.pair <$> vcon <*> many name) <*> tree)
      in
        curry3 A.TEST <$> word "test" >> name <*> many branch <*> optional (word "else" >> tree)
    <|> curry4 A.LET_UNLESS <$> word "let" >> name <*> equalssign >> exp 
        <*> word "in" >> tree 
        <*> optional (word "unless" >> word "fail" >> word "=>" >> tree)
    <|> curry4 A.IF_THEN_ELSE <$> word "if" >> name <*> equalssign >> name 
       <*> word "then" >> tree <*> word "else" >> tree
    <|> word "fail" >> succeed A.FAIL
    end
    )

    val vconarg : A.exp P.producer =  dname <$> name 
                                  <|> nullaryvcon <$> vcon 
                                  <|> bracketed exp
    val subexp = P.fix (fn subexp =>
      dvconapp <$> vcon <*> many vconarg                                  
        <|> dlambdaexp  <$> bslash >> name <~> dot <*> exp                         
        <|> dname       <$> name                                                   
        <|> A.I <$> tree
        <|> bracketed exp)
    in 
      (* reserved "pat" >> pattern >> succeed (ppname "x") <|>  *)
              (* debugging *)
      uncurry dfunapp <$> (P.pair <$> subexp <*> subexp)                    
      <|> subexp
     end)

  val def = 
        word "val"       >> (curry A.DEF <$> name <*> (equalssign >> exp))   
        (* <|>        reserved "parse" >> exp >> P.succeed (A.DEF ("z", ppname "z"))        *)
        <|>      (* debugging *)
        peek one         >> expected "definition"

  val parse = P.produce (curry fst <$> many def <*> eos)

end
