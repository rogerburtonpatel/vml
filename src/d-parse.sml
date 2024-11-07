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

    (* always-succeed parser; prints msg when run *)
  fun debug msg =
      P.ofFunction (fn ts => (app eprint ["@> ", msg, "\n"]; SOME (Error.OK (), ts)))

  (* make another parser chatter on entry *)
  val verbose : string -> 'a parser -> 'a parser
   = (fn msg => fn p => debug msg >> p)

  val veryVerbose : string -> 'a parser -> 'a parser
      = (fn what => fn p =>
           let fun shout s = app eprint ["looking for ", what, s, "\n"]
           in  P.ofFunction (fn ts =>
                                let val _ = shout "..."
                                    val answer = P.asFunction p ts
                                    val _ =
                                        case answer
                                          of NONE => shout ": failed"
                                           | SOME (Error.ERROR _, _) => shout ": errored"
                                           | SOME (Error.OK _, _) => shout ": succeeded"
                                in  answer
                                end)
           end)


  fun bracketed p = left >> p <~> right  (* XXX TODO they need not match *)
  fun barSeparated p = many (reserved "|" >> p)
  fun commaSeparated p = curry op :: <$> p <*> many (reserved "," >> p)
  fun barSeparatedMulti p = curry op :: <$> p <*> many (reserved "|" >> p)


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

(* todo: 'reserved word used as name' error message *)

  val exp = P.fix (fn exp : A.exp P.producer => 
    (* 2nd arg to tree is D.exp to silence erroneous
        millet value polymorphism error lines. 
        Change back to 'a with no current semantic effect,
        but useful if trees ever become polymorphic again.  *)
    let         
    val tree : (D.exp, D.exp) D.tree P.producer = P.fix (fn tree =>
      let 
      val branch = P.fix (fn branch =>  
        P.pair <$> (bracketed (P.pair <$> vcon <~> comma <*> commaSeparated name)) 
                                               <~> rightarrow <*> tree)
      in
        curry3 A.TEST <$> word "test" >> name 
        <*> (barSeparatedMulti branch
             <|> barSeparated branch) 
             (* allows for ocaml-style *)
        <*> optional (word "else" >> tree)
    <|> curry4 A.LET_UNLESS <$> word "let" >> name <*> equalssign >> exp 
        <*> word "in" >> tree 
        <*> optional (word "unless" >> word "fail" >> rightarrow >> tree)
    <|> curry4 A.IF_THEN_ELSE <$> word "if" >> name <*> equalssign >> name 
       <*> word "then" >> tree <*> word "else" >> tree
    <|> word "fail" >> succeed A.FAIL
    <|> bracketed tree
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
        <|>        reserved "parse" >> exp >> P.succeed (A.DEF ("z", dname "z"))       
        <|>      (* debugging *)
        peek one         >> expected "definition"

  val parse = P.produce (curry fst <$> many def <*> eos)

end
