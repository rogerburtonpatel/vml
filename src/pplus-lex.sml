structure PPlusLex : sig
  datatype bracket_shape = ROUND | SQUARE | CURLY

  datatype token
    = VCON    of string 
    | NAME    of string
    | LEFT  of bracket_shape
    | RIGHT of bracket_shape
    | RESERVED of string

  val token : token LexerCombinators.producer
  val tokenize_line : string -> token list Error.error
  val tokenString : token -> string 
  val leftString  : bracket_shape -> string
  val rightString : bracket_shape -> string
end
  = 
struct
  structure L = LexerCombinators

  (* wishing for Modula-style FROM IMPORT here ... *)
  infix 3 <*>      val op <*> = L.<*>
  infixr 4 <$>     val op <$> = L.<$>
  infix 1 <|>      val op <|> = L.<|>
  infix 6 <~> >>   val op <~> = L.<~>  val op >> = L.>>

  val succeed = L.succeed
  val curry = L.curry
  val id = L.id
  val fst = L.fst
  val snd = L.snd
  val many = L.many
  val many1 = L.many1
  val sat = L.sat
  val one = L.one
  val notFollowedBy = L.notFollowedBy
  val eos = L.eos
  val member = ListUtil.member
  


  fun char c = L.sat (L.eq c) one



  datatype bracket_shape = ROUND | SQUARE | CURLY

  datatype token
    = VCON    of string 
    | NAME    of string
    | LEFT  of bracket_shape
    | RIGHT of bracket_shape
    | RESERVED of string

  val doublequote = Char.toString (chr 96)
  val backslash = (chr 92)
  val sbackslash = StringEscapes.backslash

  fun bracketLexer token
    =  char #"(" >> succeed (LEFT  ROUND)
   <|> char #"[" >> succeed (LEFT  SQUARE)
   <|> char #"{" >> succeed (LEFT  CURLY)
   <|> char #")" >> succeed (RIGHT ROUND)
   <|> char #"]" >> succeed (RIGHT SQUARE)
   <|> char #"}" >> succeed (RIGHT CURLY)
   <|> token


  type lexer = token L.producer


  fun intFromChars (#"-" :: cs) = 
        Error.map Int.~ (intFromChars cs)  (* XXX todo overflow *)
    | intFromChars cs =
        (Error.OK o valOf o Int.fromString o implode) cs
        handle Overflow =>
          Error.ERROR "this interpreter can't read arbitrarily large integers"

  fun intChars isDelim = 
    (curry (op ::) <$> char #"-"  <|> succeed id) <*>
      many1 (sat Char.isDigit one) <~> notFollowedBy (sat (not o isDelim) one)

  fun intToken isDelim =
    L.check (intFromChars <$> intChars isDelim)

  fun isMyDelim c = Char.isSpace c orelse Char.contains Syntax.delimiters c



  val reserved = Syntax.ppreserved  
  val predefvcons = Syntax.predefvcons

  fun atom x =
    if member x reserved then
        RESERVED x
    else if Char.isUpper (String.sub (x, 0)) orelse (member x predefvcons) then
        VCON x
    else
        NAME x

  val whitespace = many (sat Char.isSpace one)

  fun barf c =
    let val msg = "invalid initial character '" ^ Char.toCString c ^ "'"
    in  Error.ERROR msg
    end

  val comment = char #";" >> many one

  fun optional p = SOME <$> p <|> succeed NONE

  fun onereserved c = char c >> succeed (RESERVED (Char.toString c))

  val reserveddelim =   onereserved #"'"
                  <|> onereserved #"."
                  <|> onereserved #","
                  <|> char backslash >> succeed (RESERVED sbackslash)

  val token =
    whitespace >>
    optional comment >>
    bracketLexer   (  reserveddelim
                  <|> (atom o implode) <$> many1 (sat (not o isMyDelim) one)
                  <|> L.check (barf <$> one)
                   )

  val tokenize_line =
    L.produce (many token <~> whitespace <~> optional comment) o explode
    : string -> token list Error.error


  fun leftString ROUND  = "("
    | leftString SQUARE = "["
    | leftString CURLY  = "{"
  fun rightString ROUND  = ")"
    | rightString SQUARE = "]"
    | rightString CURLY = "}"


  fun tokenString (VCON n)     = "vcon " ^ n
    | tokenString (NAME n)     = "name " ^ n
    | tokenString (LEFT b)     = leftString b
    | tokenString (RIGHT b)    = rightString b
    | tokenString (RESERVED s) = "reserved word " ^ s

end

