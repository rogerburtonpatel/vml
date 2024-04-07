structure LexerCombinators =
  MkListProducer (val species = "lexer"
                  type input = char
                  val show = StringEscapes.quote o implode
                 )

