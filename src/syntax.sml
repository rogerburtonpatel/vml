structure Syntax :> sig 

  val delimiters : string 
  val vmreserved : string list 
  val ppreserved : string list 
  val dreserved : string list 
  val predefvcons : string list
  val doublequote  : string
  val backslash  : char
  val sbackslash : string

end 
  =
struct 

  val doublequote = Char.toString (chr 96)
  val backslash = (chr 92)
  val sbackslash = StringEscapes.backslash

(* todo: 

then d parser empty name list after vcon in test node fix

then specify delimiters

then better parser error messages

then make semantic tests
 *)

  val vmreserved = ["val", "=", doublequote, ".", "of", "|",
                  ",", sbackslash,
                  "->",
                  "if", "fi", "[]", "E"
                  (* debugging *)
                  (* , "parse", "tree" *)
                  ]
  val ppreserved = ["val", "=", "case", doublequote, ".", "of", "|", 
                  "->", "<-", "when", "_", ",", sbackslash
                  (* debugging *)
                  (* , "parse", "pat" *)
                  ]

  val dreserved = ["val", "=", doublequote, ".", "of", "|", 
                  ",", sbackslash,
                  "test", "->", "else", "let", "in", "unless", 
                  "if", "then", "fail", "[]"
                  (* debugging *)
                  (* , "parse", "tree" *)
                  ]

  val predefvcons = ["true", "false"]

  val delimiters = "()[]{};,.\\" 
end
