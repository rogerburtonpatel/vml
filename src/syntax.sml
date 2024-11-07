structure Syntax :> sig 

  val vmdelimiters : string 
  val ppdelimiters : string 
  val ddelimiters : string 
  val vmreserved : string list 
  val ppreserved : string list 
  val dreserved : string list 
  val predefvcons : string list
  val doublequote  : string
  val backslash  : char
  val sbackslash : string
  val rightarrow : string

end 
  =
struct 

  val doublequote = Char.toString (chr 96)
  val backslash = (chr 92)
  val sbackslash = StringEscapes.backslash

  val lambda = "λ"
  val exists = "∃"
  val dot = "."
  val valkw = "val"
  val equals = "="
  val rightarrow = "->"
  val bar = "|"
  
  val corereserved = [
    valkw, 
    equals,
    lambda, 
    sbackslash,
    dot, 
    doublequote
  ]

  val vmreserved = ["if", "fi", "[]", "E", exists, 
                  bar, rightarrow
                  (* debugging *)
                  (* , "parse", "guard" *)
                  ] @ corereserved
  val ppreserved = ["case", "of", 
                  "<-", "when", "_", ",",
                  bar, rightarrow
                  (* debugging *)
                  (* , "parse", "pat" *)
                  ] @ corereserved

  val dreserved = ["test", "else", "let", "in", "unless", 
                  "if", "then", "fail", "[]",
                  bar, rightarrow
                  (* debugging *)
                  (* , "parse", "tree" *)
                  ] @ corereserved

  val predefvcons = ["true", "false"]

  val vmdelimiters = "()[]{};.\\" 
  val ppdelimiters = "()[]{},.\\" 
  val ddelimiters = "()[]{},.\\" 
end
