(* All the languages and the order in which they can be translated *)

structure Languages :> sig
  datatype language = PPLUS | VMINUS | D | Eval
  val table : { language : language, short : string, description : string } list

  val find : string -> language option
  val description : language -> string
  val le : language * language -> bool   (* determines forward *)
end
  =
struct
  datatype language = PPLUS | VMINUS | D | Eval

  fun inject (l, s, d) = { language = l, short = s, description = d }

  val table = map inject
    [ (PPLUS,  "pp",  "P+ concrete syntax")
    , (PPLUS,  "pplus",  "P+ concrete syntax")
    , (VMINUS, "vm",  "V- concrete syntax")
    , (VMINUS, "vminus",  "V- concrete syntax")
    (* , (VMINUS_ALPHA,  "vma",  "V- with alpha concrete syntax")
    , (VMINUS_ALPHA, "vminus",  "V- simple concrete syntax")
    , (VMINUS_ARROW,  "vmr",  "V- with arrow concrete syntax")
    , (AST_P, "astp", "AST for P+")
    , (AST_V,  "astv",  "AST for V-") *)
    , (D,  "d",  "decision-tree language")
    , (Eval,  "eval",  "language evaluator for P+ and V-")
    ]


  fun find x = Option.map #language (List.find (fn r => #short r = x) table)

  fun entry lang = Option.valOf (List.find (fn r => #language r = lang) table)

  val description = #description o entry

  fun pred VMINUS        = SOME PPLUS
    | pred D             = SOME VMINUS
    | pred PPLUS         = NONE
    | pred Eval          = Impossible.impossible "bug in languages"

  fun le (from, to) =
        from = to   orelse 
        to   = Eval orelse
        (case pred to of SOME x => le (from, x) | NONE => false)
end
