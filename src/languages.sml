(* All the languages we'll eventually translate, 
    and the order in which they can be translated *)

(* You'll need to use the signature, 
    but don't need to look at the implementation *)

structure Languages :> sig
  datatype language = PPLUS | VMINUS_ALPHA | VMINUS_SIMPLE | VMINUS_ARROW | AST_P | AST_V | D
  val table : { language : language, short : string, description : string } list

  val find : string -> language option
  val description : language -> string
  val le : language * language -> bool   (* determines forward *)
end
  =
struct
  datatype language = PPLUS | VMINUS_ALPHA | VMINUS_SIMPLE | VMINUS_ARROW | AST_P | AST_V | D

  fun inject (l, s, d) = { language = l, short = s, description = d }

  val table = map inject
    [ (PPLUS,  "pp",  "P+ concrete syntax")
    , (PPLUS,  "pplus",  "P+ concrete syntax")
    , (VMINUS_ALPHA,  "vma",  "V- with alpha concrete syntax")
    , (VMINUS_ALPHA, "vminus",  "V- simple concrete syntax")
    , (VMINUS_SIMPLE, "vms",  "V- simple concrete syntax")
    , (VMINUS_ARROW,  "vmr",  "V- with arrow concrete syntax")
    , (AST_P, "astp", "AST for P+")
    , (AST_V,  "astv",  "AST for V-")
    , (D,  "d",  "decision-tree language")
    ]


  fun find x = Option.map #language (List.find (fn r => #short r = x) table)

  fun entry lang = Option.valOf (List.find (fn r => #language r = lang) table)

  val description = #description o entry

  fun pred AST_P  = SOME PPLUS
    | pred AST_V  = SOME VMINUS_ALPHA
    | pred PPLUS  = NONE
    | pred VMINUS_ALPHA  = SOME PPLUS
    | pred VMINUS_SIMPLE = SOME PPLUS
    | pred VMINUS_ARROW  = SOME PPLUS
    | pred D             = SOME VMINUS_SIMPLE

  fun le (from, to) =
        from = to orelse (case pred to of SOME x => le (from, x) | NONE => false)
end
