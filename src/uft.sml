(* This is the universal forward translator. As you build the different VScheme 
    representations and the translations between them, you'll chain together 
    these translations here. It implements the actual translations *)

(* You'll get a partially complete version of this file, 
    which you'll need to complete *)

structure UFT :> sig
  type language = Languages.language
  exception NotForward of language * language
  val translate : language * language -> TextIO.instream * TextIO.outstream -> unit Error.error

(*@ false *)
  (* useful for type checking paper examples *)
  type 'a error = 'a Error.error

(*@ true *)
end
  =
struct

  (**** I/O functions and types ****)

  type instream = TextIO.instream
  val lines  = IOUtil.lines : instream -> string list
  val output = IOUtil.output 
  val outln  = IOUtil.outln


  (**** function composition, including errors ****)

  type 'a error = 'a Error.error

  infix 0 >>> >=>
  fun f >>> g = fn x => g (f x)         (* function composition, Elm style *)
  val op >=> = Error.>=>

  fun liftMap f xs = Error.list (map f xs)  (* liftMap f == map f >>> Error.list *)

  exception Backward  (* for internal use only *)
                      (* raised if someone commands a backward translation *)

  datatype language = datatype Languages.language (* imports value constructors *)
  exception NoTranslationTo of language  (* used internally *)

  (**** Reader functions ****)

  val pplusOfFile : instream -> FinalPPlus.def list error =
    lines                    (* line list *)
    >>> map PPlusLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> PPlusParse.parse       (* def list error *)    
    
  val vmsOfPP : FinalPPlus.def list -> FinalVMinus.def list =
  map VMofPP.def

  (* val dOfVMS : VMinusSimple.def list ->  =
  map Translation.vmSimpleOfPdef *)


  fun AST_P_of PPLUS = pplusOfFile
    | AST_P_of  _    = raise Backward

  fun VMINUS_SIMPLE_of PPLUS = pplusOfFile >>> Error.map vmsOfPP
    | VMINUS_SIMPLE_of  _    = raise Backward


  fun D_of _  = Impossible.unimp "translate to a decision tree"


  fun emitAST_P outfile =
    app (fn d => ( TextIO.output(outfile, FinalPPlus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  fun emitVMS outfile =
    app (fn d => ( TextIO.output(outfile, FinalVMinus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  (**** The Universal Forward Translator ****)

  exception NotForward of language * language  (* for external consumption *)

  fun translate (inLang, outLang) (infile, outfile) =
    (case outLang
       of AST_P         => AST_P_of inLang >>> Error.map (emitAST_P outfile)
        | VMINUS_SIMPLE => VMINUS_SIMPLE_of inLang >>> Error.map (emitVMS outfile)
        | D => D_of
        | _  => raise NoTranslationTo outLang
    ) infile
    handle Backward => 
    let val () = IOUtil.eprint "backward" in 
    raise NotForward (inLang, outLang) end 
         | NoTranslationTo outLang => 
    let val () = IOUtil.eprint "notran" in 
         
         raise NotForward (inLang, outLang) end


end
