(* This is the universal forward translator. As you build the different VScheme 
    representations and the translations between them, you'll chain together 
    these translations here. It implements the actual translations *)

(* You'll get a partially complete version of this file, 
    which you'll need to complete *)

(* Formerly UFT *)
structure Dtran :> sig
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

  val pplusOfFile : instream -> PPlus.def list error =
    lines                    (* line list *)
    >>> map PPlusLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> PPlusParse.parse       (* def list error *)    

  val vminusOfFile : instream -> VMinus.def list error =
    lines                    (* line list *)
    >>> map VMinusLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> VMinusParse.parse       (* def list error *)    



  val vmofPP : PPlus.def list -> VMinus.def list = 
    map VMofPP.def
  
  val dofVM : VMinus.def list -> D.def list = 
    map DofVminus.def

  fun PPLUS_of PPLUS = pplusOfFile
    | PPLUS_of  _    = raise Backward

  fun VMINUS_of PPLUS = pplusOfFile >>> Error.map vmofPP
    | VMINUS_of  _    = raise Backward

  fun Eval_of PPLUS  = pplusOfFile >>> Error.map PPlus.runProg
    | Eval_of VMINUS = Impossible.unimp "eval vminus"
    | Eval_of D      = Impossible.impossible "D is evaluated as Standard ML" (* XXX TODO really wants better error handling *)
    | Eval_of Eval   = raise Backward


  fun D_of _  = Impossible.unimp "match compiler"
  (* vminusOfFile >>> Error.map dofVM *)


  fun emitPPLUS outfile =
    app (fn d => ( TextIO.output(outfile, PPlus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  fun emitVMINUS outfile =
    app (fn d => ( TextIO.output(outfile, VMinus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  (**** The Universal Forward Translator ****)

  exception NotForward of language * language  (* for external consumption *)

  fun translate (inLang, outLang) (infile, outfile) =
    (case outLang
       of PPLUS         => PPLUS_of inLang >>> Error.map (emitPPLUS outfile)
        | VMINUS        => VMINUS_of inLang >>> Error.map (emitVMINUS outfile)
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
