(* Formerly UFT *)
structure Dtran :> sig
  type language = Languages.language
  exception NotForward of language * language
  exception Can'tDigest of language
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

  val dOfFile : instream -> D.def list error =
    lines                    (* line list *)
    >>> map DLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> DParse.parse       (* def list error *)

  (* For bad use of eval, attempting to read in D, etc. *)
  exception Can'tDigest of language

  val vmofPP : PPlus.def list -> VMinus.def list = 
    map VMofPP.def

  val dofVM : VMinus.def list -> D.def list = 
    DofVminus.defs

  fun PPLUS_of PPLUS = pplusOfFile
    | PPLUS_of  _    = raise Backward

  fun VMINUS_of PPLUS  = pplusOfFile >>> Error.map vmofPP
    | VMINUS_of VMINUS = vminusOfFile
    | VMINUS_of  _     = raise Backward

  fun runProg PPLUS  = pplusOfFile  >>> Error.map PPlus.runProg
    | runProg VMINUS = vminusOfFile >>> Error.map VMinus.runProg
    | runProg D      = raise Can'tDigest D
    | runProg Eval   = raise Can'tDigest Eval

  fun D_of VMINUS  = vminusOfFile    >>> Error.map dofVM
    | D_of PPLUS   = VMINUS_of PPLUS >>> Error.map dofVM (* the composition *)
    | D_of D       = dOfFile
    | D_of _       = raise Backward
  


  fun emitPPLUS outfile =
    app (fn d => ( TextIO.output(outfile, PPlus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  fun emitVMINUS outfile =
    app (fn d => ( TextIO.output(outfile, VMinus.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  fun emitD outfile =
    app (fn d => ( TextIO.output(outfile, D.defString d)
                 ; TextIO.output(outfile, "\n")
                 ))

  fun curry f x y = f (x, y)

  (* old version, also works *)
  fun emitD outfile = D.progString >>> (fn p => p ^ "\n") >>> curry TextIO.output outfile
  
  (**** The Universal Forward Translator ****)

  exception NotForward of language * language  (* for external consumption *)

  fun translate (Eval, _) _ = raise Can'tDigest Eval 
    | translate (inLang, outLang) (infile, outfile) =
    (case outLang
       of PPLUS  => PPLUS_of  inLang >>> Error.map (emitPPLUS outfile)
        | VMINUS => VMINUS_of inLang >>> Error.map (emitVMINUS outfile)
        | D      => D_of      inLang >>> 
        (* Error.map D.runProg *)
        Error.map (emitD outfile)
        | Eval   => runProg inLang
    ) infile
    handle Backward                => raise NotForward (inLang, outLang)
         | NoTranslationTo outLang => raise NotForward (inLang, outLang)
         

end
