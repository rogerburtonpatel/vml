(* This is the universal forward translator. As you build the different VScheme 
    representations and the translations between them, you'll chain together 
    these translations here. It implements the actual translations *)

(* You'll get a partially complete version of this file, 
    which you'll need to complete *)

structure PPlusRun :> sig
  val run : TextIO.instream -> unit Error.error

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


  (**** Reader functions ****)

  val pplusOfFile : instream -> OldPPlus.def list error =
    lines                    (* line list *)
    >>> map PPlusLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> PPlusParse.parse       (* def list error *)    
    
  val run : instream -> unit Error.error =
    pplusOfFile
    >>> Error.map OldPPlus.runProg


end
