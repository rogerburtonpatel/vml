(* Utility functions for handling text input and output for UFT *)

(* You can ignore this *)

structure IOUtil :> sig
  val lines  : TextIO.instream -> string list
  val output : TextIO.outstream -> string -> unit
  val outln  : TextIO.outstream -> string -> unit   (* adds newline *)
end
  =
struct
  fun lines fd =
    let fun go prev' =
          case TextIO.inputLine fd
            of NONE => rev prev'
             | SOME l => go (l :: prev')
    in  go []
    end

  fun output out s = TextIO.output (out, s)
  fun outln out s = app (output out) [s, "\n"]
end
  