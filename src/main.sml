(*  Implements the command line and consults the Languages 
    table (languages.sml) to see what translation is called for. *)

(* The code is mostly error handling, and you won't need to look at it. *)

structure Main = struct

  fun eprint s = TextIO.output (TextIO.stdErr, s)
  fun die s = (app eprint [s, "\n"]; OS.Process.exit OS.Process.failure)

  val arg0 = CommandLine.name ()

  fun spaces n = implode (List.tabulate (n, fn _ => #" "))
  fun pad n s = s ^ spaces (Int.max (0, n - size s))

(* 
  fun usage () =
    ( app eprint ["Usage:\n  ", arg0, " <from>-<to> [file]\n"]
    ; app eprint ["where <from> and <to> are one of these languages:\n"]
    ; app (fn r => app eprint ["  ", pad 3 (#short r), "  ", #description r, "\n"])
          Languages.table
    ; OS.Process.exit OS.Process.failure
    )

  
  fun run f stream = f (stream, TextIO.stdOut)
  fun errorApp f [] = Error.OK ()
    | errorApp f (x::xs) = Error.>>= (f x, fn _ => errorApp f xs)


  fun openIn "-" = TextIO.stdIn
    | openIn path = TextIO.openIn path

  fun tx f []    = run f TextIO.stdIn
    | tx f paths = errorApp (run f o openIn) paths
 
  val _ = tx : (TextIO.instream * TextIO.outstream -> unit Error.error) ->
               string list -> unit Error.error
    
  fun translationOf spec =
    case String.fields (fn c => c = #"-") spec
      of [from, to] =>
           (case (Languages.find from, Languages.find to)
              of (SOME from, SOME to) => UFT.translate (from, to)
               | (NONE, _) => die ("I don't recognize language `" ^ from ^ "`")
               | _ => die ("I don't recognize language `" ^ to ^ "`"))
       | _ => usage()
                   
  fun reportAndExit (Error.OK ()) = OS.Process.exit OS.Process.success
    | reportAndExit (Error.ERROR msg) = die msg

  val _ =
    let val argv = CommandLine.arguments ()
    in  case argv
          of [] => usage ()
           | spec :: args => reportAndExit (tx (translationOf spec) args)
    end
    handle UFT.NotForward (from, to) =>
      (app eprint [arg0, ": Uh-oh!\n  I don't know how to translate ",
                   Languages.description from, "\n  to ",
                   Languages.description to, "\n"]
      ; OS.Process.exit OS.Process.failure
      ) *)

end
