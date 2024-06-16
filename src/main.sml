(*  Implements the command line and consults the Languages 
    table (languages.sml) to see what translation is called for. *)

(* The code is mostly error handling, and you won't need to look at it. *)

structure Main = struct

  infixr 0 $
  fun f $ g = f g

  fun eprint s = TextIO.output (TextIO.stdErr, s)
  fun die s = (app eprint [s, "\n"]; OS.Process.exit OS.Process.failure)

  val arg0 = Path.file $ CommandLine.name ()

  fun spaces n = implode (List.tabulate (n, fn _ => #" "))
  fun pad n s = s ^ spaces (Int.max (0, n - size s))

  val () = Unit.reportWhenFailures ()

  fun maxpositive is = foldl Int.max 0 is

  val padsize = maxpositive $ map (fn r => size (#short r)) Languages.table

  fun usage () =
    ( app eprint ["Usage:\n  ", arg0, " <from>-<to> [-o outfile] [infile]\n"]
    ; app eprint ["where <from> and <to> are one of these languages:\n"]
    ; app (fn r => app eprint ["  ", pad padsize (#short r), "  ", #description r, "\n"])
          Languages.table
    ; OS.Process.exit OS.Process.failure
    )

  fun run f NONE instream = f (instream, TextIO.stdOut)
    | run f (SOME outfile) instream  = 
            let val outstream = TextIO.openAppend outfile
            in f (instream, outstream) before TextIO.closeOut outstream
            end


  fun errorApp f [] = Error.OK ()
    | errorApp f (x::xs) = Error.>>= (f x, fn _ => errorApp f xs)


  fun openIn "-" = TextIO.stdIn
    | openIn path = TextIO.openIn path

  fun tx f out []    = run f out TextIO.stdIn
    | tx f out paths = errorApp (run f out o openIn) paths
 
  val _ = tx : (TextIO.instream * TextIO.outstream -> unit Error.error) ->
               string option -> string list -> unit Error.error
    
  fun translationOf spec =
    case String.fields (fn c => c = #"-") spec
      of [from, to] =>
           (case (Languages.find from, Languages.find to)
              of (SOME from, SOME to) => Dtran.translate (from, to)
               | (NONE, _) => die ("I don't recognize language `" ^ from ^ "`")
               | _ => die ("I don't recognize language `" ^ to ^ "`"))
       | _ => usage()

  fun reportAndExit (Error.OK ()) = OS.Process.exit OS.Process.success
    | reportAndExit (Error.ERROR msg) = die msg

  val _ =
    let val argv = CommandLine.arguments ()
    in  case argv
          of [] => usage ()
           | spec :: "-o" :: outfile :: args => reportAndExit (tx (translationOf spec) (SOME outfile) args)
           | spec :: args => reportAndExit (tx (translationOf spec) NONE args)
    end
    handle Dtran.NotForward (from, to) =>
      (app eprint [arg0, ": Uh-oh!\n  I don't know how to translate ",
                   Languages.description from, "\n  to ",
                   Languages.description to, "\n"]
      ; OS.Process.exit OS.Process.failure
      )
        | Dtran.Can'tDigest Languages.D => 
          (app eprint [arg0, ": Uh-oh!\n  I can't parse or evaluate D yet.\n"]
      ; OS.Process.exit OS.Process.failure
      )
        | Dtran.Can'tDigest Languages.Eval => 
          (app eprint [arg0, ": You know better!\n", 
                             "  eval can only be used after the \"-\"!\n"]
      ; OS.Process.exit OS.Process.failure
      )
end
