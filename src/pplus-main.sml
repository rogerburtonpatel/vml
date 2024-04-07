structure Main = struct

  fun eprint s = TextIO.output (TextIO.stdErr, s)
  fun die s = (app eprint [s, "\n"]; OS.Process.exit OS.Process.failure)

  val arg0 = CommandLine.name ()

  fun spaces n = implode (List.tabulate (n, fn _ => #" "))
  fun pad n s = s ^ spaces (Int.max (0, n - size s))

  val () = Unit.reportWhenFailures ()

  type instream = TextIO.instream
  val lines  = IOUtil.lines : instream -> string list
  val output = IOUtil.output 
  val outln  = IOUtil.outln


  (**** function composition, including errors ****)

  type 'a error = 'a Error.error

  infix 0 >>> >=>
  fun f >>> g = fn x => g (f x)         (* function composition, Elm style *)
  val op >=> = Error.>=>

  val pplusOfFile : instream -> PPlus.def list error =
    lines                    (* line list *)
    >>> map PPlusLex.tokenize_line  (* token list error list *)
    >>> Error.list           (* token list list error *)
    >>> Error.map List.concat (* token list error *)
    >=> PPlusParse.parse       (* def list error *)    

  fun runProg (instream, _) = Error.map PPlus.runProg (pplusOfFile instream) 

  fun run f stream = f (stream, TextIO.stdOut)
  fun errorApp f [] = Error.OK ()
    | errorApp f (x::xs) = Error.>>= (f x, fn _ => errorApp f xs)


  fun openIn "-" = TextIO.stdIn
    | openIn path = TextIO.openIn path

  fun tx f []    = run f TextIO.stdIn
    | tx f paths = errorApp (run f o openIn) paths
 
  val _ = tx : (TextIO.instream * TextIO.outstream -> unit Error.error) ->
               string list -> unit Error.error
    

  fun reportAndExit (Error.OK ()) = OS.Process.exit OS.Process.success
    | reportAndExit (Error.ERROR msg) = die msg


  val _ =
    let val argv = CommandLine.arguments ()
    in  reportAndExit (tx (runProg) argv)
    end
end
