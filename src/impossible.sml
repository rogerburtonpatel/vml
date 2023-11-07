(* Handy functions for handling internal errors in our translator 
    (note this is not the same as the Error monad) *)

(* You'll need to use the signature *)

structure Impossible = struct
  exception Impossible of string
  fun impossible msg =
      let open TextIO
          fun shout s = (output (stdErr, s); flushOut stdErr) 
      in  app shout  ["Internal error: impossible ", msg, "\n"];
          raise (Impossible msg)
      end
  fun unimp msg = impossible (msg ^ " not implemented")
  fun exercise msg = impossible (msg ^ " is supposed to be an exercise")
end
