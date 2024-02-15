(* Representation of environments *)

(* You'll need to use the signature, 
    but don't need to look at the implementation *)

structure Env :> sig
  type name = string
  exception NotFound of name
  type 'a env
  val empty : 'a env
  val find : name * 'a env -> 'a  (* may raise NotFound *)
  val bind : name * 'a * 'a env -> 'a env
  val binds : 'a env * name -> bool

  val toString : ('a -> string) -> 'a env -> string
  val <+> : 'a env * 'a env -> 'a env  (* BPC, chap 5 *)
  val merge : ('a * 'a -> 'a) -> 'a env * 'a env -> 'a env
              (* resolver function *)
  val concat : 'a env list -> 'a env

end
  =
struct
  type name = string
  type 'a env = (name * 'a) list
  val empty = []

  fun eprint s = TextIO.output (TextIO.stdErr, s)

  exception NotFound of name
  fun not_found x =
    ( TextIO.output (TextIO.stdErr, concat ["Name not found: ", x, "\n"])
    ; raise NotFound x
    )
  fun find (name, []) = not_found name
    | find (name, (n, v)::tail) = if name = n then v else find (name, tail)
  fun bind (name, v, rho) = (name, v) :: rho

  fun binds ([], x) = false
    | binds ((x', _)::env, x) = x = x' orelse binds (env, x)

  (* to turn on environment debugging, change `val find_debug` to `val find` *)
  val find_debug = fn (x, rho) => find (x, rho)
    handle e =>
      ( app eprint ["Environment binds:"]
      ; app (fn (y, _) => app eprint [" ", y]) rho
      ; eprint "\n"
      ; raise e
      )
    
  fun toString elem rho =
    let fun binding (x, a) = concat [x, " |--> ", elem a]
    in  concat ["{ ", String.concatWith ", " (map binding rho), " }"]
    end


  infix 6 <+>
  fun pairs <+> pairs' = pairs' @ pairs

  fun merge resolver ([], rho) = rho
    | merge resolver ((n1, x)::xs, rho) = 
      if not (binds (rho, n1))
      then (n1, x)::(merge resolver (xs, rho))
      else (n1, resolver (x, find (n1, rho)))::(merge resolver (xs, rho))

  val concat = List.concat

end
  
