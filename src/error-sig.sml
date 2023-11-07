(* Operations for dealing with the Error monad *)

(* You'll need to use this signature 
   but you don't need to know how things are implemented *)

signature ERROR = sig
  datatype 'a error = OK of 'a | ERROR of string

  (* the error monad as applicative functor *)
  val succeed : 'a -> 'a error
  val <*>  : ('a -> 'b) error * 'a error -> 'b error
  val <$>  : ('a -> 'b) * 'a error -> 'b error

  (* some monad/functor operations *)
  val map : ('a -> 'b) -> ('a error -> 'b error)   (* Curried form of <$> *)
  val join : 'a error error -> 'a error
  val >>= : 'a error * ('a -> 'b error) -> 'b error

  (* Kleisli composition *)
  val >=> : ('a -> 'b error) * ('b -> 'c error) -> ('a -> 'c error)

  (* list functions *)
  val list : 'a error list -> 'a list error
  val mapList : ('a -> 'b error) -> ('a list -> 'b list error)
    (* law: mapList f xs = list (List.map f xs) *)

  (* list error out of option *)
  val option : 'a error option -> 'a option error
end
