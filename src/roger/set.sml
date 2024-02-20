(* Representation of sets *)

(* You'll need to use the signature, 
    but you don't need to look at the implementation *)

signature SET = sig
  type 'a set
  val empty : 'a set
  val member : ''a * ''a set -> bool
  val insert : ''a * ''a set -> ''a set
  val diff : ''a set * ''a set -> ''a set
  val elems : 'a set -> 'a list
  val ofList : ''a list -> ''a set
  val fromList : ''a list -> ''a set
  val singleton : ''a -> ''a set

  val union' : ''a set list -> ''a set  (* union of a list of sets *)
end


structure Set :> SET
  =
struct
  type 'a set = 'a list
  val empty = []
  fun member (x, s) = 
    List.exists (fn y => y = x) s
  fun insert (x, ys) = 
    if member (x, ys) then ys else x::ys
  fun union (xs, ys) = foldr insert ys xs
  fun union' ss = foldr union empty ss

  fun inter (xs, ys) =
    List.filter (fn x => member (x, ys)) xs
  fun diff  (xs, ys) = 
    List.filter (fn x => not (member (x, ys))) xs

  fun elems xs = xs
  fun ofList xs = foldr insert empty xs
  val fromList = ofList

  fun singleton x = [x]
end
