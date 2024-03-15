structure ListUtil :> sig  
  (* missing from mosml *)
  val mapi : (int * 'a -> 'b) -> 'a list -> 'b list
  val concatMap : ('a -> 'b list) -> ('a list -> 'b list)
  val foldri : (int * 'a * 'b -> 'b) -> 'b -> 'a list -> 'b
  val join  : ('a -> string)  -> string -> 'a list -> string
end
  =
struct
  fun mapi f xs =
    let fun go k [] = []
          | go k (x::xs) = f (k, x) :: go (k + 1) xs
    in  go 0 xs
    end

  fun concatMap f xs = foldr (fn (x, tail) => f x @ tail) [] xs

  fun foldri f z =
    let fun go k z [] = z
          | go k z (x :: xs) = f (k, x, go (k + 1) z xs)
    in  go 0 z
    end

  fun join f delim xs = 
      let fun join' [] = ""
            | join' (x::nil) = f x ^ "]"
            | join' (x::xr)  = f x ^ delim ^ join f delim xs
       in "[" ^ join' xs
       end 

  fun flip f x y = f y x
  fun uflip f (x, y) = f (y, x)

  fun curry f x y = f (x, y)
  fun uncurry f (x, y) = f x y 


  fun join f delim [] = ""
    | join f delim (x::xs) = (f x) ^ (foldr (fn (s, acc) => 
                                              delim ^ (f s) ^ acc) "" xs)



end