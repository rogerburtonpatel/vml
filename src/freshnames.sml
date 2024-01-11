structure FreshName :> sig 
val freshname : unit -> string
end 
  =
struct 

  val counter = ref 0

  fun freshname () = (counter := !counter + 1 ; "__x" ^ Int.toString (!counter))

end
