structure FreshName :> sig 
  val freshNameGenGen : unit -> (unit -> string)
  (* returns a fresh name generator *)
end 
  =
struct 

  fun freshNameGenGen () = 
    let val counter = ref 0 
    in fn () => (counter := !counter + 1 ; "__x" ^ Int.toString (!counter))
    end 

end
