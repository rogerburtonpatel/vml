structure FreshName :> sig 
  val freshNameGen : unit -> string
  (* returns a fresh name, globally unique from any prior generated *)
  val freshNameGenGen : unit -> (unit -> string)
  (* returns a fresh name generator *)
  val genOfList : (unit -> string) -> 'a list -> string list
  (* given a fresh name function, returns a list of fresh names for each xs *)
end 
  =
struct 
  val globalcounter = ref 0

   fun freshNameGen () = (globalcounter := !globalcounter + 1 ; 
                          "..x" ^ Int.toString (!globalcounter))

  fun freshNameGenGen () = 
    let val counter = ref 0 
    in fn () => (counter := !counter + 1 ; "..x" ^ Int.toString (!counter))
    end 

  fun genOfList (gen : (unit -> string)) xs = map (fn _ => gen ()) xs

end
