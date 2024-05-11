; val merge = \xs. \ys. 
;     case (P xs ys)
;       of (P NIL _) -> ys
;        | (P _ NIL) -> xs 
;        | (P (CONS x xr) (CONS y yr)) -> DOTS

fun feeling_draughty cellar key = 
  case key of (Brass | Copper), when cellar accepts key, 
                                (Beer (strength) | Wine (strength)) <- try(key, cellar), 
                                when strength > 20 -> "Good stuff!"
         | _ -> "Waste of time."


𝜆statuscode. (statuscode = Fine; Stand down | Launch the Missiles)

