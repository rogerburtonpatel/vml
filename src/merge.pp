val merge = \xs. \ys. 
    case (P xs ys)
      of (P NIL _) -> ys
       | (P _ NIL) -> xs 
       | (P (CONS x xr) (CONS y yr)) -> DOTS