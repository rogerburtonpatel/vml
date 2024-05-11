val gt = \f. \s. case (P f s) of (P ONEHUNDREDONE ONEHUNDRED) -> true | _ -> false
val x = case SQUARE(ONEHUNDREDONE) of SQUARE(n, when (gt n) ONEHUNDRED) -> print OK | _  -> print NOTOK 