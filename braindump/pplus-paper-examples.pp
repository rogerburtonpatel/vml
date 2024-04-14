val exclaimTall = \sh.
  case sh of Square s, when (> s) 100 -> 
            Wow! That's A Tall Square!  
    | Triangle w h, when (> s) 100 ->
            Goodness! Towering T10riangle!
    | Trapezoid b1 b2 h, when (> s) 100 -> 
            Zounds! Tremendous Trapezoid!
    | _ ->  Your Shape Is Small
  
val tripleLookup = \ rho. \x.
  case x of 
    Some w <- (lookup rho) x
  , Some y <- (lookup rho) w
  , Some z <- (lookup rho) y -> z
  | _ -> handleFailure x

val game_of_token = \t. 
  case t of  
    BattlePass f  | (ChugJug f | TomatoTown f) -> P (Fortnite f)
  | HuntersMark f | SawCleaver f               -> P (Bloodborne ((* 2) f))
  | MoghLordOfBlood f | PreatorRykard f        -> P (EldenRing ((* 3) f))
  | _                                          -> P (Irrelevant 0)