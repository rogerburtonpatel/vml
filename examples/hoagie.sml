

fun princeton_snacks card store free_time = 
    case store of 
        (Hoagie_Haven hours | PJs_Pancake_House hours), 
        when time_matches (hours, free_time), 
        (USD d when d > 10 | PawPoints p when p > 100) <- try (card, store) 
        -> "Rah rah rah tiger tiger tiger"
    | _ -> "Fohgettaboutit"

val princeton_snacks = λ card store free_time. 
    ∃ hours p res. store = (Hoagie_Haven hours | PJs_Pancake_House hours); 
        time_matches (hours, free_time); 
        res = try (card, store); res = (USD d; d > 10 | PawPoints p; p > 100) 
        -> "Rah rah rah tiger tiger tiger"
    [] -> "Fohgettaboutit"


fun princeton_snacktime card store free_time = 
    case store of 
      Hoagie_Haven hours -> 
        if time_matches (hours, free_time)
        then case try (card, store) of 
                USD d -> 
                if d > 10 
                then "Rah rah rah tiger tiger tiger"
                else "Fohgettaboutit"
                PawPoints p -> 
                if p > 100
                then "Rah rah rah tiger tiger tiger"
                else "Fohgettaboutit"
        else "Fohgettaboutit"
        PJs_Pancake_House hours -> 
        if time_matches (hours, free_time)
        then case try (card, store) of 
                USD d -> 
                if d > 10 
                then "Rah rah rah tiger tiger tiger"
                else "Fohgettaboutit"
                PawPoints p -> 
                if p > 100
                then "Rah rah rah tiger tiger tiger"
                else "Fohgettaboutit"
        else "Fohgettaboutit"


case ⟿ if fi 