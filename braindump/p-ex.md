SML: 
            | NAME n => if not (Env.binds (rho, n))
                        orelse not (isSome (Env.find (n, rho)))
                        then raise NameNotBound n 
                        else valOf (Env.find (n, rho))
Other SML: 
            | NAME n => if (Env.binds (rho, n))
                        then case Env.find (n, rho) of SOME v => v 
                                | NONE => raise NameNotBound n
                        else raise NameNotBound n 


PPLUS: 
| NAME n -> when Env.binds (rho, n), SOME v <- Env.find (n, rho) -> v
| NAME n -> raise NameNotBound n

VMINUS: 
[] E n. x = NAME n; Env.binds(rho, n); SOME v = Env.find (n, rho); -> v
[] E n. x = NAME n; -> raise NameNotBound n

VERSE: 
E n. x = NAME n; if (Env.binds(rho, n); E v. SOME v = Env.find (n, rho)) then v
                    else raise NameNotBound n

E n. x = NAME n; if (E v. SOME v = Env.find (n, rho)) then v
                    else raise NameNotBound n

VERSE DESUGARED: 
E n. x = NAME n; one {one {Env.binds(rho, n) | E _x. SOME _x = Env.find (n, rho)}; raise NameNotBound n | E x2. SOME x2 = Env.find (n, rho); x2} 

bindwith in vminus.sml, first block with ifs
  fun bindWith (rho : 'a lvar_env) (e : 'a exp) (v : 'a value) = 
    case (e, v) of 
      (NAME n, v) => 
        let val nval = valIn rho n 
        in if isSome nval 
           then if (eqval ((valOf nval), v)) then OK rho else REJ
           else OK (Env.bind (n, SOME v, rho))
        end 
    | ... 

bindwith in vminus.sml, first block with ifs
  fun bindWith (rho : 'a lvar_env) (e : 'a exp) (v : 'a value) = 
    case (e, v) of 
      (NAME n, v) => 
        (case valIn rho n 
          of SOME nval => 
            if (eqval (nval, v)) then OK rho else REJ
          | NONE => (Env.bind (n, SOME v, rho)))
    | ... 

VERSE: 

bindWith = \rho e v. 
  one {E n, v. (e, v) = (NAME n, v); 
       E nval. one {SOME nval = valIn rho n; 
                    if eqVal (nval, v) then OK rho else REJ
                    | OK Env.bind(n, SOME v, rho)}
    | ...
  }

Something where VMINUS is nicer than PPLUS: 

no scrutinee. 

if 
[] property1; property2 input -> if property3 input -> go_ahead
                                 [] property4 input -> cower fi
fi 

Another example where, after properties, make bindings 

let showImportantNotification n =
  match n with 
    Email(sender, _, _) if importantPeopleInfo.contains(sender) =>
      "You got an email from special someone!"
    SMS(number, _) if importantPeopleInfo.contains(number) =>
      "You got an SMS from special someone!"
    case other =>
      showNotification(other)


let showImportantNotification importantPeopleInfo n =
  match n with 
    | Email(sender, _, _) when contains (importantPeopleInfo, sender) ->
      "You got an email from special someone!"
    | SMS(number, _) when importantPeopleInfo.contains(number) ->
      "You got an SMS from special someone!"
    | other -> showNotification(other)

edited: 

let exclaimTall sh =
  match sh with 
    | SQUARE s when s > 100.0 ->
            "Wow! That's a tall square!"
    | TRIANGLE(w, h) when h> 100.0 ->
            "Goodness! Towering triangle!"
    | TRAPEZOID (b1, b2, h) when h > 100.0 -> 
            "Zounds! Tremendous trapezoid!"
    | _ ->  "Your shape is small." 

let exclaimTall sh =
  match sh with 
    | SQUARE s -> if s > 100.0 
                  then "Wow! That's a tall square!"
                  else "Your shape is small." 
    | TRIANGLE(w, h) -> 
                  if h > 100.0 
                  then "Goodness! Towering triangle!"
                  else "Your shape is small." 
    | TRAPEZOID (b1, b2, h) -> 
                  if h > 100.0
                  then "Zounds! Tremendous trapezoid!"
                  else "Your shape is small." 
    | _ -> "Your shape is small." 


(fn g => case g of V.EQN eqn => 
                    if cond
                    then goodResult 
                    else badResult
                  | _ => goodResult)

            | n      => if not (binds rho n)
                        then raise NameNotBound n
                        else (find n, rho)


                        orelse not (isSome (find n rho))