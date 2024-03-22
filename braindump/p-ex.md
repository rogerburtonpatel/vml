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
