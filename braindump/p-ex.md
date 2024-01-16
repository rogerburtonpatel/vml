            | NAME n => if not (Env.binds (rho, n))
                        orelse not (isSome (Env.find (n, rho)))
                        then raise NameNotBound n 
                        else valOf (Env.find (n, rho))

                        ugly. without valof especially; dup branches. 
                        try with verse. 

bindwith in vminus.sml, first block with ifs
  fun bindWith (rho : 'a lvar_env) (e : 'a exp) (v : 'a value) = 
    case (e, v) of 
      (NAME n, v) => 
        let val nval = valIn rho n 
        in if isSome nval 
           then if (eqval ((valOf nval), v)) then OK rho else REJ
           else OK (Env.bind (n, SOME v, rho))
        end 
        