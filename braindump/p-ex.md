            | NAME n => if not (Env.binds (rho, n))
                        orelse not (isSome (Env.find (n, rho)))
                        then raise NameNotBound n 
                        else valOf (Env.find (n, rho))

                        ugly. without valof especially; dup branches. 
                        try with verse. 

                        