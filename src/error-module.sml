(* Implementation for error-sig.sml *)

(* You'll need to use the signature (found in error-sig.sml) 
  but don't need to know how things are implemented *)

structure Error :> ERROR = struct
  datatype 'a error = OK of 'a | ERROR of string

  infix 0 >>=

  fun (OK x)      >>= k  =  k x
    | (ERROR msg) >>= k  =  ERROR msg



  fun join e = e >>= (fn x => x)
  fun errorList es =
    let fun cons (OK x, OK xs) = OK (x :: xs)
          | cons (ERROR m1, ERROR m2) = ERROR (m1 ^ ";\n  " ^ m2)
          | cons (ERROR m, OK _) = ERROR m
          | cons (OK _, ERROR m) = ERROR m
    in  foldr cons (OK []) es
    end

  val list = errorList
  
  fun map f (OK x)    = OK (f x)
    | map f (ERROR m) = ERROR m


  val succeed = OK
  fun <*> (f, x) = f >>= (fn f => x >>= (fn x => OK (f x)))
  fun <$> (f, x) = <*> (succeed f, x)

  fun >=> (f, g) = fn x => f x >>= g      (* Kleisli composition *)

  fun mapList f = errorList o List.map f

  fun option NONE = OK NONE
    | option (SOME (OK x)) = OK (SOME x)
    | option (SOME (ERROR m)) = ERROR m

end



