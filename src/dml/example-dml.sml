exception NoMatch 
type vcon = string 
datatype data = CON of vcon * data list

val conthree = CON ("3", [])
val connil   = CON ("nil", [])

val scrutinee  = CON ("cons", [conthree, CON ("cons", [conthree, connil])])

val scrutinee2 = CON ("cons", [conthree, connil])

fun len l = (case l of CON (x1, x2) => 
                    (case x1 of "cons" => 
                        (case x2 of [x3, x4] => len x4
                                 | _         => raise NoMatch)
                        | "nil" => 1
                        | _ => raise NoMatch))

fun len l = (case l of CON (x1, x2) => 
                let val x3 = x1 in 
                    (case x3 of "cons" => 
                        let val x4 = x2 in 
                        (case x2 of [x5, x6] => 1 + len x6
                                 | _         => raise NoMatch)
                        end 
                        | "nil" => 0
                        | _ => raise NoMatch)
                        end)


(* val _ = print (Int.toString (len scrutinee) ^ "\n") *)

val () = Unit.checkExpectWith Unit.intString "decision tree 1"
         (fn () => len scrutinee)
         2

val () = Unit.checkExpectWith Unit.intString "decision tree 2"
         (fn () => len scrutinee2)
         1

val () = Unit.checkExnWith Unit.intString "decision tree 3 - non-list"
         (fn () => len conthree)

val () = Unit.report ()
