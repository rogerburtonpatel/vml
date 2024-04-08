val x = x
val x = K
val x = K y
val x = f x
val x = f (f x)
val x = K y (K z)
val x = \y. y
val x = (\y. y) (\y. y)
val x = case x of x -> x
val x = case x of K -> x
val x = case x of K x y -> x
val x = case x of K x (K y z) -> z
val x = case x of x | f -> x
val x = case x of K x (K y z) | f -> x
val x = case x of K x (K y z) -> x
| f -> x
val x = case x of K x (K y z) -> x
                | f | x -> x
val x = case x of x, y -> x
val x = case x of x, y <- x -> x
val x = case x of x, x <- x, false <- true -> x
| x -> x
val go_forth = case property of Correct x, y <- x, true <- y, when x -> Go_forth
| fail -> fail
val x = case x of x | y, x <- x, false <- true, when true -> x
| x -> x
val go_forth = case property of Correct x | Good_enough x, y <- x, true <- y, when x -> Go_forth
| fail -> fail
val x = f 3
val property = Correct true
val go_forth = \y. y
val fail = \prop. prop
val go_forth = case property of Correct x | Good_enough x, y <- x, true <- y, when x -> go_forth y
| failcase -> fail Property_failed
