structure PPlus :> sig 
  type name = Core.name
  type vcon = Core.vcon

  datatype 'e pattern = PNAME of name 
                      | WHEN of 'e 
                      | WILDCARD
                      | CONAPP of vcon * 'e pattern list
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core.t 
               | I of exp ppcase

  type value = exp Core.value

  datatype def = DEF of name * exp

  val expString : exp -> string
  val valString : value -> string
  val patString : exp pattern -> string
  val defString : def -> string

  val runProg : def list -> unit 

end 
  = 
struct
  type name = Core.name
  type vcon = Core.vcon

  datatype 'e pattern = PNAME of name 
                      | WHEN of 'e 
                      | WILDCARD
                      | CONAPP of vcon * 'e pattern list
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core.t 
               | I of exp ppcase

  type value = exp Core.value

  datatype def = DEF of name * exp

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"
  val member = ListUtil.member

  fun println s = print (s ^ "\n")


  structure C = Core 

  fun expString (C ce) = 
  (case ce of C.FUNAPP (e1, e2)  => 
                          maybeparenthesize e1 ^ " " ^ maybeparenthesize e2
            | C.VCONAPP (vc, es) => C.vconAppStr maybeparenthesize vc es
            | _ => Core.expString expString ce)
    | expString (I (CASE (scrutinee, branches))) = 
      let fun branchString (p, ex) = patString p ^ " -> " ^ expString ex
          val body = 
              if null branches 
              then "" 
              else String.concatWith "\n  | " (map branchString branches)
          in "case " ^ expString scrutinee ^ " of " ^ body
          
          end
  and patString (PNAME n) = n 
    | patString (CONAPP (n, ps)) = 
         C.vconAppStr (fn (PNAME n') => n' 
                          | (CONAPP (C.K n, [])) => n
                          | cmplx => br patString cmplx) n ps
    | patString (WHEN cond)       = ("when "      ^ expString cond)
    | patString WILDCARD       = "_"
    | patString (ORPAT (p1, p2))  = (patString p1 ^ " | "  ^ patString p2)
    | patString (PATSEQ (p1, p2)) = (patString p1 ^  ", "  ^ patString p2)
    | patString (PATGUARD (p, e)) = (patString p  ^ " <- " ^ expString e)
  and valString v = C.valString expString v    
  and maybeparenthesize (C e) = C.maybeparenthesize expString e
    | maybeparenthesize other = br' (expString other)
  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

  fun patmap f g p = 
  case p 
    of  PNAME n          => PNAME (f n)
      | WHEN e           => WHEN (g e)
      | WILDCARD         => WILDCARD
      | PATGUARD (p', e) => PATGUARD (patmap f g p', f e)
      | ORPAT (p1, p2)   => ORPAT (patmap f g p1, patmap f g p2)
      | PATSEQ (p1, p2)  => PATSEQ (patmap f g p1, patmap f g p2)
      | CONAPP (vc, ps)  => CONAPP (vc, map (patmap f g) ps)


  (* environment utils *)

  infix 6 <+>
  val op <+> = Env.<+>

  infix 9 binds
  fun rho binds n = Env.binds (rho, n)

  fun lookup x rho = Env.find (x, rho)
  fun bind x v rho = Env.bind (x, v, rho)
  fun lookupv x rho = valOf (lookup x rho)
  val empty = Env.empty

  exception DisjointUnionFailed of name

  fun duplicatename [] = NONE
    | duplicatename (x::xs) =
        if List.exists (fn x' => x' = x) xs then
          SOME x
        else
          duplicatename xs

  val _ = duplicatename : name list -> name option
  fun disjointUnion (envs: value Env.env list) =
    let val env = Env.concat envs
    in  case duplicatename (Env.keys env)
          of NONE => env
          | SOME x => raise DisjointUnionFailed x
    end

  val predefs = ["print"]

  exception DuplicateNames of name

  fun captureVal rho (C.LAMBDA (n, captured, body)) = 
        C.LAMBDA (n, captured <+> rho, body)
    | captureVal rho (C.VCON (vc, vs)) = C.VCON (vc, map (captureVal rho) vs)

  fun eval rho (C ce) = 
    (case ce of 
      C.LITERAL v => v
    | C.NAME n => lookup n rho  
    | C.VCONAPP (vc, es) => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, rho, body)
    | C.FUNAPP (C (C.NAME n), arg)  => 
      if member n predefs 
      then runpredef n (rho, arg) 
      else let val v = eval rho (C (C.NAME n))
            in eval rho (C (C.FUNAPP (C (C.LITERAL v), arg)))
            end 
    | C.FUNAPP (fe, arg) => 
              (case eval rho fe 
                of C.LAMBDA (n, captured, b) => 
                    let val v_arg = eval rho arg
                        val rho' = bind n v_arg rho <+> captured
                    in eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
  | eval rho (I (CASE (C (C.LITERAL v), (p, rhs) :: choices))) =
            (let val rho' = (match rho (p, v)
                             handle DisjointUnionFailed x => 
                              raise DuplicateNames x)
            in  eval (rho <+> rho') rhs
            end
            handle Core.NoMatch => 
              eval rho (I (CASE (C (C.LITERAL v), choices))))
  | eval rho (I (CASE (_, []))) = raise Match
  | eval rho (I (CASE (scrutinee, branches))) = 
      let val v = eval rho scrutinee 
      in eval rho (I (CASE (C (C.LITERAL v), branches)))
      end 

  and match rho (PNAME x,   v) = bind x v empty
    | match rho (WILDCARD, _)  = empty
    | match rho (WHEN e, _)     = 
      (case eval rho e 
        of C.VCON ((C.K "false"), _) => raise Core.NoMatch 
         | _                         => empty)
    | match rho (PATGUARD (p, e), _) = match rho (p, eval rho e) 
    | match rho (ORPAT (p1, p2), v)  = 
      (match rho (p1, v) handle Core.NoMatch => match rho (p2, v))
    | match rho (PATSEQ (p1, p2), v)  = 
        let val rho1 = match rho (p1, v)
        in rho1 <+> match (rho <+> rho1) (p2, v)
        end 
    | match rho (CONAPP (C.K k, ps), C.VCON (C.K k', vs)) =
     if k = k' andalso length ps = length vs
     then disjointUnion (ListPair.mapEq (match rho) (ps, vs))
     else raise Core.NoMatch
  | match rho (CONAPP _, _) = raise Core.NoMatch

  and runpredef which (rho, arg) = 
    case which of 
      "print" => ( println (C.valString expString (eval rho arg)) 
                  ; C.VCON (C.K "unit", [])
                 )
      | _ => Impossible.impossible "runtime bug: running non-predef function"


  fun def rho (DEF (n, e)) = 
    let val v = eval rho e
    in bind n v rho
    end

  fun runProg defs = 
  (  foldl (fn (d, env) => 
      let val rho = def env d
      in  rho <+> env
      end) Env.empty defs;
      ()
  )

end


fun len []      = 0 
  | len (x::xs) = 1 + len xs


fun len ys = 
  if null ys 
  then 0 
  else let val xs = tl ys 
        in 1 + len xs 
        end 

datatype shape = Square    of real 
               | Triangle  of real * real
               | Trapezoid of real * real * real

fun area sh = 
  case sh of  
    Square s              =>  s * s
  | Triangle (w, h)       =>  w * h  * 0.5 
  | Trapezoid (b1, b2, h) => b1 * b2 * h * 0.5 

fun isTriangle (Triangle _) = true 
  | isTriangle _ = false 

fun isSquare (Square _) = true 
  | isSquare _ = false 

exception BadShape

fun sqSide (Square s) = s
  | sqSide _ = raise BadShape
fun triW (Triangle (w, h)) = w
  | triW _ = raise BadShape
fun triH (Triangle (w, h)) = h
  | triH _ = raise BadShape
fun traB1 (Trapezoid (b1, b2, h)) = b1
  | traB1 _ = raise BadShape
fun traB2 (Trapezoid (b1, b2, h)) = b2
  | traB2 _ = raise BadShape
fun traH (Trapezoid (b1, b2, h)) = h
  | traH _ = raise BadShape

fun area sh =
  if isSquare sh
  then sqSide sh * sqSide sh
  else  if isTriangle sh
        then 0.5 * triW sh * triH sh
        else 0.5 * traB1 sh * traB2 sh * traH sh

(* fun exclaimTall (Square (s that is larger than 100.0)) = "Wow! That's a tall square!" *)

fun append (xs, ys) = case xs of [] => ys | (x::xr) => x::append (xr, ys)




fun exclaimTall sh =
case sh of 
   Square s => if s > 100.0 
                then "Wow! That's a tall square!"
                else "Your shape is small." 
  | Triangle (_, h) => 
                if h > 100.0 
                then "Goodness! Towering triangle!"
                else "Your shape is small." 
  | Trapezoid (_, _, h) => 
                if h > 100.0
                then "Zounds! Tremendous trapezoid!"
                else "Your shape is small." 

fun exclaimTall sh =
case sh of 
   Square s => if s > 100.0 
                then "Wow! That's a tall square!"
                else "Your shape is small." 
  | Triangle (_, h) => 
                if h > 100.0 
                then "Goodness! Towering triangle!"
                else "Your shape is small." 
  | Trapezoid (_, _, h) => 
                if h > 100.0
                then "Zounds! Tremendous trapezoid!"
                else "Your shape is small." 

(* fun exclaimTall sh =
  case sh if 
    | Square s when s > 100.0 =>
            "Wow! That's a tall square!"
    | Triangle (w, h) when h > 100.0 =>
            "Goodness! Towering triangle!"
    | Trapezoid (b1, b2, h) when h > 100.0 => 
            "Zounds! Tremendous trapezoid!"
    | _ =>  "Your shape is small."  *)

(* fun tripleLookup rho x = 
  case lookup rho x of 
    SOME w, 
    SOME y <- lookup rho w,
    SOME z <- lookup rho y 
      => z
    | _ => handleFailure x *)
  
(* fun tripleLookup (rho : finitemap) (x : int) =
case lookup rho x of Some w =>
  (case lookup rho w of Some y => 
    (case lookup rho y of Some z => z
    | _ => handleFailure x)
  | _ => handleFailure x)
| _ => handleFailure x *)

(* 
datatype token = BattlePass  of funlevel 
           | ChugJug     of funlevel 
           | TomatoTown  of funlevel
           | HuntersMark of funlevel 
           | SawCleaver  of funlevel
           | MoghLordOfBlood of funlevel 
           | PreatorRykard   of funlevel
           | (* ... other lesser games' tokens ... *)                                             Dummy 



fun game_of_token token = case token of 
  BattlePass f      => ("Fortnite", f)
| ChugJug f         => ("Fortnite", f)
| TomatoTown f      => ("Fortnite", f)
| HuntersMark f     => ("Bloodborne", 2 * f)
| SawCleaver f      => ("Bloodborne", 2 * f)
| MoghLordOfBlood f => ("Elden Ring", 3 * f)
| PreatorRykard f   => ("Elden Ring", 3 * f)
| _                 => ("Irrelevant", 0)


fun game_of_token token = case token of
  BattlePass f  | ChugJug f | TomatoTown f => ("Fortnite", f)
| HuntersMark f | SawCleaver f             => ("Bloodborne", 2 * f)
| MoghLordOfBlood f | PreatorRykard f      => ("Elden Ring", 3 * f)
| _                                        => ("Irrelevant", 0) *)