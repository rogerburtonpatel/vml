structure PPlus :> sig 
  type name = Core.name
  type vcon = Core.vcon

  datatype 'e pattern = PNAME of name 
                      | WHEN of 'e 
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | CONAPP of vcon * 'e pattern list
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core.t 
               | I of exp ppcase

  type value = exp Core.value

  datatype def = DEF of name * exp

  val expString : exp -> string
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
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | CONAPP of vcon * 'e pattern list
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core.t 
               | I of exp ppcase

  type value = exp Core.value

  datatype def = DEF of name * exp

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"
  fun member x xs = List.exists (fn y => y = x) xs

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
    and maybeparenthesize (C e) = 
    (case e of C.LITERAL v => br' (C.valString expString v)
            | C.NAME n     => n
            | C.VCONAPP (C.K vc, es) => 
                if null es then vc else br' (C.vconAppStr expString (C.K vc) es)
            | C.LAMBDAEXP (n, body)  => 
              br' (StringEscapes.backslash ^ n ^ ". " ^ (expString body))
            | C.FUNAPP (e1, e2)      => br' (expString e1 ^ " " ^ expString e2))
      | maybeparenthesize other = br' (expString other)
  and patString (PNAME n) = n 
    | patString (CONAPP (n, ps)) = 
        Core.vconAppStr (fn (PNAME n') => n' 
                          | cmplx => br patString cmplx) n ps
    | patString (WHEN cond)       = ("when "      ^ expString cond)
    | patString (ORPAT (p1, p2))  = (patString p1 ^ " | "  ^ patString p2)
    | patString (PATSEQ (p1, p2)) = (patString p1 ^  ", "  ^ patString p2)
    | patString (PATGUARD (p, e)) = (patString p  ^ " <- " ^ expString e)
    
  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

  fun patmap f g p = 
  case p 
    of  PNAME n          => PNAME (f n)
      | WHEN e           => WHEN (g e)
      | PATGUARD (p', e) => PATGUARD (patmap f g p', f e)
      | ORPAT (p1, p2)   => ORPAT (patmap f g p1, patmap f g p2)
      | PATSEQ (p1, p2)  => PATSEQ (patmap f g p1, patmap f g p2)
      | CONAPP (vc, ps)  => CONAPP (vc, map (patmap f g) ps)


  structure C = Core
  infix 6 <+> 
  val op <+> = Env.<+>
  exception DisjointUnionFailed of name

  fun duplicatename [] = NONE
    | duplicatename (x::xs) =
        if List.exists (fn x' => x' = x) xs then
          SOME x
        else
          duplicatename xs

  val _ = duplicatename : name list -> name option
  fun disjointUnion (envs: 'a Env.env list) =
    let val env = Env.concat envs
    in  case duplicatename (Env.keys env)
          of NONE => env
          | SOME x => raise DisjointUnionFailed x
    end

  val predefs = ["print"]

  fun eval rho (C ce) = 
    (case ce of 
      C.LITERAL v => v
    | C.NAME n => Env.find (n, rho)  
    | C.VCONAPP (vc, es) => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, body)
    | C.FUNAPP (C (C.NAME "print"), param)  => 
    (* dirty trick to print values *)
                    ( println (C.valString expString (eval rho param)) 
                          ; C.VCON (C.K "unit", [])
                    ) 
    | C.FUNAPP (fe, arg) => 
              (case eval rho fe 
                of C.LAMBDA (n, b) => 
                  let val v_arg = eval rho arg
                      val rho' = Env.bind (n, v_arg, rho)
                    in eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
  | eval rho (I (CASE (C (C.LITERAL v), (p, rhs) :: choices))) =
            (let val rho' = match rho (p, v)
            in  eval (rho <+> rho') rhs
            end
            handle Core.NoMatch => 
              eval rho (I (CASE (C (C.LITERAL v), choices))))
  | eval rho (I (CASE (_, []))) = raise Match
  | eval rho (I (CASE (scrutinee, branches))) = 
      let val v = eval rho scrutinee 
      in eval rho (I (CASE (C (C.LITERAL v), branches)))
      end 

  and match rho (PNAME x,   v) = Env.bind (x, v, Env.empty)
    | match rho (WHEN e, _)     = 
      (case eval rho e 
        of C.VCON ((C.K "false"), _) => raise Core.NoMatch 
         | _                         => Env.empty)
    | match rho (PATGUARD (p, e), _) = match rho (p, eval rho e) 
    | match rho (ORPAT (p1, p2), v)  = 
      (match rho (p1, v) handle Core.NoMatch => match rho (p2, v))
    | match rho (PATSEQ (p1, p2), v)  = 
        disjointUnion [match rho (p1, v), match rho (p2, v)]
    | match rho (CONAPP (C.K k, ps), C.VCON (C.K k', vs)) =
     if k = k' 
     then disjointUnion (ListPair.mapEq (match rho) (ps, vs))
     else raise Core.NoMatch
  | match rho (CONAPP _, _) = raise Core.NoMatch

  and runpredef which (rho, arg) = 
    case which of 
      "print" => ( println (C.valString expString (eval rho arg)) 
                  ; C.VCON (C.K "unit", [])
                 )
      | _ => Impossible.impossible "runtime bug: running non-predef function"


  fun def (rho : value Env.env) (DEF (n, C (Core.LAMBDAEXP (x, body)))) = 
      let val rho' = Env.bind (n, Core.LAMBDA (x, body), rho)
      in rho' 
      end 
  | def rho (DEF (n, e)) = 
    let val v = eval rho e
    in Env.bind (n, v, rho)
    end

  fun runProg defs = 
  (  foldl (fn (d, env) => 
      let val rho = def env d
      in  Env.<+> (rho, env)
      end) Env.empty defs;
      ())
  


(* val branches = [(CONAPP ("K", [PNAME "n"]), C (Core.NAME "e1")), (CONAPP ("K", [PNAME "n1", PNAME "n2"]), C (Core.NAME "e2"))]
val x_ = I (CASE (C (Core.VCONAPP ("K", [C (Core.NAME "n1"), C (Core.NAME "n2")])), branches))
val _ = print ("HERE\n\n" ^ expString x_) *)

end
