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
                          | cmplx => br patString cmplx) n ps
    | patString (WHEN cond)       = ("when "      ^ expString cond)
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
    | C.NAME n => lookup n rho  
    | C.VCONAPP (vc, es) => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, body)
    | C.FUNAPP (C (C.NAME n), arg)  => 
      if member n predefs 
      then runpredef n (rho, arg) 
      else let val v = eval rho (C (C.NAME n))
            in eval rho (C (C.LITERAL v))
            end 
    | C.FUNAPP (fe, arg) => 
              (case eval rho fe 
                of C.LAMBDA (n, b) => 
                    let val v_arg = eval rho arg
                        val rho' = bind n v_arg rho
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

  and match rho (PNAME x,   v) = bind x v empty
    | match rho (WHEN e, _)     = 
      (case eval rho e 
        of C.VCON ((C.K "false"), _) => raise Core.NoMatch 
         | _                         => empty)
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
