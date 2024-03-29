structure PPlus :> sig 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (toplevelpattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
               | LAMBDAEXP of name * exp 
      and toplevelpattern =   PAT of pattern 
                            | WHEN   of toplevelpattern * exp
                            | ORPAT of pattern list 
                            | PATGUARD of toplevelpattern * (pattern * exp) list
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
  type value = exp Core.core_value
  datatype def = DEF of name * exp

  val expString : exp -> string
  val defString : def -> string

  val runProg : def list -> unit 
end 
  = 
struct 
  type name = string 
  type vcon = Core.vcon 
  datatype exp = NAME of name 
               | CASE of exp * (toplevelpattern * exp) list 
               | VCONAPP of vcon * exp list 
               | FUNAPP  of exp * exp 
               | LAMBDAEXP of name * exp 
      and toplevelpattern =   PAT of pattern 
                            | WHEN   of toplevelpattern * exp
                            | ORPAT of pattern list 
                            | PATGUARD of toplevelpattern * (pattern * exp) list
      and pattern =     PNAME of name
                      | CONAPP of name * pattern list 
  type value = exp Core.core_value
  datatype def = DEF of name * exp

  infix 6 <+> 
  val op <+> = Env.<+>
  fun fst (x, y) = x
  

exception DisjointUnionFailed of name
fun duplicatename [] = NONE
  | duplicatename (x::xs) =
      if List.exists (fn x' => x' = x) xs then
        SOME x
      else
        duplicatename xs
(* <boxed values 96>=                           *)
val _ = duplicatename : name list -> name option
(* fun disjointUnion (envs: 'a Env.env list) =
  let val env = Env.concat envs
  in  case duplicatename (map fst env)
        of NONE => env
         | SOME x => raise DisjointUnionFailed x
  end *)

  exception Doesn'tMatch

  (* fun match (CONAPP (k, ps), Core.VCON (Core.K k', vs)) =
     if k = k' then
       disjointUnion (ListPair.mapEq match (ps, vs))
     else
       raise Doesn'tMatch
  | match (CONAPP _, _) = raise Doesn'tMatch
  | match (PNAME x,   v) = Env.bind (x, v, Env.empty) *)


(* <boxed values 147>=                          *)
(* val _ = op match         : pat * value -> value env (* or raises Doesn'tMatch *)
val _ = op disjointUnion : 'a env list -> 'a env *)

fun eval (rho : value Env.env) e = 
    case e 
      of NAME n => Env.find (n, rho)
       | VCONAPP (Core.TRUE,  []) => Core.VCON (Core.TRUE, [])
       | VCONAPP (Core.FALSE, []) => Core.VCON (Core.FALSE, []) 
       | VCONAPP (Core.K n, es)  => Core.VCON (Core.K n, map (eval rho) es)
       | VCONAPP _ => 
               raise Impossible.impossible "erroneous vcon argument application"
       | FUNAPP (fe, param) => 
              (case eval rho fe 
                of Core.LAMBDA (n, b) => 
                  let val arg = eval rho param
                      val rho' = Env.bind (n, arg, rho)
                    in eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function")
      | LAMBDAEXP (n, ex) => Core.LAMBDA (n, ex)
      | CASE (ex, (p, rhs) :: choices) => Impossible.unimp "eval case"
      | CASE _ => Impossible.unimp "eval case"
          (* let val scrutinee = eval rho ex *)

fun def rho (DEF (n, e)) = 
  let val v = eval rho e
  in Env.bind (n, v, rho)
  end

fun runProg defs = 
(  foldl (fn (d, env) => 
    let val rho = def env d
    in  Env.<+> (rho, env)
    end) Env.empty defs;
    ())


        (* val _ = op match : pat * value -> value env
        val _ = op <+>   : 'a env * 'a env -> 'a env *)
            
             (* val rho' = match (p, v)
             in  eval (e, rho <+> rho')
             end
             handle Doesn'tMatch => eval rho (CASE (LITERAL v, choices))
        | CASE (_, []) =>
            raise Match *)

        (* <more alternatives for [[ev]] for \nml\ and \uml>= *)
                (* | ev (CASE (LITERAL v, 
                        (p, e) :: choices)) =
            (let val rho' = match (p, v)
        | ev (CASE (LITERAL v, [])) =
            raise RuntimeError ("'case' does not match " ^ valueString v)
        in Impossible.unimp "he"
        end  *)

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"

  fun expString (NAME n) = n
    | expString (CASE (e, branches)) = 
      let 
          fun tlpatString (PAT p) = patString p
            | tlpatString (WHEN (p, cond)) = br' (tlpatString p 
                                              ^ " when " ^ expString cond)
            | tlpatString (ORPAT []) = Impossible.impossible "empty orpat"
            | tlpatString (ORPAT [_]) = Impossible.impossible "singleton orpat"
            | tlpatString (ORPAT ps) = 
                        patString (hd ps) ^ 
                            (foldr (fn (p, acc) => " | " ^ patString p ^ acc) "" 
                            (tl ps))
            | tlpatString (PATGUARD (tlp, steps)) = 
            br' (tlpatString tlp ^ 
            (foldl (fn ((pat, ex), acc) => 
                acc ^ ", " ^ patString pat ^ " <- " ^ expString ex ^ "") "" steps))
          and patString (PNAME n) = n 
            | patString (CONAPP (n, ps)) = 
                                Core.strBuilderOfVconApp 
                                  (fn (PNAME n') => n' 
                                      | conapp => br patString conapp) 
                                  (Core.K n) 
                                  ps
          fun branchString (p, ex) = 
                                     tlpatString p ^ " -> " ^ expString ex
          in "case " ^ expString e ^ " of " ^ 
          (if null branches 
          then "" 
          else branchString (hd branches) ^ 
                (foldr (fn (br, acc) => "\n| " ^ branchString br ^ acc) "" 
                 (tl branches)))
          end
      | expString (VCONAPP (v, es)) = Core.strBuilderOfVconApp expString v es
      | expString (FUNAPP (e1, e2)) = br' (expString e1 ^ " " ^ expString e2)
      | expString (LAMBDAEXP (n, body)) = 
            StringEscapes.backslash ^ n ^ ". " ^ (expString body)
  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

end 