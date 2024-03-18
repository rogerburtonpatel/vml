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
                                Core.vconAppStr 
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
      | expString (VCONAPP (v, es)) = Core.vconAppStr expString v es
      | expString (FUNAPP (e1, e2)) = br' (expString e1 ^ " " ^ expString e2)
      | expString (LAMBDAEXP (n, body)) = 
            StringEscapes.backslash ^ n ^ ". " ^ (expString body)
  fun defString (DEF (n, e)) = "val " ^ n ^ " = " ^ expString e

end 




signature EXTENSION = sig
  type 'a context
  type 'a value = 'a Core.core_value
  type 'a extension

  val eval : ('a context -> 'a -> 'a value) -> ('a context -> 'a extension -> 'a value) 
end


structure PPlusExtension : EXTENSION = struct
  type name = string
  type vcon = PPlus.vcon
  type pat = PPlus.toplevelpattern
  datatype 'a extension = CASE of 'a * (pat * 'a) list

  type 'a value = 'a Core.core_value
  type 'a context = 'a value Env.env

  val rec eval : ('a context -> 'a -> 'a value) -> ('a context -> 'a extension -> 'a value) =
    fn evalExp =>
    let fun go context (CASE (e, choices)) =
          let val v = evalExp context e
          in  Impossible.unimp "pick the choice that matches v"
          end
    in  go
    end

end

structure NewPPlus' = MkExtended(open PPlusExtension)

structure XXX =
struct
  structure P  = NewPPlus'
  structure PX = PPlusExtension
  fun eval rho e = 
      case e 
        of P.NAME n => Env.find (n, rho)
         | P.VCONAPP (c, es) => Core.VCON (c, map (eval rho) es)
         | P.FUNAPP (fe, param) => 
                (case eval rho fe 
                  of Core.LAMBDA (n, b) => 
                    let val arg = eval rho param
                        val rho' = Env.bind (n, arg, rho)
                      in eval rho' b
                      end
                   | _ => raise Core.BadFunApp "attempted to apply non-function")
        | P.LAMBDAEXP (n, ex) => Core.LAMBDA (n, ex)
        | P.E x => PX.eval eval rho x

end




functor MkEval(structure Extended : EXTENDED
               structure Extension : EXTENSION
                                         where type 'a context = 'a Core.core_value Env.env
               sharing type Extended.extension = Extension.extension
               )
  =
struct
  fun eval rho e = 
      case e 
        of Extended.NAME n => Env.find (n, rho)
         | Extended.VCONAPP (c, es) => Core.VCON (c, map (eval rho) es)
         | Extended.FUNAPP (fe, param) => 
                (case eval rho fe 
                  of Core.LAMBDA (n, b) => 
                    let val arg = eval rho param
                        val rho' = Env.bind (n, arg, rho)
                      in eval rho' b
                      end
                   | _ => raise Core.BadFunApp "attempted to apply non-function")
        | Extended.LAMBDAEXP (n, ex) => Core.LAMBDA (n, ex)
        | Extended.E x => Extension.eval eval rho x
end




