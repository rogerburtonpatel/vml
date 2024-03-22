structure FinalPPlus :> sig 
  type name = Core'.name
  type vcon = Core'.vcon

  datatype 'e pattern = PNAME of name 
                      | WHEN of 'e 
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | CONAPP of vcon * 'e pattern list
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core'.t 
               | I of exp ppcase

  type value = exp Core'.value

  datatype def = DEF of name * exp

  val expString : exp -> string
  val patString : exp pattern -> string
  val defString : def -> string

end 
  = 
struct
  type name = Core'.name
  type vcon = Core'.vcon

  datatype 'e pattern = PNAME of name 
                      | WHEN of 'e 
                      | PATGUARD of 'e pattern * 'e 
                      | ORPAT of 'e pattern * 'e pattern 
                      | CONAPP of vcon * 'e pattern list
                      | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype exp = C of exp Core'.t 
               | I of exp ppcase

  type value = exp Core'.value

  datatype def = DEF of name * exp

  fun br printer input = "(" ^ printer input ^ ")"
  fun br' input = "(" ^ input ^ ")"




  fun expString (C ce)                           = Core'.expString expString ce
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
        Core'.vconAppStr (fn (PNAME n') => n' 
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


  structure C = Core'
  infix 6 <+> 
  val op <+> = Env.<+>
  exception DisjointUnionFailed of name

  fun duplicatename [] = NONE
    | duplicatename (x::xs) =
        if List.exists (fn x' => x' = x) xs then
          SOME x
        else
          duplicatename xs
(* <boxed values 96>=                           *)
val _ = duplicatename : name list -> name option
fun disjointUnion (envs: 'a Env.env list) =
  let val env = Env.concat envs
  in  case duplicatename (Env.keys env)
        of NONE => env
         | SOME x => raise DisjointUnionFailed x
  end

  exception Doesn'tMatch

  
  fun eval rho (C ce) = 
    (case ce of 
      C.LITERAL v => v
    | C.NAME n => Env.find (n, rho)  
    | C.VCONAPP (vc, es) => C.VCON (vc, map (eval rho) es)
    | C.LAMBDAEXP (n, body) => C.LAMBDA (n, body)
    | C.FUNAPP (fe, param) => 
              (case eval rho fe 
                of C.LAMBDA (n, b) => 
                  let val arg = eval rho param
                      val rho' = Env.bind (n, arg, rho)
                    in eval rho' b
                    end
                 | _ => raise Core.BadFunApp "attempted to apply non-function"))
  | eval rho (I (CASE (C (C.LITERAL v), (p, rhs) :: choices))) =
            (let val rho' = match rho (p, v)
            in  eval (rho <+> rho') rhs
            end
            handle Doesn'tMatch => 
              eval rho (I (CASE (C (C.LITERAL v), choices))))
  | eval rho (I (CASE (_, []))) = raise Match
  | eval rho (I (CASE (scrutinee, branches))) = 
      let val v = eval rho scrutinee 
      in eval rho (I (CASE (C (C.LITERAL v), branches)))
      end 

  and match rho (PNAME x,   v) = Env.bind (x, v, Env.empty)
    | match rho (WHEN e, _)     = 
      (case eval rho e 
        of C.VCON ((C.K "false"), _) => raise Doesn'tMatch 
         | _                         => Env.empty)
    | match rho (PATGUARD (p, e), _) = match rho (p, eval rho e) 
    | match rho (ORPAT (p1, p2), v)  = 
      (match rho (p1, v) handle Doesn'tMatch => match rho (p2, v))
    | match rho (PATSEQ (p1, p2), v)  = 
        disjointUnion [match rho (p1, v), match rho (p2, v)]
    | match rho (CONAPP (C.K k, ps), C.VCON (C.K k', vs)) =
     if k = k' 
     then disjointUnion (ListPair.mapEq (match rho) (ps, vs))
     else raise Doesn'tMatch
  | match rho (CONAPP _, _) = raise Doesn'tMatch

  (* TODO next: test eval, write vm eval, write d eval, renamings, vm parser (fun actually) *)


(* val branches = [(CONAPP ("K", [PNAME "n"]), C (Core'.NAME "e1")), (CONAPP ("K", [PNAME "n1", PNAME "n2"]), C (Core'.NAME "e2"))]
val x_ = I (CASE (C (Core'.VCONAPP ("K", [C (Core'.NAME "n1"), C (Core'.NAME "n2")])), branches))
val _ = print ("HERE\n\n" ^ expString x_) *)

end


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

  (* infix 6 <+> 
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
fun disjointUnion (envs: 'a Env.env list) =
  let val env = Env.concat envs
  in  case duplicatename (Env.keys env)
        of NONE => env
         | SOME x => raise DisjointUnionFailed x
  end

  exception Doesn'tMatch

  fun match (CONAPP (k, ps), Core.VCON (Core.K k', vs)) =
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
      | CASE _ => Impossible.unimp "case "
      (* | CASE (ex, (p, rhs) :: choices) =>
            let val v = eval rho ex 
            val rho' = match (p, v)
            in  eval (e, rho <+> rho')
            end
            handle Doesn'tMatch => eval rho (CASE (LITERAL v, choices))
      | CASE (_, []) =>
          raise Match *)

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
