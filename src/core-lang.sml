structure Core :> sig 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'exp core_value = VCON of vcon   * 'exp core_value list 
                           | LAMBDA of name * 'exp

  exception NameNotBound of name 
  exception BadFunApp of string 

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  val eqval               : 'a core_value * 'a core_value -> bool
  val boolOfCoreValue     : 'a core_value -> bool 
  val expString           : core_exp -> string 
  val valString      : 'a core_value -> string 
  val vconAppStr : ('a -> string) -> vcon -> 'a list -> string
end 
  = 
struct 
  type name = string 
  datatype vcon  = TRUE | FALSE | K of name 
  datatype 'a core_value = VCON of vcon * 'a core_value list | LAMBDA of name * 'a

  exception NameNotBound of name 
  exception BadFunApp of string 

  

  datatype core_exp = NAME of name 
                  | VCONAPP of vcon * core_exp list
                  | LAMBDAEXP of name * core_exp 
                  | FUNAPP of core_exp * core_exp 

  fun boolOfCoreValue (VCON (FALSE, [])) = false
    | boolOfCoreValue _                  = true


                     

  fun vconAppStr f n args = 
      case (n, args)
      of (K n, vs) =>
        let val vcss = foldr (fn (vc, acc) => " " ^ f vc ^ acc) "" vs
        in n ^ vcss
        end 
    | (TRUE, [])  =>  "true"
    | (FALSE, []) =>  "false"
    | (TRUE, _)   =>  Impossible.impossible "true applied to args"
    | (FALSE, _)  =>  Impossible.impossible "false applied to args"

  fun expString (NAME n) = n
    | expString (VCONAPP (n, es)) = 
     vconAppStr expString n es 
    | expString (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
    | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2

  fun valString (VCON (v, vals)) = 
          vconAppStr valString v vals 
    | valString (LAMBDA (n, e)) = 
      Impossible.impossible 
      "stringifying core lambda- client code must handle this case"

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 
end

structure Core' :> sig
    type name = string 
    type vcon = string
    datatype 'a t = NAME of name 
               | VCONAPP of vcon * 'a list
               | LAMBDAEXP of name * 'a 
               | FUNAPP of 'a * 'a 
  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp

  val map                 : ('a -> 'b) -> 'a t -> 'b t
  
  val eqval               : 'a value * 'a value -> bool

  val expString           : ('a -> string) -> 'a t -> string
  val valString           : ('a -> string) -> 'a value -> string 
  val vconAppStr : ('a -> string) -> vcon -> 'a list -> string

  end 

  = struct
    type name = string 
    type vcon = string
    datatype 'a t = NAME of name 
               | VCONAPP of vcon * 'a list
               | LAMBDAEXP of name * 'a 
               | FUNAPP of 'a * 'a 

  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp

  fun map (f : ('a -> 'b)) t = 
    case t of NAME n      => NAME n  
        | VCONAPP (vc, ts) => VCONAPP (vc, List.map f ts)
        | LAMBDAEXP (n, t) => LAMBDAEXP (n, f t)
        | FUNAPP (t1, t2)  => FUNAPP (f t1, f t2)

  fun eqval (VCON (v1, vs), VCON (v2, vs'))     = 
      v1 = v2 andalso ListPair.all eqval (vs, vs')
    | eqval (_, _) = false 

  fun vconAppStr f vc args = 
      String.concatWith " " (vc::(List.map f args))

  fun expString f (NAME n) = n
    | expString f (VCONAPP (n, es)) = vconAppStr f n es 
    | expString f (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
    | expString f (FUNAPP (e1, e2)) = f e1 ^ " " ^ f e2

  fun valString f (VCON (v, vals)) = 
          vconAppStr (valString f) v vals 
    | valString f (LAMBDA (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (f body)
    
end

structure FinalVMinus = struct
  type name = string
  type vcon = string
  datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
                    | CHOICE of 'e guard list * 'e guard list
  datatype ('e, 'a) if_fi = IF_FI of (name list * 'e guard list * 'a) list
  datatype 'e multi = MULTI of 'e list
  datatype vminus = C of vminus Core'.t
                  | I of (vminus, vminus multi) if_fi

end

structure FinalPPlus = struct
  type name = string
  type vcon = string

  datatype 'e pattern = PATNAME of name 
                  | WHEN of 'e 
                  | PATGUARD of 'e pattern * 'e 
                  | ORPAT of 'e pattern * 'e pattern 
                  | PATCONAPP of name * 'e pattern list
                  | PATSEQ of 'e pattern * 'e pattern 

  datatype 'a ppcase = CASE of 'a * ('a pattern * 'a) list
  datatype pplus = C of pplus Core'.t 
                 | I of pplus ppcase


end

structure FinalD = struct
  type name = string
  type vcon = string
  type arity = int
  type labeled_constructor = vcon * arity

  datatype 'e multi = MULTI of 'e list

  datatype ('e, 'a) tree = MATCH of 'a
              | TEST of name * (labeled_constructor * ('e, 'a) tree) list * ('e, 'a) tree option
              | IF of name   * ('e, 'a) tree * ('e, 'a) tree 
              | LET of name  * 'e * ('e, 'a) tree 

  datatype d = C of d Core'.t 
             | I of (d, d multi) tree

end


structure PPofVM = struct

  structure P = FinalPPlus
  structure V = FinalVMinus
  structure D = FinalD
  structure C = Core'


  fun typecheck () = Impossible.unimp "typecheck"
(* get all pattern names 
   introduce them all at the top
   then translate each pattern accordingly: 
   (pattern, name) goes to equation. nesting preserved. 

    *)
  fun uncurry f (x, y) = f x y

  fun patFreeNames (P.PATNAME n) = [n]
            | patFreeNames (P.PATCONAPP (vc, ps)) = 
                                List.concat (List.map patFreeNames ps)
            | patFreeNames (P.WHEN _) = [] 
            | patFreeNames (P.ORPAT (p1, p2)) = 
                        List.concat [patFreeNames p1, patFreeNames p2] 
            | patFreeNames (P.PATGUARD (p, e)) = patFreeNames p 
            | patFreeNames (P.PATSEQ (p1, p2)) =  
                        List.concat [patFreeNames p1, patFreeNames p2] 

  fun translate (P.C ce) = V.C (Core'.map translate ce)
    | translate (P.I (P.CASE (scrutinee, branches))) = 
        let val freshNameGen = FreshName.freshNameGenGen ()
            val e'           = translate scrutinee
            val (pats, rhss) = ListPair.unzip branches 
            val (scrutinee_already_a_name, name) = 
                  (case e' of V.C (C.NAME n) => (true, n) 
                            | _ => (false, freshNameGen ()))
            val ns_gs    = map (translatePatWith name) pats
            val rhss'    = map (fn rhs => V.MULTI [translate rhs]) rhss
            val options  = ListPair.map (fn ((ns, gs), rhs) => (ns, gs, rhs)) 
                                        (ns_gs, rhss')
            val internal = V.IF_FI options
            val final    =
             if scrutinee_already_a_name 
             then internal
             else V.IF_FI [([name], [V.EQN (name, e')], V.MULTI [V.I internal])]
        in V.I final
        end

  and translatePatWith n (p : P.pplus P.pattern) = 
    let val _ = translatePatWith 
          : P.name -> P.pplus P.pattern -> V.name list * V.vminus V.guard list
        val freshNameGen = FreshName.freshNameGenGen ()
        val freenames    = patFreeNames p
        fun translateTwo f p1 p2 = 
            let val (names1, guards1) = translatePatWith n p1 
                val (names2, guards2) = translatePatWith n p2
            in (names1 @ names2, f (guards1, guards2))
            end 
        val (local_names, local_guards) = 
          case p of P.PATNAME n'   => ([], [V.EQN (n, V.C (C.NAME n'))])
            | P.WHEN e             => ([], [V.CONDITION (translate e)])
            | P.PATCONAPP (vc, ps) => 
            (* introduce one fresh per ps  *)
            let val fresh_names = map (fn _ => freshNameGen ()) ps
                val ns_gs = ListPair.map (uncurry translatePatWith) 
                            (fresh_names, ps)
                val (names, guards) = ListPair.unzip ns_gs
            in (List.concat names @ fresh_names, List.concat guards)
            (* final form is n = vc (n1 ... nm); 
               translatePatWith n1 p1; ...; translatePatWith nm pm *)
            end
            | P.ORPAT (p1, p2)   => translateTwo (fn gs => [V.CHOICE gs]) p1 p2
            | P.PATGUARD (p', e) => 
              let val n'              = freshNameGen ()
                  val (names, guards) = translatePatWith n' p'
              in (n'::names, V.EQN (n, translate e)::guards)
              end
            | P.PATSEQ (p1, p2)  => translateTwo (op @) p1 p2
      in (freenames @ local_names, local_guards)
      end

  val _ = translate : FinalPPlus.pplus -> FinalVMinus.vminus


      (* fun translatePatWith n (p : P.pplus P.pattern) = 
      let val _ = translatePatWith : P.name -> P.pplus P.pattern -> V.name list * V.vminus V.guard list
          val freshNameGen = FreshName.freshNameGenGen ()
          val freenames    = patFreeNames p
          val (local_names, (local_guards : V.vminus FinalVMinus.guard list)) = 
        case p of P.PATNAME n' => ([], ([V.EQN (n, V.C (C.NAME n'))] :  V.vminus FinalVMinus.guard list))
          | P.WHEN e           => ([], [V.CONDITION (translate e)])
          | P.PATCONAPP (vc, ps) => 
          (* introduce one fresh per ps  *)
          let val fresh_names = map (fn _ => freshNameGen ()) ps 
              val ns_gs = ListPair.map (uncurry translatePatWith) (fresh_names, (ps : FinalPPlus.pplus FinalPPlus.pattern list))
              val (names, guards) = ListPair.unzip ns_gs
          in (List.concat names @ fresh_names, List.concat (guards :  V.vminus FinalVMinus.guard list list))
          (* final form is n => vc n1 ... nm, translatePatWith n1 p1 ... translatePatWith nm pm *)
          (* n = vc applied to fresh names, then map translatePatWith each name, each of ps *)

          end
          | P.ORPAT (p1, p2) => 
            let val (names1, guards1) = translatePatWith n p1 
                val (names2, guards2) = translatePatWith n p2
            in (names1 @ names2, [V.CHOICE (guards1, guards2)])
            end 
          | P.PATGUARD (p', e) => 
          let val n' = freshNameGen ()
              val (names, guards) = translatePatWith n' p'
          in (n'::names, V.EQN (n, translate e)::guards)
          end
          | P.PATSEQ (p1, p2) => 
            let val (names1, guards1) = translatePatWith n p1 
                val (names2, guards2) = translatePatWith n p2
            in (names1 @ names2, guards1 @ guards2)
            end 
        in (freenames @ local_names, local_guards)
        end 
         
                    (* introduce them as necessary with existentials *)
                    (* bind them - ns comes from patFreeNames *)
                in  if alreadyName 
                    then typecheck ()
                    (* VM.IF_FI internal *)
                    else Impossible.unimp "todo"
                    (* VM.IF_FI [VM.EXISTS (name, VM.EQN (name, e', 
                                   VM.ARROWALPHA (VM.IF_FI internal)))]  *)
                end 
  (* datatype 'e multi = MULTI of 'e list
    datatype 'e guard = EQN of name * 'e
                    | CONDITION of 'e
  datatype ('e, 'a) if_fi = IF_FI of (name list * 'e guard list * 'a) list

  datatype vminus = C of vminus Core'.t
                  | I of (vminus, vminus multi) if_fi *) *)


end