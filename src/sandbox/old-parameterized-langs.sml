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

  val eqval           : 'a core_value * 'a core_value -> bool
  val boolOfCoreValue : 'a core_value -> bool 
  val expString    : core_exp -> string 
  val valString  : 'a core_value -> string 
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


signature EXTENDED = sig
  type name = string 
  type vcon  = Core.vcon
  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp
  type 'exp extension  (* all the expressions we don't care about *)

  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp extension  (* everything else *)

  val expString    : exp -> string 

end

functor MkExtended(type 'a extension (*solid*) ) :> EXTENDED where type 'a extension = 'a extension
  =
struct
  type name = string 
  type vcon = Core.vcon
  type 'a extension = 'a extension
  datatype 'exp value = VCON of vcon   * 'exp value list 
                      | LAMBDA of name * 'exp
  datatype exp = NAME of name 
               | VCONAPP of vcon * exp list
               | LAMBDAEXP of name * exp 
               | FUNAPP of exp * exp 
               | E of exp extension  (* everything else *)


  fun vconAppStr f vc args = 
  let val name = 
      (case vc 
        of Core.K n => n 
         | Core.TRUE => "true" 
         | Core.FALSE => "false")
      val vcss = foldr (fn (v, acc) => " " ^ f v ^ acc) "" args
        in name ^ vcss
    end 

  fun expString (NAME n) = n
  | expString (VCONAPP (n, es)) = 
    vconAppStr expString n es 
  | expString (LAMBDAEXP (n, body)) = 
      StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
  | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
  | expString (E e) = Impossible.unimp "print an extended expression with a helper"

end



(* OLD VERSIONS -- HALFWAY THERE *)

(* structure NewPPlus =
  MkExtended(type name = string
         datatype pat = NAME of name | APP of Core.vcon * pat list
         datatype 'a extension = CASE of 'a * (pat * 'a) list)

structure NewVMinus =
  (* shortcut: the expressions that can appear in a guard are the same
     as the ones that can appear on a right-hand side *)
  MkExtended(type name = string
             datatype 'exp guard = CONDITION of 'exp
                                 | EQN       of name * 'exp
             datatype 'exp guarded = GUARDED of name list * 'exp guard list * 'exp 
             datatype 'a extension = IF_FI of 'a guarded list)

structure SpeculativeVMinus =
  (* the expressions that can appear in a guard are _different from_
     the ones that can appear on a right-hand side *)
  MkExtended(type name = string
             structure ExpressionsInGuards =
               MkExtended(datatype 'a extension = EMPTY_EXTENSION of 'a extension)
             structure E = ExpressionsInGuards
             datatype guard = CONDITION of E.exp
                            | EQN       of name * E.exp
             datatype 'exp guarded = GUARDED of name list * guard list * 'exp 
             datatype 'a extension = IF_FI of 'a guarded list) *)



(*---------------*)

structure Sandbox = struct
  (*
  expL = core + if_fi(expL)
  expR = core + if_fi(expR)

  datatype guard = CONDITION of expL
                 | EQN       of name * expL


  if_fi(e) = IF_FI of (name list * guard list * e) list
  *)

(*

  structure ExpressionsInGuards =
    MkExtended(datatype 'a extension = EMPTY_EXTENSION of 'a extension)
  structure E = ExpressionsInGuards

  datatype 'exp guarded = GUARDED of name list * guard list * 'exp 
  datatype 'a if_fi = IF_FI of 'a guarded list

  datatype if_fi_in_guarded = I of if_fi_in_guarded if_fi
  datatype exp_on_rhs = EXP
  datatype if_fi_on_rhs     = I of  if_fi
*)

end


functor MkIf (type 'extension core) 
  =
struct
  type name = string
  datatype expL = L of expL core
                | IF_FI of (name list * guard list * expL) list
  and     guard = CONDITION of expL
                | EQN       of name * expL

  datatype expR = R of expR core
                | IF_FI of (name list * guard list * expR) list
end

functor MkIfParametric (type 'extension coreL
                        type 'extension coreR) 
  =
struct
  type name = string
  datatype 'exp guard = CONDITION of 'exp
                      | EQN       of name * 'exp
  datatype ('expL, 'expR) if_fi = IF_FI of (name list * 'expL guard list * 'expR) list

  datatype expL = L of expL coreL
                | IF_FI of (expL, expL) if_fi

  datatype expR = R of expR coreR
                | IF_FI of (expL, expR) if_fi
end




structure ExtensibleCore = struct
  type name = string 
  type vcon  = Core.vcon
  datatype 'extension exp = NAME of name 
                          | VCONAPP of vcon * 'extension exp list
                          | LAMBDAEXP of name * 'extension exp 
                          | FUNAPP of 'extension exp * 'extension exp 
                          | E of 'extension
end

structure MultiExtension = struct
  datatype 'e exp = CORE  of 'e exp ExtensibleCore.exp
                  | MULTI of 'e exp list
end

structure VerseX = struct
  (* knot-tying *)
  datatype exp = E of exp MultiExtension.exp
end

structure MultiTransformer = struct
  datatype 'a plus_multi = BASE of 'a
                         | MULTI of 'a plus_multi list
end

structure VMinusTransformer = struct
  type name = string
  datatype 'a guard = CONDITION of 'a
                    | EQN of name * 'a

  datatype 'a plus_if_fi = BASE of 'a
                         | IF_FI of (name list * 'a plus_if_fi guard list * 'a plus_if_fi) list
end

structure SplitVMinusTransformer = struct
  type name = string
  datatype 'a guard = CONDITION of 'a
                    | EQN of name * 'a

  datatype ('a, 'b) plus_split_if_fi
       (* 'b extended with if_fi, with guards in the set "'a extended *)
       (* with if_fi *)
     = BASE of 'b
     | IF_FI of (name list * ('a, 'a) plus_split_if_fi guard list * ('a, 'b) plus_split_if_fi) list
end

structure PPlusTransformer = struct
  type name = string
  datatype 'exp pattern = PATNAME of name 
                   | WHEN of 'exp 
                   | PATGUARD of 'exp pattern * 'exp 
                   | ORPAT of 'exp pattern * 'exp pattern 
                   | PATCONAPP of name * 'exp pattern list

  datatype 'a plus_case = BASE of 'a 
                        | CASE of ('a plus_case pattern * 'a plus_case) list
end


structure StandardTransformer = struct
  open ExtensibleCore (* to rename a type *)
  type 'a plus_standard = 'a exp
end

structure TrueVMinus = struct
  open MultiTransformer  open StandardTransformer (* to make a point *)
  open SplitVMinusTransformer
  datatype exp = E of (exp plus_standard, exp plus_standard plus_multi) plus_split_if_fi
end

structure TruePPlus = struct
  open StandardTransformer (* to make a point *)
  open PPlusTransformer
  datatype exp = E of exp plus_standard plus_case
end

structure DTransformer = struct 
  type name = string 
  type vcon = Core.vcon 
  type arity = int
  type labeled_constructor = vcon * arity

  datatype 'exp tree = MATCH of 'exp tree
              | TEST of name * (labeled_constructor * 'exp tree) list * 'exp tree option
              | IF of name   * 'exp tree * 'exp tree 
              | LET of name  * 'exp * 'exp tree 

  datatype 'a plus_tree = BASE of 'a 
                        | TREE of 'a plus_tree tree 

end 

structure TrueD = struct
  open StandardTransformer
  open DTransformer
  datatype exp = E of exp plus_standard plus_tree

end


val (x__ : TrueVMinus.exp) = TrueVMinus.E (SplitVMinusTransformer.BASE (MultiTransformer.BASE (ExtensibleCore.NAME "n")))

val test = (SplitVMinusTransformer.BASE (MultiTransformer.BASE (ExtensibleCore.NAME "n")))

(* PP -> VM *)

structure P = TruePPlus
structure VM = TrueVMinus
structure E = ExtensibleCore
structure PT = PPlusTransformer

fun vmOfPPex (e : TruePPlus.exp ExtensibleCore.exp) = 
Impossible.unimp "typecheck"

val _ = vmOfPPex : TruePPlus.exp ExtensibleCore.exp -> TrueVMinus.exp ExtensibleCore.exp

val tppexe = P.E (PPlusTransformer.BASE (E.NAME "n"))
val excorex = P.E (P.BASE (E.NAME "n"))
val excorex = VM.E (VM.BASE (MultiTransformer.BASE (E.NAME "n")))

(* fun vmOfPP (P.E (P.BASE (e : P.exp E.exp))) = 
let fun wrap ex = TrueVMinus.E (SplitVMinusTransformer.BASE (MultiTransformer.BASE ex))
in 
    case e of  
      E.NAME "n" => VM.E (VM.BASE (MultiTransformer.BASE (E.NAME "n")))
  (* |   E.VCONAPP (vc, es)  => wrap (E.VCONAPP (vc, map vmOfPP (es : P.exp E.exp list))) *)
  (* | LAMBDAEXP _ => _
  | FUNAPP _ => _
  | E _ => _ *)

  (* VM.E (VM.BASE exp) *)
          (* | P.CASE _ => Impossible.unimp "typecheck"   *)
  end *)



(* val _ = vmOfPP : TruePPlus.exp -> TrueVMinus.exp *)

structure LanguageKnotsTied = struct
  open MultiTransformer  open StandardTransformer (* to make a point *)

  (* the point: these two languages are equivalent: *)
  datatype exp  = E  of exp plus_standard plus_multi
  datatype exp' = E' of exp plus_multi plus_standard

  (* the conclusion: write all code to operate on language transformers,
     tie the knot only at the end *)

  (* list of transformers:
       - standard lambda, value constructors
       - if-fi
       - MULTI (placeholder for the full power of Verse)
       - decision trees
       - case matching
   *)

   (* list of languages
        p_plus  = p_plus + standard + case_matching
        v_minus = v_minus + standard + if_fi
        d       = d + standard + decision_trees

      datatype p_plus = E of p_plus plus_standard plus_case_matching 
      datatype verse  = E of verse plus_standard plus_multi
    *)

    (* translations
          val matchCompile : ('a -> 'b) -> ('a plus_if_fi) -> ('b plus_tree)
          val pPlusToVMinus : ('a -> 'b) -> ('a plus_case) -> ('b plus_if_fi)
     *)
end


structure VminusX = 
  MkIfParametric(type 'a coreL = 'a ExtensibleCore.exp
                 type 'a coreR = 'a MultiExtension.exp)

  
functor MkDecisionTreeTooSimple(type 'a core) 
  =
struct
  type name = string
  type vcon = Core.vcon
  type arity = int
  type labeled_constructor = vcon * arity

  datatype data = CON of vcon * data list
                  (* ^ arity *)
  datatype pattern = VCONAPP of data * name option 

  datatype path = CHILD of unit core * int

  datatype tree = MATCH of tree core
                | TEST of name * (labeled_constructor * tree) list * tree option
                | IF of name   * tree * tree 
                | LET of name  * path * tree 
end

functor MkDecisionTree(type 'a coreL
                       type 'a coreR) 
  =
struct
  type name = string
  type vcon = Core.vcon
  type arity = int
  type labeled_constructor = vcon * arity
  datatype data = CON of vcon * data list
                  (* ^ arity *)
  datatype pattern = VCONAPP of data * name option 

  datatype expL = COREL of expL coreL
                | CHILD of name * int

  datatype tree = MATCH of tree coreR
                | TEST of name * (labeled_constructor * tree) list * tree option
                | IF of name   * tree * tree 
                | LET of name  * expL * tree 

  datatype tree = MATCH      of tree coreR
                | TEST       of name * (labeled_constructor * tree) list * tree option
                | IF         of name * tree * tree 
                | LET        of name * tree coreL * tree 
                | LET_CHILD  of name * name * int * tree 
end

(*
  txCore  : ('a -> DEST) -> ('a core -> DEST)

  structure Dest = MkDecisionTree(type 'a core = 'a MultiExtension.exp)


  txVerse (VerseX.E (CORE e)) = txCore e
  txVerse (VerseX.E (MULTI m)) = ... translation of multi to DEST ...


*)

structure Core' = struct
    type name = string 
    type vcon = string
    datatype 'a t = NAME of name 
               | VCONAPP of vcon * 'a list
               | LAMBDAEXP of name * 'a 
               | FUNAPP of 'a * 'a 

  fun map (f : ('a -> 'b)) t = 
    case t of NAME n      => NAME n  
        | VCONAPP (vc, ts) => VCONAPP (vc, List.map f ts)
        | LAMBDAEXP (n, t) => LAMBDAEXP (n, f t)
        | FUNAPP (t1, t2)  => FUNAPP (f t1, f t2)
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

(* structure NewPPlus' = MkExtended(open PPlusExtension)

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
end *)






end