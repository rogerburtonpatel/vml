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
  val strOfCoreValue  : 'a core_value -> string 
  val strBuilderOfVconApp : ('a -> string) -> vcon -> 'a list -> string
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


                     

  fun strBuilderOfVconApp f n args = 
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
     strBuilderOfVconApp expString n es 
    | expString (LAMBDAEXP (n, body)) = 
        StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
    | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2

  fun strOfCoreValue (VCON (v, vals)) = 
          strBuilderOfVconApp strOfCoreValue v vals 
    | strOfCoreValue (LAMBDA (n, e)) = 
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


  fun strBuilderOfVconApp f vc args = 
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
    strBuilderOfVconApp expString n es 
  | expString (LAMBDAEXP (n, body)) = 
      StringEscapes.backslash ^ n ^ ". " ^ (expString body) (* backslash *)
  | expString (FUNAPP (e1, e2)) = expString e1 ^ " " ^ expString e2
  | expString (E e) = Impossible.unimp "print an extended expression with a helper"

end



structure NewPPlus =
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
             datatype 'a extension = IF_FI of 'a guarded list)



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

structure StandardTransformer = struct
  open ExtensibleCore (* to rename a type *)
  type 'a plus_standard = 'a exp
end

structure VMinusXXX = struct
  open MultiTransformer  open StandardTransformer (* to make a point *)
  open VMinusTransformer
  open SplitVMinusTransformer
  datatype exp = E of (exp plus_standard, exp plus_standard plus_multi) plus_split_if_fi
end



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
