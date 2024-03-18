structure SimplePattern = struct
  type vcon = string
  type name = string
  datatype atom = VAR   of name
                | WILDCARD
  datatype pat = APPLY of vcon * atom list
               | ATOM  of atom
    (* N.B. a pattern for literal integer k is represented
       as APPLY (Int.toString k, [])  *)
end

signature SIMPLE_CASE = sig (* elimination form for constructed data *)
  datatype atom  = datatype SimplePattern.atom
  datatype pat = datatype SimplePattern.pat
  type name = Pattern.name
  type 'exp t = 'exp * (pat * 'exp) list
  val map : ('a -> 'b) -> ('a t -> 'b t)
  val fold : ('exp * 'a -> 'a) -> 'a -> 'exp t -> 'a
  val free : ('exp -> name Set.set) -> ('exp t -> name Set.set)
  val liftError : 'a Error.error t -> 'a t Error.error
  val mapError : ('a -> 'b Error.error) -> ('a t -> 'b t Error.error)
  val exists : ('a -> bool) -> 'a t -> bool
end

structure SimplePatUtil :> sig
  val bound : SimplePattern.pat -> SimplePattern.name list
  val embed : SimplePattern.pat -> Pattern.pat
end
  =
struct
  structure P = SimplePattern
  fun atom (P.VAR x) = SOME x
    | atom P.WILDCARD = NONE
  fun bound (P.APPLY (_, pats)) = List.mapPartial atom pats
    | bound (P.ATOM a) = List.mapPartial atom [a]

  fun embed (P.ATOM a) = atom a
    | embed (P.APPLY (vcon, atoms)) = Pattern.APPLY (vcon, map atom atoms)
  and atom (P.VAR x) = Pattern.VAR x
    | atom P.WILDCARD = Pattern.WILDCARD

end


structure SimpleCase :> SIMPLE_CASE = struct
  datatype atom  = datatype SimplePattern.atom
  datatype pat = datatype SimplePattern.pat
  type name = Pattern.name
  type 'exp t = 'exp * (pat * 'exp) list
  fun map f (e, choices) = (f e, List.map (fn (p, e) => (p, f e)) choices)
  fun fold f z (e, choices) = List.foldr (fn ((p, e), z) => f (e, z)) (f (e, z)) choices

  fun free subFree (e, choices) = 
    let fun freeChoice (p, e) = Set.diff (subFree e, Set.ofList (SimplePatUtil.bound p))
    in  Set.union' (subFree e :: List.map freeChoice choices)
    end

  fun liftError (Error.ERROR msg, _) = Error.ERROR msg
    | liftError (Error.OK e, choices) =
        let fun choice (p, Error.OK e) = Error.OK (p, e)
              | choice (_, Error.ERROR msg) = Error.ERROR msg
        in  case Error.list (List.map choice choices)
             of Error.OK choices => Error.OK (e, choices)
              | Error.ERROR msg => Error.ERROR msg
        end

  fun mapError f = liftError o map f

  fun exists p (e, choices) = p e orelse List.exists (fn (_, e) => p e) choices
end

