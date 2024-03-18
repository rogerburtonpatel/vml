structure Pattern = struct
  type vcon = string
  type name = string
  datatype pat = APPLY of vcon * pat list
               | VAR   of name
               | WILDCARD
    (* N.B. a pattern for literal integer k is represented
       as APPLY (Int.toString k, [])  *)
end

signature CASE = sig (* elimination form for constructed data *)
  datatype pat = datatype Pattern.pat
  type name = Pattern.name
  type 'exp t = 'exp * (pat * 'exp) list
  val map : ('a -> 'b) -> ('a t -> 'b t)
  val fold : ('exp * 'a -> 'a) -> 'a -> 'exp t -> 'a
  val free : ('exp -> name Set.set) -> ('exp t -> name Set.set)
  val liftError : 'a Error.error t -> 'a t Error.error
  val mapError : ('a -> 'b Error.error) -> ('a t -> 'b t Error.error)
  val exists : ('a -> bool) -> 'a t -> bool
end

signature CONSTRUCTED = sig (* introduction form for constructed data *)
  type vcon = Pattern.vcon
  type name = Pattern.name
  type 'exp t = vcon * 'exp list
  val map : ('a -> 'b) -> ('a t -> 'b t)
  val fold : ('exp * 'a -> 'a) -> 'a -> 'exp t -> 'a
  val free : ('exp -> name Set.set) -> ('exp t -> name Set.set)
end

structure PatUtil :> sig
  val bound : Pattern.pat -> Pattern.name list
end
  =
struct
  structure P = Pattern
  fun addBound (P.APPLY (vcon, pats), vars) = foldr addBound vars pats
    | addBound (P.WILDCARD, vars) = vars
    | addBound (P.VAR x, vars) = x :: vars
  fun bound p = addBound (p, [])
end


structure Case :> CASE = struct
  datatype pat = datatype Pattern.pat
  type name = Pattern.name
  type 'exp t = 'exp * (pat * 'exp) list
  fun map f (e, choices) = (f e, List.map (fn (p, e) => (p, f e)) choices)
  fun fold f z (e, choices) = List.foldr (fn ((p, e), z) => f (e, z)) (f (e, z)) choices

  fun patBound (APPLY (_, ps)) = Set.union' (List.map patBound ps)
    | patBound (VAR x) = Set.singleton x
    | patBound WILDCARD = Set.empty


  fun free subFree (e, choices) = 
    let fun freeChoice (p, e) = Set.diff (subFree e, patBound p)
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

structure Constructed :> CONSTRUCTED = struct
  type vcon = Pattern.vcon
  type name = Pattern.name
  type 'exp t = vcon * 'exp list
  fun map f (con, es) = (con, List.map f es)
  fun fold f z (con, es) = List.foldr f z es
  fun free subFree (con, es) = Set.union' (List.map subFree es)
end

