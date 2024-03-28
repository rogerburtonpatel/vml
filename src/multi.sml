structure Multi :> sig 
  datatype 'e multi = MULTI of 'e list
  val multiString :    ('e -> string) -> 'e multi -> string
  val map : ('a -> 'b) -> 'a multi -> 'b multi 
end 
  =
struct 
  datatype 'e multi = MULTI of 'e list
  fun multiString (f : 'e -> string) (MULTI es) = String.concat (map f es) 

  fun map f (MULTI es) = MULTI (List.map f es)

end
