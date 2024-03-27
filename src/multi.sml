structure Multi :> sig 
  datatype 'e multi = MULTI of 'e list
  val multiString :    ('e -> string) -> 'e multi -> string
end 
  =
struct 
  datatype 'e multi = MULTI of 'e list
  fun multiString (f : 'e -> string) (MULTI es) = String.concat (map f es) 

end
