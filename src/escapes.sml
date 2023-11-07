structure StringEscapes :> sig
  val charInString : char -> string
    (* escape a single character as for a C string literal,
       except the possibility of a trigraph is ignored *)
  val quote : string -> string
    (* quotes the given string as for C.  Trigraphs are supported. *)
end
  =
struct

  fun charInString #"'" = "'"
    | charInString #"?" = "?"
    | charInString c    = Char.toCString c

  fun withTrigraph #"'" = "'"
    | withTrigraph c    = Char.toCString c

  fun quote s =
    let val tx = if String.isSubstring "??" s then withTrigraph else charInString
    in  String.concat ["\"", String.translate tx s, "\""]
    end

end        
