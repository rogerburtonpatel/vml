structure Tree :> sig 
    type vcon = string 
    datatype data = CON of vcon * data list
end = 
struct
    type name = string 
    type exp  = int 
    type vcon = string 
    type data = vcon * int * name list
                        (* ^ arity *)
    datatype pattern = VCONAPP of data * name option 
    datatype 'a tree = MATCH of 'a 
                     | TEST of name * pattern list * 'a tree
                     | IF of name   * 'a tree      * 'a tree 
                     | LET of name  * exp          * 'a tree 



end


