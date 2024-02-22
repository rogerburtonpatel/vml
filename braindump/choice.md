--intro--


// hmm. a is unbound here. 
if 
E x b a. x = (One a | Two b); -> a + b
fi


// how do you sort this? 
if 
E x b a. x = (One a | Two b); a = 2; -> a
fi


// design space: when 'a is bindable in e1 | e2', must a be bound in both 
e1 and e2, or only 1? 

// how do you sort this? 
if 
E x a. x = (a > 7); a = 2; -> a
fi

// how about this? 
if 
E x b a. x = (One a | Two b); x = Two b; -> a
fi

// how about this? 
if 
E x. x = (3 | 4); x = 4; -> x
fi

// and this? 
if 
E x. x = (3 | 4); x = 5; -> x
fi

// maybe in sorting all non-choice bindings come before choice. 
// solving involves actively 'choosing one' - the same as we do in sorting. 

// third example seems sortable with that in mind to this:
if 
E x b a. x = Two b; x = (One a | Two b); -> a // this is an error and it should be 
fi



// BIG question: must if-fi start on a programmer-given scrutinee? 

if (E x a. x = One a)
E b. x = (One a | Two b); a = 2; -> a
fi


if (E x. x = One 1) // <- STARTING INFORMATION
E a b. x = (One a | Two b); a = 2; a = 3; -> 77
fi

// emit warning: no path to final value of this guard. to hope for in mc. 


// Prior, I had 


// PREP for MC: 

- Algebraic laws around choice in

Exmaple: if (p1 | p2) ... -> e fi   === if p1 ... -> e [] p2 ... -> e fi

Compiler for choice-free subset 


