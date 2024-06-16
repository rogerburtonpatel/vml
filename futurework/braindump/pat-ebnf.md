p ::= term {| term}
term ::= factor {, factor}
factor ::= atom <- exp // pattern guard; expression results in atom
        | atom
atom ::= x | K {atom} | ❨p❩ | when exp

case x
    of Foo a, pat1, pat2, pat3 <- exp1, pat4 -> result

    // a factor can either be an atom bound from an explicit expression 
    // on the rhs of an <- OR it can just be a pattern, which succeeds if 
    // it matches the ORIGINAL scrutinee 


    C[[atom]] = C[[atom <- $SCRUTINEE]]
    T[[atom <- exp]] = [[atom']] `=` [[exp]]

