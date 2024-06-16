- We will use the translation of uML to vml as a basis for vml. 

`translate : P -> V`

For our language, we have

`vml == (uML - P) + V-`

, where `P` is the set of all patterns and case expressions in uML, and `V` is the set of 
all equations and solvers. 

Our translation need only cover `P`; in layperson's terms, we
can construct our language out of the uML initial basis with the
translation `P -> V` applied to all pattern-like forms. So, 
we have 

`vml == uML` _with_ `P -> V`

`vml == uML` _with_ `case -> if ... fi`

Within case, we have our pattern forms. These become our new "equation-like" forms 

If we want a complete translation from uML to vml, we have a function that is the identity for all expressions in uML except those involving patterns, and it `P -> V` for those rest. 

`fulltranslate : uML_def list -> vml_def list`

```
fulltranslate uML_def = 
    case uML_def  
        of pattern_form => p_to_v pattern_form
         | UML_EXP (components) => VML_EXP (fulltranslate components)
```
where p_to_v is `P -> V`, `pattern_form` is a pattern or case expression. 