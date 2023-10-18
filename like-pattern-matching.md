The first code example in the Verse paper strikes me as "unlike pattern 
matching." 

$\exists x, y, z. x = \langle y, 3 \rangle; x = \langle 2, z \rangle; y  $ 

After analyzing it and other examples, I realized it had several
unique properties that were unlike `case` expressions: 

1. There was no clear scrutinee 
2. Logical variables depended cyclically on each other to determine their values

I made two conjectures: 

1. Cycles between logical variables meant it was not possible 
to use a literal as the scrutinee in a decision tree; one 
would have to scrutinize logical variables
2. Because these cyclically dependent logical variables can 
change depending on where in the unification process the 
program is, they cannot be reliably used as the scrutinee in a
pattern match. 

As such, one idea that gets two birds stoned at once is to 
answer two of our leading questions: 

1. What does it mean for a subset of verse to be 
"like pattern matching?"
2. What are the Verse terms we want to rule out because they're 
not sufficiently like pattern matching? 

by making three claims:
1. It is unlike pattern matching to have logical varaibles at runtime.
2. If we can compile our equations to decision trees with values as scrutinees, there need not be logical variables at runtime. 
3. Cycles between logical variable dependencies prevent compilation to 
decision trees, because the variable dependency graph isn't a DAG. 


By traversing variable dependencies, we can identify if there are cycles 
between them. If there are, we cannot guarantee compilation to a decision 
tree. 

Hence, in our subset $V^-$, we can design a form of data that creates 
restrictions on logical varaibles.

```
value_bound_var = 
      VALUE of value
    | FORMAL of name
    | LV_BINDING of logical_variable * value_bound_var 
```
(this structure must be expanded to include tuples and other data structures that hold logical variables)

We include `FORMALS` here a terminating case for logical variable bindings because we know lambdas will $\beta$-reduce to substitute formals with values.

By traversing this structure to its terminating case, we can be assured 
that our graph contains no cycles. Because it is directed by nature of 
dependency flow, it is then a DAG, and we can be certain of valid 
compilation to decision tree. 

Let's look at the paper's _append_: 

append := 𝜆⟨𝑥𝑠, y𝑠⟩. ((𝑥𝑠 = ⟨⟩; y𝑠) | (∃x xr. 𝑥𝑠 = ⟨x, xr⟩; ⟨x, append⟨xr, y𝑠⟩⟩))

In the first, branch all we see are formals and values: good. In the second, 
In the second, we see new logical variables $x$ and $xr$ bound to the formal $xs$: fine. 


Let's look at a translation of a nested pattern: 

```
case pair of 
    (xs, SOME z) => z::xs
```

Our translation is: 
$(\textbf{one}\{(\exists xs, y, z. \texttt{pair} = (xs, y);  y = \texttt{SOME}  z; \lambda \langle\rangle. z::xs  | \textbf{wrong}\})\langle\rangle$

We can see $xs$ and $y$ are depend on $\texttt{pair}$, a formal - all good. 
And $z$ depends on $y$, which is only OK because $y$ depends on $\texttt{pair}$.
By following our dependency graph upwards, we can see it is a DAG, and our 
equation can therefore be compiled to a decision tree with a value as the 
scrutinee. 
<!-- Because all logical variables must be _somewhat_ value-restricted
(the following is not valid Verse):

$\exists x.  x$  -->

