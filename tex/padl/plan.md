For next iteration: 

- Polish 
- More context and explanation for the technical parts 

Scratch:

- [ ] improve syntax 
- [ ] benchmarks 
- [ ] Beef up technical details as suggested

- [x] make a doc from scratch, skip intro 


Things to point out:

2. Things to do :
- [x] Workshop the title

- [ ] intro: fancy pm is nice, there are standard ways but not unified, there
  are other examples like vc and the ultimate, we’re looking at a compromise.
  contribution is core calculus that is very small yet quite expressive.
- [ ] Section 2: just examples
- [ ] PM extensions are good. here are 3 examples:
- [ ] But not unified/haskell/whatever
- [x] Cut section 3
- [ ] 3. Go straight to Vminus - grammar, opsem, examples.

- [ ] IT'S JUST AS EXPRESSIVE. AND MORE. 

- [ ] Continue to cut relation to verse, but say “Verse is significantly more
  expressive because of the backtracking. The point is to explore the design
  space in the middle: existential quantifier and overload =, but retain
  compilability to decision tree”

- [ ] V- has nonlinear patterns by default from the existential quantifier -
they know about nonlinear patterns, so explain only briefly. “V- supports the
common ones, and there are even more that you get for free”

- [ ] Talk about coverage checking: 'when' makes this NP-hard; here is work on 
how to do some. future work integrates this into V-. 


- [ ] 4. Compilation- d syntax (semantics are straightforward, cite with
  semantics.)
- [ ] a. the target language
- [ ] b. the compiler : the rules, the english script
- [ ] 5. evaluation (steve will think on how to express correctness)
- [ ] a. definitely 24 microbenchmarks
- [ ] b. performance: decision trees are height-bound. exact shape depends on
  heuristics, as is well known, here are how mine adhere to that, where the
  knobs work

V- and D sections
- [ ] Include which heuristics, why they matter: reduction strategies (in eval and analysis?)
- [ ] V- syntax, semantics
- [ ] Definitely english explanation of D-compile rules
- [ ] Syntax of d, say sem are obvious
- [ ] Coherent translation between them

- [ ] 6. discussion, future work, related work, etc
- [ ] talk about https://dl.acm.org/doi/pdf/10.1145/3689746 - write enough of a
  summary for comparison


- [ ] EVAL:
- [ ] Call it “Evaluation and Analysis”
- [ ] 24 micro benchmarks: {side conditions, or patterns, guards, nonlinear
  patterns} powerset
- [ ] Heuristic affects code size but never affects the height. Point to NR
  paper, then say how mine is different
- [ ] It’s well-known that any match compiler with a heuristic can be given a
  pessimal example.
- [ ] Proof sketch of decision tree height boundedness
- [ ] High-level:
- [ ] Exploring the design space, do it by enumerating all the features people
  want, then present solution, expressivity, compilation to decision trees.
- [ ] Discussion: how does this compare to traditional PM? Then look at PPlus.
  PP to D is established.

  


GOALS:
- REALLY strong examples: Stephanie: "Examples can make or break a paper."

0 abstract : 1 par
- PM is good and well studied. But extensions to PM are hard to get to work
  together: only in 2023 did GHC get or-patterns, OCaml still doesn't have
  full pattern guards, etc. 
  - Verse calculus shows concise, powerful syntax in choice and =, but it's 
  unintuitive and can be slow. Can we use it to make decisions instead? 
  - Read: THE ULTIMATE CONDITIONAL SYNTAX
  - Here we show:
  a. how putting all extensions to pattern matching makes for 
  more brief examples (short and long ex), 
  
  b. how V- does just the same (short and long ex), 
  
  c. at no extra cost (match compiler)

  Lokey it's decent. 

1 intro, short but very important : 2-3 par, about 1 page 
    Same as abstract, but elaborate on evalutation and match compiler. 

2 BRIEF pm, rich examples : 1-2 p
PM is good, but there are lots of pessimal examples: 
lack of side conditions, lack of guards, lack of or patterns... 

Languages have some of these, but only haskell has all, and only recently...
plus examples of all in a strict semantics has all of them. 

3 BRIEFER vc : 1 p Verse calculus is neat, but semantics of choice are
unintuitive (launch the missiles) and unification can be slow (source?). 

3.5 pplus : 1.5 p

Solution1: throw everything in a basket. how is it with the 4 given examples? 

4 vminus is the focus : 1.5-3 p 

Solution2: v- is nice at doing this all very easily. 

5 vminus to d is the focus : 1.5-3 p 

... at no extra cost. 

6 evaluation: 2-3 p

Most important: on a large functional example, v- is at least as good as 
P+. 

6 conclusion, fd, citations : remaining 1-2 pages
total 15. done 

\rab{fix odd page indentation}