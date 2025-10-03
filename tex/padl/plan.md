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

