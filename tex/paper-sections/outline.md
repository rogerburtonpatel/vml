7To hit on: 
V- 
P+ 
Erlang
if-fi multiples == case multiples == sucks 
Why is verse "smooth?" examples 
Efficiency 


What can you write in V-minus (and compile efficiently to D) that
can't (easily) be expressed in P-plus?  Is there anything interesting there?
Section 1:

Section 2:

Etc:



INtro 

The Verse language looks more expressive than pattern matching. But a full
implementation of Verse must use logical variables at runtime, which can be
costly. We have identified a subset of the Verse Calculus that subsumes pattern
matching but does not require logical variables at runtime. Furthermore, we
demonstrate how full Verse can be written to "match the semantics" of this
subset and subsequently enjoy its performance benefits. 
(Likely rewrite- syntactic, static analysis)




- restricting is chill -> decision-making similar to pattern matching without
  the cost
- subset- syntactic 

static analysis 
and 


GOOO


Intro The Verse language looks more expressive than pattern matching. But a full
implementation of Verse must use logical variables at runtime, which can be
costly. We have identified a subset of the Verse Calculus that subsumes pattern
matching but does not require logical variables at runtime. Furthermore, we
demonstrate how full Verse can be written to "match the semantics" of this
subset and subsequently enjoy its performance benefits.

We make three main contributions. \bf{Our first contribution} is a syntax,
semantics, and implementation of a subset of Verse, which we call \Vminus
(pronounced V-minus), that imposes a few key restrictions that remove the
possiblity of logical variables at runtime. We also provide a comparison
language, P+, which has pattern matching with popular extensions. We go on to
show that V- is just Verse with syntactic restrictions, and we provide a static
analysis which identifies if full Verse programs abide by those restrictions. 


\bf{Our second contribution} is a translation from P+ to V- and one from V- to
"an intermediate representation involving decision trees", and a proof that 
the transformations are semantics-preserving. 

\bf{Our third contribution} is less formal: we present an argument that Verse,
beyond being as expressive as P+, is in many cases able to produce more elegant
programs. "We also show how some extensions to P+, when held alone, cannot
express what Verse can."



Indeed, we show that Verse's equations subsume a number of the popular
extensions to pattern matching. We finally claim that Verse's expressiveness
is part and parcel with the elegance of its programs and that: 

- Verse programs == short, eloquent, ez to express, sometimes more so than pm 
- Some things that extensions to pattern matching can't express, verse can. 


Contributions:
- \Vminus. We also provide a comparison language, P+, which has pattern matching
with popular extensions. We go on to show that V- is just Verse with syntactic
restrictions, and we provide a static analysis which identifies if full Verse
programs abide by those restrictions. 
- Translation from P+ to V- and from V- to D, proof of semantic preservation. 
- An argument that Verse is nice to program in, and sometimes nicer than P+


example 


We make x main contributions 
bold contributions 

Informally: differences between uVerse and Verse 

INtroducting the opposition: P+ 

Semantics 

