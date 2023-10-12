The practice of deconstructing composite data with pattern matching 
(specifically, with Tree patterns) is longstanding in the world of functional programming. 
The introduction of equation solving as a novel paradigm for data deconstruction 
within the new programming language Verse (Peyton Jones et al., 2023) therefore necessarily 
begs questions: What are the advantages of the new system? In what ways is it more or 
less expressive than pattern matching? And, for our purposes: What is the smallest subset of 
the Verse calculus that is as expressive as pattern matching? 
In our experiments, we have identified a subset of the Verse Calculus that subsumes pattern 
matching with popular extensions but does not require the full execution of the Verse language. 
We go on to claim that there are no programs generatable with the subset that cannot be created 
using pattern matching with popular extensions, implying set equality. 
We finally discuss notions of expressiveness in terms of decision trees, 
the parameters of this subset, and the Verse terms excluded from the subset. 



New Introduction:
---------
 
The Verse language looks more expressive than pattern matching. 

// Starting with verse good- establishes as subject. Pattern matching at end bc most important thing- good. 

But an implementation of Verse must use logical variables at runtime. 

// Shift to implmentation is eh- coherent subject is generally the same. 
// "Must use" is good. 

But at runtime, an implementation of Verse must use logical variables. 

We have identified a subset of the Verse Calculus that subsumes pattern 
matching but does not require logical variables at runtime. 

this is better than:

The introduction of equation solving as a novel paradigm for data deconstruction 
within the new programming language Verse (Peyton Jones et al., 2023) necessarily begs questions: What are the advantages of the new system? In what ways is it more or 
less expressive than pattern matching? And, for our purposes: What is the smallest subset of 
the Verse calculus that is as expressive as pattern matching? 


We go on to claim that there are no programs generatable with the subset that cannot be created 
using pattern matching with popular extensions, implying set equality. 


We finally discuss notions of expressiveness in terms of decision trees, 
the parameters of this subset, and the Verse terms excluded from the subset. 

 
- like pattern matching
- expresses PM with popular extensions (P+)
- expresses something not in P+
