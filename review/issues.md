Issues marked in bold are especially important. 

(These comments apply to a PDF with the MD5 checksum of `a560eac7bd66bd4f7914cf389c4e448c`.)


Abstract
--------

- [x] line 9: turn "fail to express" into a positive, e.g., certain computations can only be expressed verbosely

- [x] line 9, "extensions": begin with the old information: the problem can be resolved by extensions

- [ ] line 10: I don't know what "unified" means.  Extensions aren't an actor, so they are the wrong subject.

- [ ] lines 13 to 15: last two sentences, rewrite. Begin with the old info: to resolve these problems, you propose a new language v-minus, which has two desirable properties.  Then swap the order of the properties so it matches the earlier order (expressive power before cost model).

Milod: 

- [ ] Abstract: Overall good and to the point. I would only alter the final two sentences to make it clear that these are your contributions, rather than facts established by someone else. Consider changing to: "I formalize Verse as V-, a core language that uses Verse’s equations with some restrictions, and show that it can be compiled to a decision tree. I also show that V- subsumes P+, a core language with three popular extensions to pattern matching."


Introduction
------------
- [ ] line 21: Luc Maranget should appear on this list.  Also, if you can do it, chronological order is better than alphabetical here—it tells the story of development.

- [x] line 29: I'd put the important word "succinctly" at the end of the clause.

- [x] lines 29 to 34: swap the last two points: before presenting the solution (extensions), elaborate the problem.

- [ ] line 35: "unified" again.

- [ ] lines 43 and 44, information flow: put old info at the beginning, new info at the end.

- [ ] line 45: main verb should be the important action: "deconstruct".  Not "shed".

- [x] line 51, grammatical subject: "and expressions can backtrack..."

- [x] line 53, "harmonize"?  Could strike this sentence.

- [ ] lines 53 to 55: **Thesis statement is not strong enough,** or is insufficiently well signposted.  You could repurpose the previous sentence.  E.g., "In this thesis, I show that the expressive quality of Verse's equations and the decision-tree property of patterns can be combined in a single language."

- [ ] lines 55 and 57: pick one: "demonstrate" or "show"

- [ ] lines 59 to 66: don't claim these as contributions.  I might try "To make the demonstration convincing, I have formalized, ..., and I have implemented ..."

Milod: 

- [ ] Line 20: cut words "in academy"
- [ ] Line 37: "ad hoc" probably more precisely captures what you mean than "ad infinitum"
- [ ] Line 42: " it might be nice" is a bit too casual, as well as too uncertain of yourself.
- [ ] Line 43: As this is the first time you are mentioning "Verse", you should explicitly say "the programming language Verse"
- [ ] Line 47:  the use of the words "look" and "it appears at a glance" are throwing me for a loop here. Is there a reason for the uncertainty? If not, use more assertive wording. If there is a reason, make that reason a tad more explicit.
- [ ] Line 53: Change from passive to active voice, e.g., something like "I aim to harmonize the expressive ...." Also, "harmonize" is a bit confusing here; maybe use "marry" or "combine"
- [ ] Line 57: "demonstrate how" -> "show that"
- [ ] Line 61: Looks like the macros for V- and P+ need an extra space character at the end of them. If you \usepackage{xspace}, you can add the \xspace command to the end of the macros. This "smartly" adds space only when necessary (and not when, e.g., the macros is followed by punctuation).
- [ ] Lines 59-66: A bit nitpicky, but consider reordering this list of contributions to match the orders of the sections you cite (so P+ first, then decision trees, then Verse).



Section 2
---------

Milod: 
- [ ] Line 70: "flush out" -> "expand on"
- [ ] Line 85: nix "manually"
- [ ] Line 88: "function" -> "functional"
- [ ] Line 89: Consider cutting "I claim to know..." sentence entirely. Then, you can say "I list some reasons why below, and I refer to these as ..."
- [ ] Line 97: bullet point (4) is a bit confusing... consider rephrasing
- [ ] Line 104: A bit off track here but... you state that the shapes are represented by their side lengths, but the subsequent area function refers to the heights of the TRIANGLE and TRAPEZOID shapes—the height is not (necessarily) the length of a side.
- [ ] Line 160: Many languages have constructs that will provide observer functions for free, e.g., Scheme's records. Argument (3) here strikes me as a bit flimsy for that reason, and I think your case is just as strong without it.
- [ ] Lines 154-160: The use of "Good!" and "wins" are fun but perhaps a bit too fun :). May want to cut these and keep things concise and to the point.
- [ ] Line 195: nix second "common" here
- [ ] Line 210: nix "Let's dive in"
-Throughout: instead of the "-", you should use the traditional (longer) emdash "—". In latex, that's three dashes in a row, "---"
- [ ] Line 236: "are" -> "am"
- [ ] Line 356: "much appear simpler" typo here
- [ ] Lines 389-397: unnecessary whitespace here
- [ ] Line 402: "how fun I'd" typo here
- [ ] Line 448: "dissimilarity" -> "different"
- [ ] Lines 481-484: need rephrasing here—it sounds like Figure 8 is the one with "uninteresting code" when really you mean to point to Figure 8 as the solution. Also, somewhere you should explicitly say what or patterns actually are.
- [ ] Line 489-490: a bit to familiar with the reader here—reads more like a tutorial than a scientific paper.
- [ ] Lines 517-524: drop the mention of "I spotted", and instead say directly that Verse offers an alternative. Also, it seems like you are already introducing the next section here. This paragraph may be more at home in the following section rather than in this one.

-Section 2.1 and 2.2 general comment: These sections are quite long. I'm a bit torn on this. in a typical conference/workshop paper, this would be too much time spent explaining subjects that are not your own contributions. On the other hand, you do a very good job of explaining how pattern matching and these various extensions work. As I mentioned earlier, this reads a bit more like a tutorial than a scientific paper. The reason I'm torn is: I do not know whether or not this style is common in an honor's thesis. This is probably something to check in with Norman about.

- [ ] Line 545: use an inline citation rather than saying "the Verse paper"
- [ ] Line 546: nix "to your pattern matching-accustomed brains"
- [ ] Line 557: I believe this is the first time you use the term "unification." You should define it explicitly.
- [ ] Line 562: "for me to cover in this paper" -> "to cover here"
- [ ] Line 567: "real, written Verse code." -> "Verse"
- [ ] Line 535 (the Fig 9 example): should "x" be "s" here?
- [ ] Line 571: nix "good old"
- [ ] Lines 577-580: I would get rid of "I prefer" and rephrase the claim. It's easy to support the particular claim you've stated if it's just a preference! You want to assert something more detached from yourself.
- [ ] Line 583: "math-y" -> "relies more on mathematical notation"
- [ ] Line 603: do not ask "Do you remember how...." Instead, just cite the section you are referring to.

(will return to if there's time)

- [ ] line 555, use singular: "Every equation ... takes"

Section 3
---------
- [ ] line 663: feels startling because information flow is reversed.  You want "to bridge the gap ... I have created ..."

- [x] line 655: "all the extensions above"

- [ ] **lines 663 to 667: This part appears to put D on the same footing as the other two.  That won't do.  Fix it two ways: fix the information flow, and put D in a separate sentence: "To model pattern matching with extensions, I introduce P+.  To model programming with equations, I introduce V-.  And to provide an efficient cost model to which both P+ and V- can be compiled, I introduce D."**

- [ ] lines 666 and 667, "without backtracking or multiple results": The ice is thin here.  Given that V- has a form of choice, it's not obvious to me that there's never any backtracking.  Is it impossible to express backtracking?  Or does the match compiler reject programs that require backtracking?

- [ ] line 671: **bogus figure refs X, Y, Z**

- [ ] line 677: correct the main verb (e.g., "I present")

- [ ] line 679: bad reference: **"Figure 1" is not only not Figure 1, but it seems not to exist.**

- [ ] line 678: Give the unifying language its name (U).

- [ ] line 685: compound modifiers must be hyphenated: "lambda-calculus term"

- [ ] line 688: singular.  "Every expression is evaluated when ..."

- [ ] line 690, typing: typed intermediate code and typed assembly language are very much a thing.  Just try "typing for low-level languages like D is outside the scope of this thesis."




- [ ] line 727: garden-path sentence.  Rewrite.

- [ ] line 730: "although pattern guards subsume, ... I include ..."  (note change of number in subject).

- [ ] line 735: Eventual discussion should include Maranget's algorithm, which works by generalizing a single pattern to a set/sequence/matrix.


- [ ] lines 739ff: **Very rough transition.  This needs to be fixed.**  Needs an informal intro (what is the semantics going to tell us).  And metavariables should go into a figure, not the main text.

- [ ] lines 763 to 768: **Desperately needs a concrete example.** Draw something from section 1.

- [ ] lines 772ff: Each sentence after a bullet should be capitalized.

- [ ] line 776: "disjoint union" needs an explanation with an example.

- [ ] line 787: s/introducing/introduce/

- [ ] line 812: **Transition from English to formalism is too abrupt.**

- [ ] line 816: combine sections: form of judgment should not be in a different section from its rules.

- [ ] line 927: put the new info (figure 12) at the end.

- [ ] line 931: Explain the value-constructor thing after line 697.   With examples.  And justification:

  - Explain the value model.

  - Note that in full languages, numbers and strings have a similar status to value constructors, but their presence would complicate your development (of semantics and code).
  
  - But using just value constructors, we can simulate some interesting stuff.  For example, "Wow! That's a Tall Square."  (And explain what that syntax means.)
  
- [ ] line 927: Make it clear that the examples in Figure 12 compile.

- [ ] lines 939 to 932: Simplify.  And forget the parser—blaming limitations on the parser just makes you look bad.  1. As explained above, use value constructors.  2. P+ has no infix operators, so parenthesized.

- [ ] line 961: In the caption, also make it clear that the examples in Figure 12 compile.

- [ ] line 937: Strike the subordinate clause: "P+ admits of ..."

- [ ] lines 936 to 982: **This section isn't germane to your thesis.** Move it to an appendix.



- [ ] lines 986 to 989, verbs.  "The elements of VC that lead to unpredictable or costly run times are backtracking and multiple results."  (Main verb "to be" chosen in order to end the sentence with the topic of the paragraph.)

- [ ] lines 989 to 993, keep one subject: "Removing ... strips ... but it leaves VC's equations ..."

- [ ] lines 994 to 998: **I can't reconcile this claim with the figures.**  It looks like choice is permitted only in `if ... fi`.  And I don't see `one`.   In any case, "drawn to harnessing" needs to be related to your thesis and to be connected with examples.  Instead, I suggest you cut it.

- [ ] line 999: s/imagine/propose/

- [ ] line 1015: This claim needs to be substantiated.  First with an example, then later with a theorem and a proof.

- [ ] line 1021: the proper citation for guarded commands is as follows:

```
@book{dijkstra:discipline,
  publisher = {Prentice Hall},
  title = {A Discipline of Programming},
  address = {Englewood Cliffs, NJ},
  author = {Edsger W. Dijkstra},
  year = {1976},
}
```

- [ ] lines 985 to 1025: this page isn't working for me.  Let's talk about it tomorrow.

- [ ] lines 1026 to 1045: I don't see a way for a reader to compare V- with P+.  Since they are almost the same, that's a problem.  Consider returning to the unified figure.

- [ ] line 1052, singular: "A programmer can..."

- [ ] line 1061: "previous problems" needs a page reference.

- [ ] line 1064: Either substantiate the claim (by pointing out the similarities and differences), or drop it.

- [ ] lines 1092ff: subsection 3.7 belongs in the discussion section.

- [ ] line 1113: yes, definitely examples.  In the discussion section.

- [ ] line 1117: same issues with transition as were present with P+.  When fixing both, use parallel structure.

- [ ] line 1140: singular "expression," please.

- [ ] line 1141: needs examples (just one instance apeice).

- [ ] line 1143: **rho-hat doesn't look like a value.**

- [ ] line 1153: wrong actors here.  "We" don't do anything.  It may be better to start here: "Like VC, V- has a nondeterministic semantics." Then continue with a comparison.  (E.g., if no progress, Verse hits a normal form but V- gets stuck?)

- [ ] line 1160: singular.  An environment maps each name either to a value v or to ⊥.  Then explain what a binding to ⊥ represents.

- [ ] line 1161, refine or reject: needs examples.

pages 28 and 29: perhaps there are too many subsections here.

- [ ] line 1327: D is actually quite practical.  It's a very minor tweak of P: you give up the ability to write nested patterns, but you gain a deterministic and perspicuous cost model.

- [ ] line 1330: Not sure I'd use "invariant" here.  Perhaps, "one key property of the cost model is ..."

- [ ] lines 1332 to 1335: Too vague.  Concretely, there are two points to be made.  1. The worst-case cost of evaluating a decision tree is linear in its depth.  2. When a decision tree is produced by compiling P, there are pathological cases in which the total size of the tree is exponential in the size of the source code (from P).  Run time remains linear, but code size may not be.
