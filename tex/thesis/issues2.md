More comments on PDF with MD5 checksum `a560eac7bd66bd4f7914cf389c4e448c`.


Section 4
---------
- [ ] line 1346: 4 "~~Section 2.4 claimed that~~ Pattern matching has a desirable efficiency property."

- [ ] line 1349: Paper titles aren't used. The authors are treated as actors.  So "MacQueen and Baudinet (1985) built the foundation for and Maranget (2008) expanded on."

- [ ] line 1348: Don't make the reader try to remember the connection between "decision tree" and "desirable cost model."  Say straight out that a decision tree makes a decision without ever examining any value more than once.

- [ ] line 1357: Strike "simple."  That's for the reader to decide.

- [ ] line 1360: It's not clear to the reader why an intermediate representation used in Maranget's algorithm should have any bearing on the representation of the final decision trees.  Make that connection clear and explicit.

- [ ] lines 1386 to 1388: The 1, 2, 3 is confusing.  Here and in Figure 17, stick with `ys`, `xs`, and `...`.  And consider expanding the `...` into `if x < y then x :: merge rx ys else y :: merge xs ry`.

- [ ] Section 4.1: I don't think Maranget's *algorithm* is important for your thesis, and I don't see any benefit to going into details.  Since the stack doesn't appear in Figure 17, you can get ride of that detail.

- [ ] Figure 17: The figure needs to be explained.  When presented with values `xs` and `ys`, how is the decision tree evaluated?  And where do the bindings of `x`, `rx`, `y`, and `ry` come from?

- [ ] line 1425: "scrutinee" needs to be explained here.  And the explanation moved to the front of section 4.

- [ ] line 1425: missing space after D

- [ ] Section 4.3: the first part of this section goes up front (start of section 4).

- [ ] line 1425: **This sentence is wrong.**  The cost property is established as follows: the match compiler must ensure that no test node T has any proper ancestor T' such that T and T' both test the same location in memory.

- [ ] lines 1431 to 1433: delete

- [ ] The rest of this section is too drafty to warrant further comment.


Section 5
---------
- [ ] line 1469: You've stepped into the Turing tar pit.  By itself, the existence of a translation proves nothing.  For example, you can certainly translate P+ to P, but that doesn't show that pattern matching subsumes its extensions.

- [ ] To substantiate a claim of subsumption, you must exhibit a translation that does more than just preserve semantics.  Typically one is looking for a translation that preserves some kind of structure.

- [ ] In this, case there's really only one goal that makes sense: the translation should preserve the *improvements* that are enabled by the extensions.  That is, whatever properties you are claiming for code written in P+ (elegance, concision, single point of truth), those properties must be preserved by the translation. **This is a key argument needed to support your thesis, i.e., that V- is a plausible alternative to P+.**

- [ ] At this point all of this is something of a heavy lift, and you might instead wish to support the claim somewhat informally.  (Unfortunately I don't think you can strike it all together.)


One solution: 

- [ ] Just know that if you can write nice code P+, you can write equally nice code in V-. 
- [ ] Can I prove it to you? No. Future work. 
- [ ] Equivalent examples. 
- [ ] Translation that's solid on no duplication but has other flaws. Fixing them in future work. 
- [ ] Say in future work. 

Section 6
---------
- [ ] line 1549: When you're this specific, the text needs to say "Verse Calculus" in full.

- [ ] line 1552: Missing a period after VC.

- [ ] line 1552: "An excellent" should start a new paragraph.  And the subject of the sentence should probably be "Extensions," which are old and familiar.

- [ ] line 1555: "Compiling" should start a new paragraph.

Overall: This section is terribly thin.  At minimum, you can beef it up by explaining why each thing is a related:

- [ ]  - First sentence is fine as is.

- [ ]  - How does the formal rewrite semantics relate to your work?  In particular, to your big-step semantics?  Why do you use big step when they use a calculus?

- [ ]  - What does Maranget's formalism have to do with your work?

- [ ]  - Do Erwig and PJ cover every extension you describe?  If not, where are others discussed?

- [ ]  - How does Augustsson's algorithm relate to yours?  Scott and Ramsey's?


- [ ] line 1546: **You've done a ton of implementation work, and to this point it is not really mentioned explicitly.  That is selling yourself short.**  You don't need to say a lot, but do add a section enumerating what you've implemented and what experiments you've been able to do with the implementation.


Section 7
---------
- [ ] Unless I missed it, there is a ton of future work that is much less speculative than what I see here.  In particular, all the semantics work that would be needed to support an ICFP submission:

  - V- is deterministic.
  
  - Your semantics of V- is consistent with the published semantics of VC.

  - I feel like there must be other semantic things we have talked about, but at this moment I can't recall them.
  
- [ ] Section 7.0.1: This isn't about types, it's about exhaustiveness analysis.  It's an important problem, definitely worth mentioning, and there are some recent GHC papers that are relevant (improving GHC's ability to detect inexhaustive patterns in the presence of fancy types).

- [ ] At the moment I think there's nothing inherently interesting about typing P+ or V-.

- [ ] Section 7.0.2: Right now the alphas are an experiment that has not yet panned out.  Some parametricity might (or might not) warrant a sentence in your implementation section, but section 7.0.2 should be deleted.

- [ ] Section 7.0.3: **I can't find a question or a need here.**  What exactly do you propose to study?  Also, Haskell pattern matching already has weird semantics because of lazy evaluation; maybe or-patterns aren't there because integrating them into a lazy language is gnarly?

- [ ] Section 7.0.3 could safely be deleted.

- [ ] Section 7.0.4 can be summarized as "my work might be useful to someone else."  This section is speculation, not future work.  But the last paragraph has some promise, and you can sharpen it: one future project is to extend V- to include all of VC (I believe all that's missing is choice), and then to adapt your match compiler so that it compiles the parts that can be compiled, falling back to the VC's fully general evaluation mechanism only when necessary.

- [ ] Everything else in Section 7.0.4 should be deleted.


Section 8
---------
- [ ] I'm of the "say what you did" school.  The first two paragraphs fit that school; the third does not.

- [ ] IMO this section could be stronger.  Have you not demonstrated that programming with equations is an acceptable, perhaps even promising, alternative to pattern matching?  I think that's the conclusion you want to support.  And it's probably a good idea to recapitulate some of the evidence.

- [ ] line 1651: There's no evidence you've explored a design space.  And in fact you've explored very few alternatives.

- [ ] line 1652: It's not "compiled to a decision tree" that's important here, it's the conclusion that "compiled to a decision tree" supports.

- [ ] line 1653: "Bridge the gaps" doesn't look falsifiable to me.  Delete it.

- [ ] line 1661: "paved the path" is a vague generality.  Drop the metaphor and identify the exact actors and actions you hope for.  Or just delete the paragraph.


Section 9
---------
- [ ] This one would not be appropriate for me to comment on.

Section 10
----------
- [ ] I haven't checked the references.  I will try to get that done before a draft goes to your full committee.


Page headers: **Should be Burtonpatel, not Burtonpatel et al.**