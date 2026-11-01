# (A) Kill-shots / hard blockers

No false theorem or counterexample is established. **The current subsection does not pass the requested explicit-type and proof-exposition gate.** Its mathematical method is plausible and the principal existence arguments can be reconstructed, but several categorical constructions and universal properties are left as unnamed or untyped assertions. The repairs below concern the displayed mathematical data and their connections; they do not require changing Appendix A.

Reviewed: version 25 of *Logical consequence and essential incompleteness in recursion categories*, §7.4, “The numerical realization,” including Proposition 7.7 and its numerical application. The frozen source is `tmp/numerical26/round1/08-essential-incompleteness-of-arithmetic.tex`, lines 285–488. PDF/printed pages 36–38 supply the page anchors. All source-line anchors below refer to that frozen file. This is an author-side audit, not a whole-paper publication review or a Lean verification.

# (B) Major weaknesses

## H1. The categorical equivalences lack the promised typed comparison data

**Anchor:** Proposition 7.7, p.36, lines 338–358, and its proof pp.36–37, lines 360–391: “The recursive numerical codings identify these carriers … and give the stated equivalence” and “These assignments respect composition by pullback and give the restriction equivalence.”

**Claim as written:** `Tot(Split(Rec)) ≃ C_rec` and `Par(C_rec,Mono) ≃ Split(Rec)`.

**Failure mode:** missing_definition / ambiguous categorical comparison. **Evidence:** absence in the displayed construction, with a structural reason the omitted data matter.

The first equivalence is not named and has no object or morphism action. A split carrier is a subset of `|X|`, where `X` is a formal numerical type; it is not literally an object of `C_rec`, whose objects are subsets of finite powers of N. For example, a coproduct carrier consists of tagged elements, and a nested product carrier contains nested tuples. The recursive coding maps from §5 provide a repair, but the proof must choose and use them rather than silently identify their sources with numerical subsets. Conversely, a carrier in `N^m`, including the singleton `N^0`, requires a chosen tuple encoding before it defines an idempotent on ω. Merely naming recursive codings does not specify these two functors or their comparison isomorphisms under the user's requirement that every type be explicit.

The span-to-partial-map assignment in the second comparison is described, but its source and target functors, its relationship to the first comparison, and its object action have not been specified. The text also uses the same letter `m` first for `m:C→D` and then for the left leg `m:B→C` of a span; these are locally scoped examples, but the second occurrence should be freshly typed when the functor is defined.

**Repair:** name the total comparison, give its carrier and arrow actions through the fixed numerical codings, give a quasi-inverse on c.e. finite-power carriers and its arrows, and state the inverse comparison maps. Specify the restriction comparison on objects and on monic spans, with the inverse given by the domain inclusion and total restriction. Verify identities, composition, and restriction using these formulas. A succinct proof is sufficient; no new general categorical theorem is needed.

**Downstream impact:** the sentence, derivation, and range objects later used in the splitting depend on this comparison. Without explicit transport data the numerical realization is insufficiently specified for the intended formalization. **Severity:** major exposition/type omission, repairable; no counterexample to the existence of the equivalences is claimed.

## H2. The initiality arguments omit the algebra structures, fold equations, and relevant slice types

**Anchor:** Proposition 7.7, p.37, lines 393–427: “an algebra for the functor `K_P` … on `x:X→P` and `y:Y→P`”; “The resulting morphisms … satisfy the algebra equations”; and “This defines an algebra morphism.”

**Claim as written:** parameter-stable initial syntax and list algebras and an initial inference algebra for every axiom subobject.

**Failure mode:** missing_definition / compressed universal-property argument. **Evidence:** displayed arrows and equations required by the claim are absent at the cited anchors; the constructive evaluation argument itself identifies a repair.

The argument correctly says that algebra operations are defined on their specified carriers and that evaluation terminates on valid syntax. It does not assume an ambient total recursive extension. However, the arbitrary algebra's structure maps are not declared, the source constructor algebra is not written, the two folds are not named or declared as arrows over P, and their algebra-morphism equation is referred to without being stated. The list claim is then relegated to “in the same way” without its nil/cons structure or fold type. The derivation argument has no displayed conclusion map for the full derivation object, no named initial structure arrow, no type for the arbitrary target algebra, and no named slice fold or algebra equation. These omissions leave exactly the universal-property data the user has asked to make explicit.

**Repair:**

- For the syntax proof, declare the arbitrary pair of slice carriers and both `K_P` structure maps, the parameterized constructor pair, and folds `h_T:P×Tm→X`, `h_F:P×Fm→Y` satisfying the projection equations and the pair algebra equation in `(C_rec/P)^2`. Explain that the finite evaluation records use the chosen partial-recursive programs for those operations, terminate on valid inputs by induction, and determine a computable function on the specified source. State uniqueness through the same constructor equations.
- For lists, declare an arbitrary nil arrow and cons arrow over P, the fold `P×List(V)→X`, and its two recursion equations, with induction on length proving termination and uniqueness.
- For derivations, declare `H_A:C_rec/Fm→C_rec/Fm`, the full conclusion map `c_all:P_all→Fm`, the node-constructor structure arrow, an arbitrary target algebra on `(Q,q)`, and a fold `f:(P_all,c_all)→(Q,q)` with `qf=c_all` and `f δ=α H_A(f)`. The current leaves-to-root induction proves the required carrier/conclusion invariant and uniqueness once these data are written.

The recursive signature hypothesis should be instantiated by its objects `Σ_k,Π_k` and their arity range in `C_rec`. The syntax and derivation codes and algorithms already developed in §5 can be reused as numerical constructions; their universal properties here must be proved directly for the arbitrary computable target operations. A regular interpretation functor does not automatically preserve an initial algebra.

**Downstream impact:** these are the universal properties needed to apply Appendix A, not optional numerical descriptions. **Severity:** major under the explicit-type/exposition requirement, locally repairable; no mathematical impossibility is established.

## H3. The numerical application needs an explicit bridge to the earlier code interpretation

**Anchor:** pp.37–38, lines 430–488, particularly “Thus the partial identities `a,b` on `A,B` remain inseparable”; `θ:N→S`; “Theorem A.6 identifies the pullback … with `c_T`”; and application of Lemma 7.1 to obtain equation (14).

**Claim as written:** the syntax and proof objects supplied by Proposition 7.7 give the numerical sentence theory in `Split(Rec)` and the two reduction inequalities required by Corollary 4.3.

**Failure mode:** ambiguous comparison / missing explicit typing. **Evidence:** structural argument concerning the two distinct ambient categories and code presentations.

The subsection gives a useful convention that a c.e. subset `D⊆N` also denotes `(ω,1_D)` in the splitting. This explains why N can denote the whole numerical split object, but the application should state this instance and the types of `a=1_A` and `b=1_B` explicitly. More substantially, Lemma 7.1 is a statement about the `B_PA` realization and its Set/partial-function interpretation; the application uses newly realized syntax in the numerical splitting. The proof does not state that the numerical syntax and derivation coding is chosen to be the same coding, nor provide a comparison if another coding is used. The existence of an initial algebra gives a unique algebra isomorphism, not literal equality of numerical carrier sets. The inference to the two numerical restriction inequalities therefore needs the code/denotation identification to be stated.

Similarly, the sentence-conclusion map is described as “the set of codes of finite derivation trees … whose conclusions are sentences.” To use the appendix's pullback statement without an identification ambiguity, define it as the actual restriction/pullback of the chosen full derivation conclusion map. Otherwise a proof reader has to supply the coding comparison and the pullback square.

**Repair:** fix the same numerical syntax and derivation coding already used in §5 and §7.1 (or explicitly give the corresponding recursive isomorphisms), name the full proof conclusion and its sentence pullback, and state the map types in `C_rec` and their transported types in the splitting. Explain that the standard interpreted graphs coincide with these numerical graphs, so Lemma 7.1's inclusions are exactly the partial-identity inequalities in the numerical realization. The image/range theorem of Appendix A should then be invoked once for the least theory.

**Downstream impact:** equation (14) and the final application of the categorical incompleteness corollary depend on this interface. **Severity:** major comparison/exposition omission, repairable by explicit choices and a short argument; the current text does not provide evidence of a false inequality.

# (C) Minor issues

## H4. Replace the compressed substitution identification by its precise imported algorithms

**Anchor:** p.37, lines 409–412: “Induction identifies them with the lists of free-variable occurrences and the usual free-for substitution on these named-variable trees.”

**Failure mode:** ambiguous / compressed exposition. **Evidence:** the appendix's formula substitution is a total option-valued morphism with an admissibility subobject, not a globally total formula replacement operation.

The word “usual” does not specify which of the already defined operations is realized. The intended named-variable syntax is clear from Appendix A, but this sentence should name the term substitution, the option-valued formula substitution, and its admissibility pullback. The algorithms and quantified-constructor cases are already given in Proposition 5.7. Cite and reuse those numerical algorithms, explain that their constructor equations hold on the numerical carriers, and use the newly proved numerical initiality to identify them with the appendix's morphisms. Do not duplicate Appendix A's fold proof or silently replace option-valued substitution by an everywhere-successful operation.

**Severity:** minor local exposition issue, but necessary under the user's terminology/type standard. The mathematical claim is repairable without new literature.

# (D) Cross-section consistency failures

The following interfaces were checked and did not yield an independent mathematical defect:

| Data | Typed check or mathematical reason | Status |
| --- | --- | --- |
| `Rec`, the maps `φ_e`, and `J_rec` | `X,Y∈O`; `φ_e:|X|⇀|Y|`; morphism equality is extensional. `J_rec:Rec→Pfn` has its object/arrow action stated and is covariant. Composition and identity follow from the earlier coding identities. | Pass. |
| Turing morphism | The standard interpretation of the PA-provable specialization identity gives total recursive parameter maps in `Rec`. | Pass. |
| Reversed conditional | For complementary c.e. domains C and C′ in a recursive formal-type carrier, both sets are recursive in that carrier. The branch function into the tagged coproduct is total recursive, giving the required source lift. | Pass; the injection types are inherited from the declared restriction-coproduct convention. |
| Regularity | Finite limits are computed on c.e. carriers; images are c.e.; a surjection descends a fiber-constant computable map by dovetailed preimage search. Set pullbacks of surjections stay surjective and remain c.e. computable pullbacks. | Mathematical method valid; explicit comparison data need H1. |
| Monomorphisms | Singleton maps detect noninjectivity. For an injection, dovetailed preimage search is a partial-recursive inverse with domain its c.e. image. | Pass. |
| Syntax folds | Leaves-to-root evaluation uses each operation only on its own carrier. Structural induction gives the required parameter-fiber invariant and termination, and the constructor equations give uniqueness. | Mathematical method valid; missing typed structures/equations are H2. |
| Derivation carrier | For recursive signature coefficients, syntax-side checks are recursive. Finitely many c.e. axiom tests can be dovetailed to semidecide valid finite derivation trees. | Pass. |
| Full versus sentence derivations | The full initial algebra lives over `Fm`; its sentence pullback is not asserted initial for the same inference functor over S. | Intended distinction preserved, but the actual pullback should be displayed under H3. |
| Theory image | Appendix A supplies leastness from initiality; its image/range lemma applies once monomorphism partial inverses and the realization comparison are established. | Correct dependency; do not reprove Appendix A. |

The subsection can retain one purpose as the numerical realization of the categorical incompleteness argument: construction of the numerical category and logical objects discharges the hypotheses of the final categorical application. No additional split is required merely because Proposition 7.7 has several structural conclusions. The issue is the explicit mathematical interface, not the number of paragraphs.

The numerical objects and computations are external constructions used to realize the categorical structure. Such an application need not be written entirely without sets. The repair is to state the category memberships, comparison maps, and changes of interpretation rather than claim that all of §7.4 is internal categorical reasoning.

# (E) Acceptance conditions, non-negotiable

1. **Proposition 7.7 category comparisons:** named, typed functors and their object/arrow actions through the chosen codings, plus inverse comparisons and functor-law justification. Failure blocks acceptance of the numerical realization as explicitly specified.
2. **Proposition 7.7 syntax/list universal properties:** typed target algebra structures, slice folds, equations, termination on their specified carriers, and uniqueness for arbitrary target algebras. Failure leaves the key initiality obligation insufficiently stated.
3. **Proposition 7.7 derivation universal property:** typed full conclusion, constructor structure, arbitrary target algebra, slice fold and algebra equation, with the current evaluation invariant and uniqueness made explicit. Failure leaves the premise of Appendix A's image theorem inadequately specified.
4. **Substitution interface:** name the option-valued map, term map, admissibility subobject, and the specific reused algorithms from §5.7. Failure leaves the requested substitution realization imprecise.
5. **Numerical application:** explicitly compare the chosen syntax/proof codes with §7.1's standard interpretation, define the sentence proof map as a pullback of the full map, and type the restriction inequalities in the splitting. Failure leaves the categorical incompleteness application with an unstated comparison.

These endpoints are concrete repairs. No new mathematical axiom, consistency assumption, ambient total-extension assumption, or general theorem about preservation of initial algebras is justified or required by the audit.

# (F) Not checked / uncertainty log

Read completely: frozen §7.4. Read for dependencies: formal numerical types and coding, arithmetized evaluation/parameterization, restriction-splitting conventions and range functors, the predicate-category realization and its monomorphism/image proof, syntax/list initiality and the detailed substitution algorithms in §5, the general derivation-initiality proof, the standard-code and model interpretations relevant to §7.1, and Appendix A's finite-power, syntax, rule-functor, image, sentence-theory, and range conventions. The PDF text on pp.36–38 was inspected for anchors.

This audit does not re-prove all earlier syntax and soundness results, all later applications, or every bibliography entry. No new factual literature claim is proposed. No Lean elaboration or kernel verification was performed. A full rendered-layout check is left to the parent workflow when revised pages are compiled.

**Strongest confirmed blocker:** the universal-property and comparison data omitted in H1–H3 prevent the requested explicit-type acceptance.

**Strongest suspected unconfirmed blocker:** none promoted to a mathematical finding; no counterexample to Proposition 7.7 is established.

**Most important thing not checked:** the earlier full syntax/soundness developments were used through their stated and inspected interfaces rather than re-audited constructor by constructor.

**Dependence on unavailable material:** none for the identified omissions or repair method.

**Final recommendation:** unknown for a whole-paper publication decision; **local acceptance withheld pending the explicit constructions H1–H4**. The stated mathematical conclusions need not be dropped if those data are supplied as described.
