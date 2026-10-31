# Independent review of v8 Appendices B–C

Reviewed source: `tmp/v8_appendices_B_C.tex`, lines 1–697, read continuously in full. The references to the Miller carrier presentation and the formal numerical-type convention were checked against `tmp/v8_sections1_4.tex` and `tmp/v8_sections5_8.tex`. No draft was edited. This report concerns mathematical levels, constructions, domains, and exposition; it does not certify all results in the paper.

Two presentation corrections are required: the first-order initiality statement must name the category of algebras, and Appendix C should consistently use concrete numerical carriers. Both have been communicated to the integrating author and accepted for correction. The finite-proof initiality argument and the counterexample retain their mathematical content. No fatal or major mathematical defect was confirmed in this read.

## (A) Kill-shots / hard blockers

None confirmed. In particular, the proof-object argument does not require the arbitrary target algebra carrier to consist of proof trees, and the counterexample does not use an oracle to compute its total parameter map.

## (B) Major weaknesses

None confirmed. The existence arguments needed in these particular effective categories are present: valid derivation carriers are semidecidable, their conclusion maps are total on those carriers, and evaluation into an arbitrary algebra is computable with the required name invariance. The corrections below distinguish the ambient categories and their objects; they do not call for a new existence theorem.

## (C) Minor issues and concrete repairs

### C1. The first-order proposition names the slice rather than its algebra category

**Anchor.** Lines 386–397, Proposition `prop:first-order-proof-initial`:

> “This algebra is initial in $\mathcal D/\mathsf F$.”

**Failure mode:** `ill_typed` / `ambiguous`. **Severity:** minor; local wording repair.

The endofunctor is `H_T:D/F -> D/F`. Its algebra is initial in the category of `H_T`-algebras, whose underlying objects lie in the slice. It is not an initial object of the slice itself. The subsequent proof is a proof of initiality among algebras, so no change to the construction or proof is needed.

**Evidence:** `structural_argument`; the algebra is defined at lines 392–395, and the comparison at lines 421–429 quantifies over arbitrary `H_T`-algebras.

**Replacement:**

```latex
This algebra is initial among $\mathsf H_T$-algebras in
$\mathcal D/\mathsf F$.
```

The integrating author has agreed to apply this correction.

### C2. Appendix C calls its objects formal types while using their set carriers as the objects throughout

**Anchors.** Lines 460–471:

> “The objects of $\mathcal C_K$ are the formal numerical types generated from $\N$ by binary products and tagged coproducts ...”

> “Let $F:\mathcal C_K\to\Pfn$ send each formal numerical type to its chosen coded carrier ...”

Line 558 refers again to “every formal parameter type.”

**Failure mode:** `inconsistent_use`. **Severity:** minor, but a necessary presentation clarification under the paper's explicit level convention.

Section 5 distinguishes the formal generator `omega` from its set carrier `N`. Appendix C instead calls `N` a formal generator, then uses `N`, products, subsets, graph equality, and ordinary partial functions directly. The construction is consistently meaningful as a concrete category of numerical carriers. Declaring that presentation preserves all subsequent formulas and avoids an undeclared identification of a formal type with its carrier.

**Evidence:** `structural_argument`; compare the first paragraph of `tmp/v8_sections5_8.tex`, the displayed functions at lines 473–484 and 532–559 here, and the subsets and partial functions at lines 569–629.

**Recommended replacement for the object definition:**

```latex
The objects of $\mathcal C_K$ are the numerical carriers obtained
from $\N$ by binary Cartesian products and tagged disjoint unions,
with fixed recursive codings.
```

Retain the definition of its arrows as partial functions on these carriers. Replace the functor sentence with:

```latex
Let $F:\mathcal C_K\to\Pfn$ send each numerical carrier to the
same set and each arrow to the same partial function.
```

At line 558, use “every parameter carrier” rather than “every formal parameter type.” This is a concrete presentation clarification, not a change to the counterexample. The integrating author has agreed to apply it.

### C3. Optional precision for evaluation into an arbitrary algebra

**Anchors.** Lines 277–289 refer to an output of `eta_j` as having a “conclusion,” and lines 421–424 say:

> “For any $\mathsf H_T$-algebra, evaluate a tree from its leaves to its root using its algebra operations.”

**Status:** no mathematical error confirmed. In B.3 the output belongs to the arbitrary carrier `Q_j`, and the text explicitly says that its formula label is obtained **under `q_j`**. It does not identify that output with a derivation tree. The values are only required to lie in the appropriate fibers of `q_j`.

For the user's strict distinction between carriers and derivations, the first-order proof can name those maps in one sentence, without repeating the preceding tree-induction proof:

```latex
For an algebra $\eta:\mathsf H_T(Q,q)\to(Q,q)$, evaluation by
$\eta$ defines $u:\mathsf{Der}_T\to Q$ with $qu=d_T$.
```

The existing induction and exact-domain paragraph can then follow. In B.3, “the result has conclusion `lambda_j(xi)`” can be made purely formal by “the result lies in `q_j^{-1}(lambda_j(xi))`”; this is optional because the existing text already specifies the map `q_j`. No extra assumption on `Q` is required, and no claim that `Q` consists of trees should be introduced.

### C4. Optional economy: omit the ordinary halting-set proof

**Anchor.** Lines 451–454 prove the nonrecursiveness of the usual diagonal halting set.

This is an elementary background argument and can be reduced to “The set $K$ is not recursive.” In contrast, retain the reduction at lines 600–607: it proves nonrecursiveness of the particular set `A` used in this counterexample and is part of the construction. Likewise retain the explanation at lines 547–554 that oracle-program specialization is an ordinary recursive code operation. That distinction is essential here.

## (D) Confirmed comparisons, domains, and construction checks

### Syntax and propositional proofs

1. **Lines 15–32:** `S_j` consists of numerical codes of finite syntax trees; `S` is the functor formed from those carriers and relabeling maps. The constructors are explicitly natural transformations. The text does not silently identify the functor with one component set.
2. **Lines 44–68:** the target `Z` of a syntax-algebra morphism is arbitrary. Evaluation calls the given component operations `alpha_j`, which are total on their specified carriers. Finite induction gives termination and membership in `Z_j`; a separate naturality induction assembles the component maps. Decidability of the target carrier is not assumed.
3. **Lines 90–130:** proof codes retain leaf tags and formula parameters. Modus-ponens matching is a recursive test, and the finitely many nonlogical leaf-membership tests are semidecidable. The induced relabeling maps preserve both membership and premise matching. The conclusion maps form a natural transformation by an explicit equation.
4. **Lines 148–185:** the image subfunctor and its partial identity are distinguished. Leastness is proved by finite induction. Consistency uses componentwise Boolean valuations only to exclude opposite conclusions; it does not claim the valuations form a natural transformation. The conclusion `t_0 nu^*t_0=0` follows from componentwise disjointness, as stated.

### The initial algebra over the formula object

5. **Lines 194–224:** the axiom-instance object contains tagged parameter data, not merely formulas. The pullback defining `M(Q,q)` matches **the formula labels** of two elements of the arbitrary carrier `Q`; it does not require those elements to be proofs. The displayed pullback is correctly typed, and `kappa_q=pi_2 w_q` has target `S`.
6. **Lines 226–240:** the action on a slice morphism is specified by both pullback projections. The equation for `w` proves preservation of formula labels. Pullback uniqueness proves the functor laws.
7. **Lines 242–255:** actual tree constructors provide the algebra on `(Prf,c)`. The injectivity of the implication constructor ensures that the two children determine the consequent, so the extra matching data in `M(Prf,c)` does not introduce an alternative derivation-tree constructor.
8. **Lines 257–301:** for arbitrary `eta`, evaluation maps proof trees to elements of `Q_j`. The equalities under `q_j` put the pair of evaluated children in the pullback. Each operation is computable and total on the relevant carrier; finite induction proves the recursive evaluation map is total on `Prf_j`. Naturality and uniqueness are separately addressed. Thus the arbitrary-algebra and derivation-tree levels remain distinct.
9. **Lines 304–306:** distinct derivations with a common conclusion remain distinct in the proof carrier; only the range forgets which proof was chosen. This states an actual distinction and should be retained.

### First-order derivations

10. **Lines 312–349:** the all-formula carrier `F` and its sentence subobject `S` are distinguished before the rules are defined. Generalization is unrestricted because all nonlogical assumptions are sentences. Logical axiom instances with free variables are permitted. The resulting calculus has no open nonlogical hypotheses whose free variables could obstruct generalization.
11. **Lines 351–384:** finite limits and coproducts are taken in the explicitly selected concrete presentations. In the Miller case, the referenced carrier presentation declares that the total arrows have exact source restriction idempotent. Equality tests, finite conjunctions of semidecision tests, and tagged unions preserve the shared-name domain property. Thus the stated constructions exist in the specified category.
12. **Lines 386–419:** the derivation carrier contains all finite rule trees, with formula conclusions. Sentence proofs are defined afterward by a pullback. Intermediate formulas may have free variables; the passage to sentence conclusions does not remove them from a derivation.
13. **Lines 421–429:** the Miller-case evaluation first waits for membership in the valid-tree carrier. It therefore cannot halt on an invalid tree under some names. On a valid tree, every name passes the test and all algebra operations are total on their indicated carriers; their output values are independent of the name. Consequently the evaluation map has exactly the required domain and value. This is a genuine construction obligation and should survive any shortening of elementary exposition.
14. **Lines 431–434:** closedness is recursively decidable; intersecting with it preserves the relevant semidecidability. The range of the sentence-conclusion map gives precisely the theorem restriction idempotent. The claim relies on the range structure already proved for the surrounding categories and does not assume all subsets are represented.

### Counterexample to automatic lifting

15. **Lines 462–484:** the domain and ordinary extension are distinct data. In the displayed enumeration `f_{e,a}`, the actual domain is explicitly `W_a^K intersect dom(phi_e)`, so undefined ordinary computations are handled correctly. Every arrow of the stated class has such a representation.
16. **Lines 500–530:** composition uses the exact domain `D_f intersect f_0^{-1}(D_g)`. This is `K`-c.e. by dovetailing. Restrictions and ranges have ordinary identity extensions. The range agreement law compares both values and domains on the actual image. Finite joins of restriction idempotents are unions of `K`-c.e. domains.
17. **Lines 532–559:** `tau_K` has a `K`-c.e. domain and an ordinary partial recursive extension. Both specialization functions `e(z)` and `a(z)` are ordinary total recursive functions of code data; the latter inserts a parameter into an oracle program without consulting the oracle. Their paired parameter map is therefore a total source arrow. Exact domains and values establish universality. No unproved closure under arbitrary `K`-recursive total maps is used.
18. **Lines 561–567:** under the concrete-carrier presentation, `F` is faithful and preserves the displayed operations. Its target `Pfn` supplies splitting, connected probes, weak choice, and inverse-image preservation; these are target properties and are not being attributed to `C_K`.
19. **Lines 569–598:** the displayed diagonal pair is computed using the actual oracle-restricted evaluator domain. The proposed separator `A` omits the oracle-domain condition, but this is legitimate: one member of the diagonal pair is contained in `A`, and the other in its complement. Membership in `A` is decidable relative to `K`, so both separator idempotents exist in the source.
20. **Lines 600–622:** the explicit reduction from `K` proves this particular `A` is not recursive. The codiagonal restricted to `A^c+A` is a partial injection with full image. Its section must be total and must select the displayed tag. Any source preimage of that section would therefore be an ordinary total recursive function, contradicting nonrecursiveness of `A`. This verifies failure of the required lift, rather than merely failure of a guessed section.
21. **Lines 624–629:** the two source arrows have disjoint domains and ordinary recursive extensions. Any upper bound is forced on all inputs because the two domains cover the carrier; it must equal the nonrecursive switch. This proves absence of a common upper bound while leaving finite joins of restriction idempotents intact.

The two failures in C1 and C2 are the only confirmed categorical-level errors in this fragment. The uses of finite trees, coordinates, and numerical membership in the explicitly concrete constructions do not constitute further errors.

## (E) Required endpoints

1. Change the first-order proposition to initiality **among `H_T`-algebras** in the slice. Failure leaves the ambient category misstated.
2. Declare Appendix C's concrete carrier presentation and remove the two remaining references to formal types there. Failure leaves a conflict with the paper's formal-type convention.
3. Preserve the exact-domain argument for Miller-case evaluation and the ordinary-recursive specialization argument in the counterexample. These are mathematically substantive, even when elementary background proofs are shortened.

The integrating author has agreed to the first two corrections. This report records the fragment as read; it does not claim to have verified their later application.

## (F) Unchecked matters and bounded conclusion

The bibliography at lines 632–695 was read for internal naming and local references. Its full bibliographic metadata, web links, current preprint versions, and claims in external papers were not independently reverified in this task. The two supplied Montagna papers were independently examined in the preceding arithmetization task, recorded in `tmp/v8_arithmetization_source.md`.

The whole fragment was read, and the relevant carrier-presentation definitions were checked. After the responsible agent reported readiness, the final shortened arithmetization in `tmp/v8_sections5_8.tex`, lines 1–172, was independently read, together with the model interpretation through line 225. No further repair was identified in that bounded read:

- `G(e,x,y)` with an internal index variable is distinguished from `G_e(x,y)` with a fixed standard numeral.
- The trace predicate, output function, index compilers, fixed evaluator index, and PA-total parameter index have explicit types.
- The pairing matches the product coding. A typed `X`-input is represented by its `gamma_X`-code, so `r=[k_e]_T:X -> omega` computes the required specialization on that code.
- The displayed PA graph identity with the intermediate program code `p` supplies the categorical factorization; totality is established before that factorization is called a Turing universal property.
- The model interpretation decodes intermediate arithmetic codes through `gamma_Y^M`, and allows quantified traces to range over the entire model.
- The Montagna p.108, p.115 Note 1, p.109 (*) and DPM p.644 citations match the independently checked primary passages. The lengthy elementary trace proof has appropriately been removed from the manuscript and retained only in the external source note.

The remaining Sections 6–8 were not independently reread in full in this task. No compilation or rendering check was performed, and no manuscript edits were made.

Strongest confirmed issue: the initiality statement names the slice instead of the algebra category. Strongest suspected but unconfirmed blocker: none identified. Most important matter outside this review: correctness of the completed combined manuscript and consistency of its final cross-references after integration. The local findings do not depend on missing source material. Final whole-paper recommendation: unknown; the bounded conclusion is that these two presentation corrections are needed and no fatal or major mathematical defect was confirmed in Appendices B–C.
