# (A) Kill-shots / hard blockers

This is an author-side audit of the complete source of *Inseparable domains
and computational extensions*, dated 29 October 2026, using the invoked
HostileRefereeGPT — Cat/Rec skill. It is not an independent or human referee
report. The reviewed axes are mathematical correctness, categorical typing,
hypothesis use, and the relation to the stated recursion-category problem.

No fatal defect is confirmed in the revised manuscript. The signed-literal
result is explicitly restricted to selected domain extensions. It is not
stated as a construction of a classical deductive presentation from an
arbitrary recursion category.

# (B) Major weaknesses

No major mathematical defect is confirmed. The following is the complete
claim audit, with the hypotheses used and the argument checked.

| Anchor | Claim and explicit data | Check and status |
| --- | --- | --- |
| §1, Proposition 1.1 | A total pair reduction transports inseparability when total inverse image preserves binary domain joins. | Pullback preserves zero, top, and meets by restriction identities and totality; join preservation is separately assumed. A target complementary separator pulls back to a source one. Checked. |
| §2, Lemma 2.1 | Restriction domains on a binary restriction coproduct are exactly pairs of restriction domains. | For each domain `e`, the identity `e i_j = i_j bar(e i_j)` determines both coproduct components. Conversely the restriction of `a+b` has components `i_0 a`, `i_1 b`; hence `a+b` is a restriction idempotent. Composition is coordinatewise, so this is an order isomorphism, including its stated preservation of existing meets and joins. Checked. |
| §2, Theorem 2.2 | `Σ:Pair(R)→Inv(R)` is left adjoint to `J`. | The source objects are ordered disjoint domain pairs, not arbitrary predicates. The target objects are consistent total-involution presentations. The arrow actions `f↦f+f` and `h↦h` preserve their inequalities and equivariance. The mutually inverse hom-set assignments are `h↦h i_0` and `f↦[f,ν f]`. The second assignment is equivariant because `ν²=1`, and its domain inequality is exactly the two pair inequalities. Naturality holds for arbitrary pair reductions and arbitrary equivariant target arrows, without invertibility. Unit and counit are correctly typed. No join or range premise is used. Checked. |
| §2, Theorem 2.3 | Inseparability is equivalent to essential incompleteness of the signed presentation. | Write an arbitrary selected extension as `c+d`. Extension, consistency, and completeness become respectively coordinate containment, `cd=0`, and `c∨d=1`. This proves both implications and the claimed isomorphism of extension posets. The base extension is consistent because `ab=0`. Only the indicated joins in `D(X)` are needed; the coproduct order isomorphism supplies those on `X+X`. Checked. |
| §3, functor `P` and Corollary 3.1 | One fixed atom arrow makes every consistent classical-extension theorem/refutation pair inseparable. | Monotonicity gives both reduction inequalities for every `t≥t₀`. The natural transformation has the same component `θ` at all extensions. Proposition 1.1 then proves inseparability, which is stronger than the contradiction with completeness alone. No new interpretation family or soundness assumption is introduced. Checked. |
| §3, one-node diagram and relative form | Existing proof constructors give the fixed lower bounds; an unsplit assertion domain uses a relative top. | The two composites have types `A→S` and `B→S`; composing with `t₀` fixes them. Their restrictions pulled back to the splitting objects are identities, equivalently `a≤θ*t₀` and `b≤θ*ν*t₀`. The source references and the original partial negation conditions were checked against the committed manuscript sources. Checked. |
| §4, Proposition 4.1 | A zero- and domain-join-preserving restriction functor reflects inseparability of a specified source pair; bijectivity on the endomorphism hom-set also yields preservation. | Reflection is direct preservation of the four separator equations. For preservation, fullness on this hom-set lifts a target separator as arrows; taking restrictions lifts it as domains. Injectivity reflects the complement and containment equations. Source disjointness is explicitly assumed; it is not inferred from its image. Checked. |
| §4, Proposition 4.2 | A recursion-category functor can preserve the chosen evaluator, products, coproducts, ranges, and finite-run iteration while destroying a specified inseparable pair. | The diagonal-object full subcategory of `C×C` has componentwise partial arrows and structures. A pair of total numerical program-parameter maps proves universality of `(τ,τ)`. Projection to the second factor sends the disjoint inseparable pair `(a,p),(b,q)` to the nonzero complementary even/odd pair `p,q`. First components of any source separator would separate `a,b`. Checked. |

For the last claim, Heller's printed pp.1261 and 1265 were inspected directly
in the supplied scan. His 1990 definition is a prodominical isotype with a
Turing morphism. The product example satisfies that definition. It fails
the stronger dominical condition because nonzero `(1,0)` and `(0,1)` have
zero restriction product. The revised source states this limitation.
Thus the example is not being silently asserted in the narrower dominical
class.

# (C) Minor issues

The following defects were exhibited in the first draft and repaired in
the revised source. None invalidated a central proof.

1. **Wrong numerical cross-references.** Anchor: §3, the one-node proof
   paragraph and the unsplit-assertion paragraph. The draft cited
   “Corollary 7.3” in the general supplement and “Theorem 7.1” in the
   23-page note. Failure mode: `inconsistent_use`; evidence: `citation`.
   Counting the theorem environments in the committed sources locates
   `gen:essential` at Corollary 6.3 and `ct:certificate-transfer` at
   Theorem 6.1. Downstream impact: the original citations did not locate
   the claimed construction. Severity: minor. Repairability: local;
   both citations were corrected.

2. **Untyped partial negation in the relative paragraph.** Anchor: §3,
   “For an unsplit assertion domain…”. The draft introduced `V` but used
   `ν*t` without redeclaring the partial endomorphism or its restriction.
   Failure modes: `missing_definition`, `ambiguous`; evidence:
   `absence_in_text`. The relative construction requires
   `ν:V→V`, `bar(ν)=s`, and `sν=ν`, not a total endomorphism on all of
   `V`. Downstream impact: this paragraph's type and top-preservation
   argument were not explicit. Severity: minor. Repairability: local;
   the revised source supplies these data and the partial inverse-image
   formula.

3. **Omitted target of the domain functor.** Anchor: §1, following the
   inverse-image identities. The draft described a “contravariant
   functor on `Tot(R)`” without naming its target. Failure mode:
   `missing_definition`; evidence: `absence_in_text`. Downstream impact:
   the categorical signature was incomplete, though the object and arrow
   operations were supplied. Severity: minor. Repairability: local;
   the revised source gives `D:Tot(R)^op→Pos` and defines `Pos`.

The revised source also defines `f+g` for arbitrary typed arrows before
using `Σ(f)=f+f`. No further repair is requested by this audit.

# (D) Cross-section consistency failures

No unresolved variance, typing, or framework drift is confirmed.

- Domain inverse image is contravariant in a total arrow; the extension
  functor and both functors in the adjunction are covariant. The domain
  map induced by a restriction functor is covariant. These are separate
  constructions with their directions stated.
- The walking-arrow test succeeds for a strict extension `t<t'`:
  `P(t→t')` has underlying map `1_S`, but it is an arrow between two
  different objects of `Pair(R)`. Its reverse need not exist. Naturality
  of the constant component `θ` uses no inverse to this arrow.
- The signed presentation uses a total involution. The classical syntax
  application explicitly does not require involutivity of its negation
  constructor. The latter application uses `Pair(R)` directly rather
  than incorrectly treating classical syntax as an object of `Inv(R)`.
- General separator transport assumes stable binary joins under total
  inverse image. The concrete signed-presentation equivalence uses the
  coproduct order isomorphism instead. No general stability theorem is
  inferred from the latter.
- The projection example concerns the image of a specified pair. Its
  target still has other inseparable pairs. Reflection likewise requires
  specified source preimages; it does not lift an arbitrary target pair.
- The signed-literal theorem constructs no implication or Hilbert closure.
  The manuscript retains the earlier consistency and construction
  hypotheses for its classical application. It does not claim that the
  Di Paola–Heller construction problem has thereby been solved in full.

# (E) Acceptance conditions, non-negotiable

1. **Precise selected-extension statement.** Deliverable: Theorem 2.3 and
   the following scope paragraph. Endpoint: its extensions remain
   restriction domains on the stated signed syntax object, and classical
   closure is not claimed. Status: met. Failure would require dropping the
   classical-construction inference, if made.
2. **Correct reflection and preservation hypotheses.** Deliverable:
   Proposition 4.1. Endpoint: source disjointness, zero/join preservation,
   and the extra lifting-and-reflection hypothesis for preservation remain
   explicit. Status: met. Omitting them would require rejection of the
   corresponding unrestricted assertion.
3. **Correct recursion-category class in the counterexample.** Deliverable:
   Proposition 4.2 and its subsequent qualification. Endpoint: use
   Heller's 1990 definition and retain the failure of dominicality.
   Status: met. Without that qualification, any claim covering the narrower
   dominical class through this example must be withdrawn.
4. **Close the local reference and definition defects.** Deliverable: the
   revised §1 and §3 source. Endpoint: the items in (C) are repaired with
   the correct cited numbers and typed partial inverse image. Status: met.
   Failure would require local revision, not rejection of the main proofs.

# (F) Not checked / uncertainty log

- The complete new mathematical source was read and its displayed proofs
  checked. The relevant earlier atom constructors, one-node equations,
  and cited theorem locations were read in their committed sources.
- The previous finite-stage proof construction, consistency arguments,
  and full three-point cosheaf example were not re-audited here. Their
  existing verification is reused; this audit checks the new interface
  and conclusions, not every proof in those documents.
- The numerical existence of an inseparable pair and a universal partial
  recursive evaluator is used as established background from the earlier
  construction. It was not reproved here from a machine model.
- Heller's definition and the dominical obstruction were checked against
  the scan, not solely OCR. No additional result from Heller's printed
  proofs, including Proposition 6.2, was imported.
- No novelty or priority claim is certified. The note claims an explicit
  construction and implications, not first discovery. No Lean
  formalization or older axiom count was used as evidence for these proofs.
- Final compilation and rendered-page inspection belong to the separate
  verification record. This report does not claim to perform those checks.

Strongest confirmed blocker: none in the revised claims.
Strongest suspected unconfirmed blocker: none identified by this audit.
Most important item not checked: the complete earlier construction and
consistency proofs on which the classical application remains conditional.
Dependence on unavailable material: none for the elementary new proofs;
publication-level originality and the full dependent development were not
assessed.
Final recommendation: **unknown** as a publication recommendation; no
confirmed mathematical blocker remains for the statements audited here.
