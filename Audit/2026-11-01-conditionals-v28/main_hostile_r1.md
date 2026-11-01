# (A) Kill-shots / hard blockers

No false theorem or mathematical blocker was established in the inspected version-28 main-paper changes. This author-side review concerns the removal of the local-connectedness criterion and the direct complementary-conditional arguments that replace its applications. It does not certify the whole manuscript.

The new `cor:source-conditionals` has the required mathematical content. Its source conditional is a total morphism `ell_c:U -> U+U`; composing with the summand restriction idempotents gives the stated inverse images. Range agreement is applied after `[c,c']:U+U ⇀ U`, whose range is the identity. The range functor preserves the resulting equations under the explicitly typed coproduct comparison. Corollary `cor:separator` then rules out a complementary separator. No local-connectedness, splitness or weak-choice assertion is used in this inference.

# (B) Major weaknesses

None confirmed in the inspected changes. No new counterexample or unproved initiality-preservation claim is introduced.

# (C) Minor issues

## C1. State the category of the Miller separator explicitly

- **Anchor:** §8.1, `sections/04-miller-sequences.tex`, initial version-28 lines162–168: “If $c,c'$ are complementary restriction idempotents on a numerical object $X$ … Each domain is independent of the representation”.
- **Claim as written:** the two domain computations can be run uniformly over every representation of the Miller sequence.
- **Failure mode:** `ambiguous` ambient morphism class.
- **Evidence:** `structural_argument` and `absence_in_text`. The preceding paragraph defines `K_p` and `Rec^p`. Uniformity over all representations is supplied by membership in `E_a`, not by being an arbitrary idempotent in either of those later-mentioned categories.
- **Impact:** the displayed conditional belongs to the source `E_a` only when its defining restrictions have that source type. The branch proof itself is valid with this type.
- **Severity and repairability:** minor, locally repairable. Declare `c,c':X ⇀ X` as complementary restriction idempotents **in `E_a`** before the domain searches.

## C2. Include range preservation in the counterexample proposition's claim

- **Anchor:** Appendix C, `appendices/c-section-lifting.tex`, initial version-28 lines47–51, proposition `prop:missing-lift`: “The functor $F$ is faithful, preserves restriction products and reflects zero morphisms”.
- **Claim as written:** the proposition lists faithfulness, products, zero reflection and the nonzero/join conditions.
- **Failure mode:** `inconsistent_use` between the full advertised counterexample and the narrower list in its proposition statement.
- **Evidence:** `structural_argument`. The appendix opening advertises a faithful **range functor**, and `cor:separator` requires a range functor. The unchanged proof at lines122–124 already verifies restrictions, ranges, zeros and coproduct preservation. This is a statement-completeness issue, not an absent proof or a false assertion.
- **Impact:** the full comparison interface should be visible in the proposition's claim rather than recovered only from its proof.
- **Severity and repairability:** minor. State that `F:C_K -> Pfn` is a faithful range functor, with the additional product and zero-reflection properties already listed.

# (D) Cross-section consistency failures

The following interfaces were checked against the actual source.

| Interface | Types and law checked | Result |
| --- | --- | --- |
| New complementary-conditional corollary | `F:R -> A`, total `ell_c:U -> U+U`, `s_c=chi^{-1}F(ell_c):FU -> FU+FU`; swapped summand inverse images; containment of `F(a_i)` inherited from a hypothetical separator | No mathematical failure found. |
| Model interpretation | `F_M:S_T -> Pfn`; Lemma `lem:switch` supplies one total source conditional; preimages of unions and nonempty `M` supply the remaining hypotheses | Correct direct application. |
| Numerical interpretation | `J_rec:Rec -> Pfn`; the displayed recursive branch map has the two required restrictions; target total inverse images preserve unions and `J_rec(1_omega)` is nonzero | Correct direct application. |
| Miller interpretation | `I_p J_p:E_a -> K_p`; one program runs the complementary domain computations; exactly one branch succeeds for every representation, so domain and value are representation-independent | Correct after C1's explicit source declaration. The compactness/unanimity proof for the Turing morphism remains. |
| Failure of Turing-morphism preservation | Under the temporary assumption that `J_p(tau_a)` is Turing in `Rec^p`, use `I_p:Rec^p -> K_p` and total `p`-recursive conditionals; the existing `p`-decidable separator contradicts the new corollary | Correct replacement of the removed criterion. |
| Cosheaf conditional | Domain inclusions `m:C -> V`, `m':C' -> V`; `q=[m,m']:C+C' -> V`; computable inverse components and the typed naturality equation `r_i^{C+C'} q_0^{-1}=q_i^{-1} r_i^V` | The inverse is a morphism of `E`. The copairing `[i_1m,i_0m']q^{-1}:V -> V+V` is total and belongs to `R_X` by fullness. |
| Cosheaf target and endpoints | `I:R_X -> A` and `U|K_2:K_2 -> Pfn`; nonzero identities and target total inverse-image union laws remain explicit | Correct direct applications. The local-connectedness proposition is retained as a separate categorical property. |
| Faithful model family | `F_T:S_T -> D_T`, with coordinatewise interpretation of the one source conditional, coordinatewise join law and nonzero identity | Correct direct application; the theory-extension argument remains unchanged. |
| Lifting counterexample | `F:C_K -> Pfn`; separator `P=F(1_A)`, `N=F(1_Ac)`; its total conditional is not recursive, hence has no source preimage | Correct comparison counterexample; no local-connectedness theorem is required for its conclusion. |

The retained sufficient condition using joins of disjoint-domain morphisms proves existence of the source conditional. It does not assume that the range functor preserves joins of partial morphisms. That distinction is preserved.

A source search found no surviving reference to `thm:local-lifting`, `prop:local-switch` or `lem:connected-alternative` in the main manuscript. The new abstract and introductory references no longer make locally connected targets a premise of the applications. The long categorical syntax, substitution, derivation, soundness and proof-code arguments are outside the edited blocks.

# (E) Acceptance conditions, non-negotiable

1. State the Miller source morphism class as in C1. Failure leaves the representation-uniformity step ambiguous.
2. State that the Appendix C comparison is a range functor as in C2. The proof already provides the endpoint.
3. Preserve the nonzero and total inverse-image join hypotheses in every direct application, and retain the actual source conditional constructions. Omitting one would require re-review of that application.
4. Compile the exact revised manuscript and check the changed references and rendered pages. This reviewer has not performed those separate build/layout checks.

These are local acceptance conditions. The review does not recommend any additional compression, relocation or application removal.

# (F) Not checked / uncertainty log

The review read the changed source and its surrounding type/definition interfaces in §3, the model interpretation, numerical application, Miller application, cosheaf application and Appendices C–D. It compared the diff with the version-27 baseline. It did not re-prove the full numerical or syntactic initiality constructions, recertify literature claims, run Lean, compile the new version or inspect its renderings. The separate note was not yet available at this review stage.

**Strongest confirmed blocker:** none mathematical; C1–C2 are minor explicit-interface repairs.

**Strongest suspected unconfirmed blocker:** none advanced as a finding.

**Most important thing not checked:** compilation/rendering of the exact final manuscript and the forthcoming separate note.

**Dependence on unavailable material:** none for the main-paper conclusions; this report makes no conclusion about the unfinished note.

**Final recommendation:** unknown for a whole-paper decision. No mathematical objection to the scoped changes, subject to the two minor repairs and the separate build checks.
