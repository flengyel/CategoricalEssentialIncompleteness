# (A) Kill-shots / hard blockers

Date: 29 October 2026. This is an author-side audit using the invoked
HostileRefereeGPT — Cat/Rec workflow. The objects reviewed are the complete
`CONSTRUCTION_REVIEW.md` and `SYNTACTIC_SOURCE_CHECK.md` in this directory.
The task is to assess the proposed route from the valid unprimed `S_T`, not
to review a journal submission or establish novelty.

No fatal defect is confirmed. The short argument constructs a forbidden
separator in ordinary computability from a hypothetical complete consistent
c.e. extension of PA. It does not assert that external completeness produces
a restriction-total separator inside `S_T`.

# (B) Major weaknesses

No major defect is confirmed in the classical benchmark. The following
claim audit records the actual mathematical checks.

| Anchor | Data and claim | Derivation and status |
| --- | --- | --- |
| Construction review §1; source check, “What the unprimed sources define” | Arrows of `S_T` use a single proof of universally quantified Kleene equality. | DPM printed p.646 places the input quantifier inside `T⊢` for unprimed `S_T`, and outside it in the distinct primed construction. For the unprimed quotient, uniform graph equivalence substitutes through the existential graph formula for composition. Both congruence laws therefore follow. Checked. |
| Construction review §1, domain order and structure | Domains are Σ₁ partial identities, ordered by uniform T-provable implication, with the stated finite lattice operations. | Conjunction represents composite restrictions. Disjunction is an upper bound and the least one because the two implication proofs combine by propositional case elimination. These are statements in the uniform proof order, not claims about mere external set inclusion. Checked. |
| Construction review §1, quotient functor `Q_{T,T'}` | Theory extension gives a covariant, hom-set-surjective functor preserving the specified computational structures. | An equality proved in `T` remains provable in `T'`; the chosen programs for each structural operation are unchanged. Thus representatives define the object and arrow actions, preserve composition and restrictions, and satisfy the stated extension-composition equations. A target representative is already a source representative, proving hom-set surjectivity. The range compiler represents its Σ₁ image in every theory. Checked. |
| Source check, “For f:X⇀Y, define R_f(y)…” and the following agreement calculation | The image partial identity is the least domain receiving `f` and satisfies the stronger agreement property in the uniform proof order. | The graph of `Df` is `G_f(x,y)∧D(y)`, so `Df=f` is equivalent to the displayed uniform implication. First-order existential elimination converts it to `∀y(R_f(y)→D(y))`. The same input witnesses `R_f` on every output of `f`, proving `R_f f=f` already in PA. For `gf=hf`, an input witness for `R_f(y)` and functionality of `f` turn composite graph equality into `G_g(y,z)↔G_h(y,z)` under that range assumption. Existential elimination therefore proves `gR_f=hR_f` uniformly in T. No global choice of a preimage or external-to-internal inference is used. Checked. |
| Construction review §1, canonical pair | The distinguished diagonal pair remains inseparable in every consistent `S_T`. | For complementary Σ₁ domains, dovetailed search has the two branches whose graph specifications PA verifies; `T` proves totality from their covering statement. The Turing morphism and this case operation give the internal diagonal argument. Nontriviality follows from consistency. The conclusion is re-established for the chosen pair in each target; it is not inferred from a general preservation theorem. Checked. |
| Construction review §3, `E_T` | Proof-instance extraction gives a well-defined covariant map between the two domain posets. | Uniform provable equivalence yields provable equivalence at every numeral, hence equal proof-instance sets. A uniform implication yields inclusion. Proof enumeration gives a c.e. partial identity from each representative. No equality of arbitrary program arrows in `Rec` is inferred. Checked. |
| Construction review §3, preservation properties | `E_T` preserves finite meets and top, and preserves bottom under consistency. | A proof of a conjunction gives proofs of both conjuncts; proofs of both give a proof of the conjunction. The top numeral instances are provable. A numeral instance of bottom has no proof in a consistent theory. Binary joins are correctly excluded in general. Checked. |
| Construction review §3, extension inequality | `E_T(e)≤E_{T'}(Qe)`. | Every provable instance remains provable after theory extension, but additional instances can become provable. Only the inequality is asserted; no unsupported naturality equality is used. Checked. |
| Construction review §3, constants | `n∈E_T(e)` iff `eκ_n=κ_n` in the valid uniform quotient. | The PA-verified graph of `eκ_n` is the constant output `n` conditional on `D(n)`. Uniform equality with the total constant is equivalent in PA to `D(n)`; the reverse implication may be obtained by instantiating the input at `0`. This uses no terminal object or new pointwise arrow quotient. Checked. |
| Construction review §2, canonical ordinary sets `A,B` | The diagonal output-0 and output-1 sets are disjoint c.e. and recursively inseparable. | Functionality gives disjointness; enumeration gives c.e. domains. A recursive separator produces a total program outputting `1` on the separator and `0` off it. At its own index, either membership decision contradicts the appropriate inclusion. Checked. |
| Construction review §2, `I_T,Z_T` and `q_T` | The identity and zero fibers of the effective presentation form disjoint c.e. sets. | The unary hom-set uses the fixed program indices. Proof enumeration makes each fiber c.e. If an index belonged to both, transitivity of graph equality would identify identity and zero, contradicting their PA-provable inequality and consistency. `q_T` is explicitly a map of sets; it is not a functor from extensional computations. Checked. |
| Construction review §2, compiler `r` | `r(A)⊆I_PA` and `r(B)⊆Z_PA`, making the identity/zero pair inseparable. | The compiler graph is `α(n)∧y=x`. A verified output-0 trace supplies a PA proof of uniform identity equality. A verified output-1 trace and deterministic functionality supply a PA proof of `¬α(n)`, hence uniform zero equality. The total primitive recursive compiler pulls any recursive separator back to a separator of `A,B`. Only inclusions, not inverse-image equalities, are used. Checked. |
| Construction review §2, extension and completeness | Quotients enlarge both fibers; completeness would make `I_T` a recursive separator. | The equality `q_{T'}=Qq_T` and preservation of identity and zero give the two fiber inclusions. Consistency keeps the enlarged fibers disjoint. Completeness and c.e. axioms permit parallel proof search for `Eq(e,i)` versus its negation; consistency makes the answers exclusive. This decides `I_T`, which avoids `Z_T`, contrary to inseparability. There is no claim that `I_T∪Z_T` covers all indices. Checked. |
| Construction review §2, functor `I` | The consistent-extension poset maps to `Pair(Rec)` through identity and zero fibers. | Pair objects and their total-recursive reduction arrows are defined. Extension inclusions give the identity reduction on the index carrier, and composition is literal identity composition. The fixed compiler `r` reduces `(ω,A,B)` to each object. Checked. |
| Construction review §4, extracted enlargements | `A⊆E_T(a_T)` and `B⊆E_T(b_T)`, with disjoint right-hand sides under consistency. | Every genuine finite computation gives a PA proof of its numeral instance. If both extracted domains contained a numeral, `T` would prove both output predicates, contradicting their PA-provable uniform disjointness. Equality with the original c.e. sets is not needed or asserted. Checked. |
| Construction review §4, positive and negative proof sets | Under hypothetical completeness, `C_T,N_T` form a complementary c.e. separator. | Proof enumeration makes both sets c.e., including the negative proof set even though `¬α` is not generally Σ₁. Consistency makes them disjoint. Computation verification gives `A⊆C_T`; an actual output-1 computation and provable disjointness give `B⊆N_T`. Completeness for the numeral family `α(n)` makes the union all of ℕ. Parallel proof search therefore computes a separator, contradicting inseparability. Checked. |
| Construction review §4, extension functor `O` | Consistent c.e. extensions map covariantly to `Pair(Rec)`. | Both proof sets increase under theory inclusion. Consequently the underlying total identity is an admissible reduction from the earlier pair to the later one. The same identity reduces `(ω,A,B)` to each pair. Functor identities and composition hold literally. Checked. |
| Construction review §6, true arithmetic | Completeness alone does not complement all domains of `S_T`. | For `T=Th(ℕ)`, a uniform graph equivalence is provable exactly when it is true, so arrow equality is ordinary extensional equality and `S_T` is `Rec` on the fixed objects. Its c.e. domain lattice still contains inseparable pairs. The unavailable step is effective enumeration of all T-proofs. Checked. |

The argument uses the effective presentation of deduction, not merely an
unstructured abstract category. Section 5 explicitly identifies these
additional data, and the report does not claim to have supplied them in
every nonnumerical recursion category.

# (C) Minor issues

**Observation typing in the proposed general data.** Anchor: construction
review §5, item 2, the phrase “computational domains in the original
category.” Failure mode: `ambiguous`. Evidence: `absence_in_text`: the
candidate-data list did not initially name that fixed target category or
separate the variance of positive and negative observations. Severity:
minor. Impact: it could obscure the already-correct distinction between
the domain extraction `E_T` and negative proof enumeration; it does not
affect the argument in §4. Repairability: local.

The precise clarification is to use a fixed computational category
(`Rec` in the benchmark) and separate observation maps. For a domain
represented by `D`, positive observations are proofs of `D(n)` and negative
observations are proofs of `¬D(n)`. Positive observations are monotone in
the domain argument; negative observations are antitone in that argument.
Both increase under theory extension. Negative observations do not require
`¬D` itself to represent a domain of `S_T`.

This issue was reported before any repair. It is an exposition correction
to the candidate data, not a proposed change to the proof. The revised
§5 now names Rec, defines the separate observations, states their variance,
and distinguishes negative proof search from a negated internal domain.
The issue is resolved.

# (D) Cross-section consistency failures

No unresolved mathematical framework drift is confirmed in the reviewed
argument.

- The valid `S_T` quotient has one uniform proof inside its definition.
  Evaluating a domain at individual numeral constants later does not alter
  that quotient or revive `S'_T`.
- `Q` acts covariantly on the categories of programs. `E_T` acts covariantly
  only on the domain posets. The latter is not presented as an all-arrow
  functor `S_T→Rec`, and the separator proof does not require one.
- The fibers `I_T,Z_T` are c.e. domains on the presentation-index object in
  Rec, rather than internally asserted domains of `S_T`. The map `q_T` has
  a hom-set as codomain. Its compatibility with `Q` is a set-map equation,
  not a newly asserted categorical functor or a pointwise quotient.
- The walking-arrow test succeeds for a strict extension `T⊂T'`: quotient
  arrows exist in that direction without an assumed inverse. The observation
  pair inclusions likewise need not be equalities or isomorphisms.
- PA-provable disjointness of two machine-output predicates is distinct
  from internally proving consistency of T's own deduction. Only the former
  internal disjointness is used. External consistency is used to rule out
  simultaneous positive and negative proofs at a standard numeral.
- Completeness makes external proof search terminate. No T-proof of the
  universal termination of that search is inferred. The internal and
  external notions of totality remain distinct.
- An extracted canonical domain may strictly contain the corresponding
  actual halting set when `T` is not Σ₁-sound. Only inclusions and disjointness
  are required; no soundness or ω-consistency is smuggled into the proof.
- The earlier finite-stage, range-completion, and cosheaf constructions are
  identified as possible means to supply general proof-observation data,
  not as prerequisites for the PA benchmark or as results invalidated by
  this simplification.

# (E) Acceptance conditions, non-negotiable

1. **Retain the uniform quotient.** Deliverable: construction review §1 and
   source check. Endpoint: the universal input quantifier remains inside
   the proof relation and composition congruence is justified by graph
   formulas. Status: met. Replacing this with separate instance proofs would
   invalidate the claimed category construction and require rejection of
   that replacement.
2. **Retain the domain-level scope of extraction.** Deliverable: §3.
   Endpoint: quotient invariance, effectivity from representatives, and the
   stated order properties are proved without claiming an all-arrow
   functor or general binary-join preservation. Status: met. Any stronger
   functor claim needs a separate construction and proof or must be dropped.
3. **Make the separator's two searches explicit.** Deliverable: §§2 and 4.
   Endpoint: both `C_T` and `N_T` are c.e., their disjointness uses
   consistency, their coverage uses only the stated completeness family,
   and `B⊆N_T` uses verified finite output-1 computations. Status: met.
   Omitting one of these points would leave the separator inference unproved.
   For the identity/zero route, the deciding searches are for `Eq(e,i)`
   and its negation, not for the two fibers as if they were complementary.
4. **Preserve the consistency and totality distinctions.** Deliverable:
   §6. Endpoint: no internal `Con(T)` or T-provable totality is inferred from
   external consistency/completeness. Status: met. An unsupported internal
   inference would have to be withdrawn.
5. **Keep the generalization as specified construction data.** Deliverable:
   §5, including the clarification in (C). Endpoint: name the fixed
   computational target and distinguish positive from negative observations;
   do not claim these have been constructed for arbitrary recursion
   categories. Status: met. The classical result may remain, but an unproved general
   existence claim would have to be dropped.

# (F) Not checked / uncertainty log

- Both review files were read completely. The typed quotient, graph
  composition law, least-domain and agreement range properties, identity/zero
  fibers, compiler reduction, domain extraction, and both separator proofs were independently
  reconstructed from the displayed data.
- Primary scan images independently inspected in this audit: Montagna 1989,
  printed pp.108 and 111, and Di Paola–Montagna 1991, printed p.646. They
  support the unprimed quotient, restriction domain, Turing morphism,
  ranges, and the distinction from dominical categories. No primed-system
  category claim was imported.
- Other source-page checks in `SYNTACTIC_SOURCE_CHECK.md` were performed by
  the source-checking collaborator, not repeated here. In particular this
  audit did not independently reread FailureOfComposition v37 or all earlier
  chat artifacts. Its mathematical conclusions depend on the displayed
  valid quotient and reconstructed laws, not on those historical claims.
- The earlier finite-stage and complete cosheaf constructions were not
  audited again. Their prior verification remains separate.
- A general nonnumerical family of proof-observation operations has not
  been constructed by this report. Section 5 records the problem rather
  than settling it.
- No Lean development was used as evidence. No originality judgment is
  being made about the classical essential-incompleteness argument.

Strongest confirmed blocker: none for the classical benchmark.
Strongest suspected unconfirmed blocker: none identified in its displayed
argument; existence of the proposed nonnumerical observation data remains
an explicitly open construction task.
Most important item not checked: a general construction realizing those
data outside the numerical syntactic benchmark.
Dependence on unavailable material: none for the displayed benchmark proof;
the historical comparison scope is limited as recorded above.
Final recommendation: **unknown** for the proposed general axiomatization;
no confirmed mathematical blocker remains in the classical route reviewed.
