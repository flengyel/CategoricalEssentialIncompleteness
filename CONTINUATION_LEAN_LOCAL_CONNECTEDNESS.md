# Continue the Lean formalization of categorical essential incompleteness

These are retained instructions for the completed v5 baseline.
The current target is v46; use [docs/CODEX_WSL2_V46.txt](docs/CODEX_WSL2_V46.txt)
and [FORMALIZATION_STATUS_V46.md](FORMALIZATION_STATUS_V46.md) for new implementation.
The earlier task text is preserved below.

Resume substantive Lean work in `flengyel/CategoricalEssentialIncompleteness`. Formalize the current paper, **Local connectedness, range functors, and essential incompleteness**, Version 5, including its applications and appendices. The first objective is the abstract categorical proof through Corollary 6.7; it is the beginning of the full-paper formalization, not its stopping point.

## Authoritative mathematical source

- Repository: `git@github.com:flengyel/CategoricalEssentialIncompleteness.git`.
- Reviewed manuscript baseline: commit `883f1f792a5e4a244974d00458e8a9dee61b2f94`.
- LaTeX: `manuscript/archive/essential_incompleteness_via_local_connectedness_v5.tex`.
- PDF: `manuscript/archive/essential_incompleteness_via_local_connectedness_v5.pdf`.
- Existing Lean entry point: `Lean/CategoricalEssentialIncompleteness.lean`.
- Existing verifier: `scripts/verify.py`.
- Current pinned toolchain: `leanprover/lean4:v4.35.0-rc2`; retain the repository's dependency pins unless an actual implementation obstacle requires a justified change.

Work in the existing WSL2/Debian checkout, normally `/home/flengyel/src/CategoricalEssentialIncompleteness`. Inspect the current branch, changes, remote and applicable `AGENTS.md` files. Fetch over SSH and reconcile newer work without discarding local changes. The baseline identifies the mathematical source; it is not an instruction to reset the checkout to an older commit. If the manuscript has subsequently changed, identify the mathematical changes before selecting the formalization target.

`FORMALIZATION_STATUS.md`, `FORMALIZATION_REQUIREMENTS.md`, the old entry-point commentary, and `CONTINUATION_GENERAL_RECURSION_CATEGORIES.md` contain earlier targets. Their definability-algebra, enrichment, PER and Lindenbaum-quotient agenda does not govern this task. This prompt supersedes those mathematical targets where they conflict with v5. Preserve useful existing results and build safeguards. Update the current status and requirements to distinguish the v5 work from the earlier development, retaining the historical record.

## Why the formalization is being resumed

The earlier Lean development proved representation-based statements and an arithmetic incompleteness consequence, while the connection from its recursion-category machinery to its intended categorical theorem remained incomplete. The manuscript has since been rebuilt around a different, explicit argument:

1. Local connectedness in a target restriction category gives particular sections.
2. A section-lifting condition and the source Turing morphism produce inseparable restriction idempotents in the source recursion category.
3. Explicit morphisms connecting that pair to theorem and refutation restriction idempotents imply essential incompleteness.
4. The syntactic, arithmetic and three-point-space constructions establish the relevant instances.

Two separate model reviews found no confirmed mathematical defect in the current arguments. Follow-up checks reconstructed the PA proofs required by the syntactic and arithmetic constructions. Those are ordinary mathematical reviews, not Lean proofs. Use their conclusions as context for implementing the mathematics, not as axioms or as evidence that any new Lean declaration already exists.

## Exact categorical target

Read Sections 2 and 6 before choosing interfaces. In the paper, composition is `gf = g ∘ f`; Lean's `f ≫ g` applies `f` first. Translate every formula accordingly.

For a partial morphism `f : X ⇀ Y`, write `bar f` for its restriction idempotent. For a restriction idempotent `e` on `Y`, its inverse image is `f*e = bar(e f)`. A complementary pair `c,c'` on `X` satisfies `cc'=0_X` and `c∨c'=1_X`. A disjoint pair `a_0,a_1` is inseparable if there is no complementary pair `c,c'` with `a_0≤c` and `a_1≤c'`.

The range operation must satisfy both leastness among restriction idempotents receiving a morphism and the paper's agreement law. Local connectedness means that connected restriction idempotents are jointly epimorphic in the precise sense of Section 2. A partial monomorphism and its section have the definitions given there. Do not replace these definitions by informal set-theoretic analogues in the abstract theorem.

### Proposition 6.2 — `prop:local-switch`

The target is a locally connected **split** restriction category with ranges, restriction zeros and binary restriction coproducts. It satisfies weak choice, and inverse images along arbitrary morphisms preserve binary joins of restriction idempotents.

Prove the connected-alternative lemma and the proposition in full, including the passage from total test morphisms to arbitrary partial test morphisms using restriction splitting. For disjoint restriction idempotents `a,b` on `X`, prove that `p = ∇_X(a+b)` is a partial monomorphism with a unique section `s`, and that

```text
p s = bar s = a ∨ b.
```

For complementary `c,c'`, obtain the total section of `∇_X(c'+c)` satisfying `s c = i_1 c` and `s c' = i_0 c'`.

### Theorem 6.3 — `thm:local-lifting`

Use a source recursion category `R` with ranges and binary restriction coproducts, and a target `A` satisfying Proposition 6.2. A range functor `F : R → A` preserves restrictions, ranges, restriction zeros and binary restriction coproducts. Define its canonical coproduct comparison

```text
χ_{X,Y} : F X + F Y ≅ F(X+Y).
```

Choose a source Turing morphism `τ : U×U ⇀ U`, an isomorphism `b : U ≅ U+U`, and require `F(1_U) ≠ 0`. For every complementary source pair `c,c'` on `U`, obtain the target section `s_c` from Proposition 6.2 and assume a source morphism `ℓ_c : U ⇀ U+U` satisfying

```text
F(ℓ_c) = χ_{U,U} s_c.
```

Prove inseparability of the actual restriction idempotents

```text
a_0 = (b τ Δ_U)*(1_U + 0_U),
a_1 = (b τ Δ_U)*(0_U + 1_U).
```

The proof must obtain the total parameter morphism from source Turing universality, prove the diagonal equation in the source, and then apply `F`. Local connectedness supplies target sections; it does not supply an inseparable pair in the target.

Preserve the theorem's exact generality:

- The source is not assumed locally connected, and the target is not assumed to be a recursion category.
- `F` is not assumed faithful, product-preserving, or totality-reflecting.
- The source lifts `ℓ_c` are not assumed total.
- Only sections associated with complementary **source** pairs are required to lift. Do not assume arbitrary target separators lift.
- Do not replace the lifting hypothesis by the stronger existence of joins of all suitable parallel arrows. Proposition 6.4 proves a sufficient condition separately.

### Corollary 6.7 — `cor:domain-incompleteness`

Formalize the statement in a restriction category with restriction zeros and binary joins of restriction idempotents preserved by inverse image along **total** morphisms. Given inseparable `a,b` on `U`, total morphisms `θ : U → S` and `ν : S → S`, and a restriction idempotent `t_0` on `S`, assume exactly

```text
a ≤ θ* t_0,
b ≤ θ* (ν* t_0).
```

For every restriction idempotent `t ≥ t_0` satisfying `t (ν* t) = 0_S`, prove that `t,ν* t` are inseparable and hence `t ∨ ν* t ≠ 1_S`.

Export a combined categorical essential-incompleteness theorem that first derives its pair from Theorem 6.3 and then applies Corollary 6.7. Include Corollary 6.7's additional hypotheses explicitly; do not assume they follow from Theorem 6.3. Prove the required preservation of inseparability under the inclusion into the restriction splitting when an application constructs its sentence and proof objects there.

## Implementation order and complete scope

Use dependency order rather than manuscript order where useful. Work continuously through the following objectives; they are not approval gates.

1. Inspect and reuse the existing restriction, product, coproduct, range, numerical and arithmetic code where its definitions and hypotheses agree with v5. Prove explicit comparisons for alternative presentations that are reused. Implement the missing abstract structure and prove Proposition 6.2, Theorem 6.3, Proposition 6.4, Corollary 6.7 and their combined consequence.
2. Construct the uniformly provable syntactic categories `S_T`, their model functors, the faithful family of model interpretations, theory-extension functors, and the syntactic section lifts. Establish the results of Sections 3–6 under their stated hypotheses.
3. Instantiate the categorical theorem in the classical recursion category. Construct the sentence and proof objects, conclusion range, negation and numeral-substitution morphisms, and the two required inclusions. Derive recursive inseparability of the theorem and refutation sets of every consistent c.e. extension of PA, then incompleteness, through the newly formalized categorical results.
4. Formalize the three-point-space construction, its Turing morphism, syntax and finite-proof objects, consistency, internal essential incompleteness and endpoint observations. Include the structural and non-equivalence results in Appendix A and the syntax/proof results in Appendix B.
5. Formalize Appendix C's counterexample to the theorem with section lifting omitted. It is part of the full-paper target, not an optional illustration.

Maintain a correspondence table for **all 24 numbered results**, with exact Lean declarations, hypotheses and status, together with the unnumbered constructions needed by their proofs. These are the stable LaTeX labels:

| Part | Labels |
| --- | --- |
| Sections 4–5 | `prop:model`, `thm:faithful` |
| Section 6 | `lem:connected-alternative`, `prop:local-switch`, `thm:local-lifting`, `prop:disjoint-joins`, `lem:switch`, `cor:pair`, `cor:domain-incompleteness` |
| Sections 7–8 | `cor:arithmetic`, `prop:endpoint`, `thm:cosheaf-observation` |
| Appendix A | `prop:fork-cosheaves`, `prop:fork-total`, `prop:fork-structure`, `prop:fork-local`, `lem:fork-dominance`, `lem:fork-frames`, `thm:fork-turing`, `prop:fork-recursion`, `prop:fork-distinction` |
| Appendix B | `prop:fork-syntax-initial`, `thm:fork-proof-presentation` |
| Appendix C | `prop:missing-lift` |

Do not mark the current paper formalized because an older theorem has a similar name or numerical conclusion.

## Application-specific requirements

### Syntactic categories and PA

Use uniformly quantified provable graph equality. Do not use the pointwise equivalence relation of the primed systems. A fixed programming system must have PA-provable functionality, composition, structural coding, universal evaluation and parameterization identities; the parameter program must be PA-provably total. Ordinary acceptability of a numbering alone does not establish these claims.

For the switch in Lemma 6.5, write the two Σ₁ predicates as `C(x)=∃u R(x,u)` and `C'(x)=∃v R'(x,v)` with fixed primitive-recursive witness tests. Search increasing finite bounds, using a fixed priority if both tests succeed. Prove in PA that the program halts exactly when `C(x)∨C'(x)` and, under disjointness, that its graph is

```text
(C(x) ∧ z=i_1(x)) ∨ (C'(x) ∧ z=i_0(x)).
```

Then use the theory's proofs of coverage and disjointness to obtain totality and the graph equation in `T`. Quantified computations in a model range over its entire carrier, including nonstandard elements. The PA proofs must justify that interpretation uniformly.

The paper-level reconstruction uses deterministic coded computations, PA induction on coded runs, and explicit composition, interpretation and specialization constructions. Montagna (1989), printed pp. 108–109, invokes formalized s-m-n and supplies PA-exact Σ₁ graph representation; note 1 on p. 115 gives the computation convention. These sources justify the mathematical target; cite them accurately and prove the required Lean statements or instantiate already proved results with matching definitions.

For Section 7, standard finite computations supply PA proofs of individual numeral instances. PA-provable functionality and parity give the universal disjointness needed for the negative instances. Preserve the distinction between these numeral proofs, a uniform graph equation, and a theory's proof of universal halting. Do not impose soundness or Σ₁-soundness on the consistent extensions. Do not identify internal inseparability in `S_T` with effective logical incompleteness without the additional construction in Section 7.

### Three-point example

Use the indexing category and functor category defined in the paper. Distinguish the components of a functor from the values of its associated cosheaf on open sets; the value on the whole space is a pushout. The three-point space is obtained by gluing two Sierpiński spaces and is not itself the two-point Sierpiński space.

Prove equality of partial morphisms, including equality of their restrictions, in the Turing-factorization construction. Construct the actual syntax and proof objects, their universal properties, conclusion range, atomic inclusions and consistency argument. Do not assume decidable internal equality of the universal object or replace the example by an equivalent numerical category. Apply Theorem 6.3 and Corollary 6.7 to obtain its incompleteness results.

## Prevent recurrence of the earlier mismatch

The abstract combined theorem must derive its inseparable pair using the source Turing morphism and the local-connectedness/section-lifting argument. The incompleteness applications must actually instantiate that theorem; the syntactic-category application must instantiate Theorem 6.3. A separate classical incompleteness proof, an unused categorical theorem, or an unexplained inseparability assumption does not complete this task.

Do not place a desired conclusion or an unproved decisive lemma in a structure field and then claim its construction. A conditional intermediate lemma is legitimate when its remaining hypotheses are recorded and subsequently discharged in the promised instances.

Inspect imported interfaces for stronger assumptions: full Boolean lattices of restriction idempotents, arbitrary joins of parallel morphisms, extra properties of the functor, or a range operation lacking agreement. These are compatibility checks, not assertions that the imported code is defective. Keep weaker internal lemmas when useful and export the exact manuscript statements.

Preserve existing working proofs. Do not make completion of the superseded enrichment or Lindenbaum programme a prerequisite for v5. Use restriction-category terminology in new mathematical documentation; retain existing API identifiers where renaming would cause needless disruption. Define symbols and morphism types before use. Keep implementation and review commentary outside the manuscript.

## Verification, reporting and delivery

- No `sorry`, `admit`, new mathematical axioms, or unproved instances in the completed dependency chain. Retain the verifier's permitted axioms: `propext`, `Quot.sound`, and `Classical.choice`.
- Inspect the fully elaborated types of the exported results and their transitive proof dependencies. Check that the combined theorem and its applications use the new categorical construction and have no hidden extra hypotheses.
- Build changed modules while implementing. Integrate them into the project entry point and transitive axiom audit, then run `python3 scripts/verify.py` from the repository root. Extend source and manuscript tracking for v5 transparently; do not alter recorded hashes or weaken checks merely to make the verifier pass.
- Run checks required by the actual changes. Reuse successful verification of unchanged work; do not create repeated verification rounds or artificial checkpoints. A build failure, new change or unresolved concern may justify another run.
- Keep a concise current correspondence table and record the first exact unproved inference if a genuine mathematical obstacle remains. Declaration counts alone do not establish theorem fidelity or completion. Request an independent review of the substantive statements and dependency chain when those proofs are available, and resolve concrete findings.
- Commit completed, validated changes to `main` and push over SSH without force. Preserve unrelated work and existing stashes. Report the commit, the mathematical results completed, the checks actually run, and any remaining results. Do not claim a build, push, formalization or external verification that was not performed.

Begin with the existing source and the exact interfaces needed for Proposition 6.2, then prove the categorical chain. Do not stop after a plan, a scaffold or a documentation update. Continue through the full-paper target unless a concrete unresolved mathematical or environmental obstacle prevents progress; report that obstacle precisely without declaring the remaining work complete.
