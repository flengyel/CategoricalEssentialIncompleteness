# Author-side review of the syntax continuation

Scope: the new Lean constructions and changed correspondence rows since
`0c7fdc79e26cf0f7da360a4c84f2773b1ad12b3a`. This is an author-side audit,
using the HostileRefereeGPT — Cat/Rec instructions, with separate source
reviews by the collaborating agents. Compilation and transitive axiom
results are recorded in the accompanying verification JSON. This review
does not certify the whole manuscript or an independent kernel replay.

## (A) Kill-shots / hard blockers

No mathematical hard blocker was confirmed in the completed constructions.
The open application obligations below prevent a claim of complete v46
formalization.

## (B) Major weaknesses

1. **The printed uniform computation presentation remains unproved.**
   Anchor: §5, `05-syntactic-recursion-category.tex`, Lemma 5.1,
   `lem:arithmetized-evaluation`, and the preceding definition of
   `Tr(e,x,t)`. The claim is PA-provable uniform evaluation, composition
   and specialization for the printed deterministic trace coding.
   Failure mode: **unproved**; evidence: **structural_argument**. The new
   exponential pairing, inverse graphs, formal-object isomorphisms and
   recursive model comparison prove the object-coding comparison for the
   production quotient programs. They do not construct a compiler between
   the production stage evaluator and the printed three-variable trace
   predicate. Downstream: literal presentation identifications remain
   qualified. Severity: major for full completion; repairable by the
   stated uniform graph and index equations. No counterexample to Lemma
   5.1 is claimed.

2. **Syntax evaluation does not yet establish categorical initiality.**
   Anchor: §5, `05a-internal-syntax.tex`, Proposition 5.5,
   `prop:st-syntax-initiality`. The claim is initiality for every actual
   two-sorted algebra in every parameter slice. Failure mode:
   **unproved**; evidence: **absence_in_text** in the production endpoint.
   Arbitrary predicate-category slice algebras are decoded, literal postfix constructors and
   parser framing are proved, and positive finite records give unique
   accepted-word evaluation and actual arrows over the parameter. The
   constructor commutation equations, algebra-Hom uniqueness and
   initiality package and final TotalSplit syntax transport remain uncompiled drafts. The parser carrier's
   stored-word check also needs the conservation/decomposition comparison
   with the plain printed parser predicate. Downstream: the concrete
   syntax instance and its later named substitution comparisons remain
   pending. Severity: major for full completion; repairable by these
   universal-property proofs. No evaluator or initiality conclusion has
   been inserted as a premise of the completed decoder.

3. **Typed rule inputs do not yet supply finite-derivation initiality.**
   Anchor: §5, `05a-internal-syntax.tex`, Lemma 5.8,
   `lem:syntactic-derivation-initiality`, and its typed rule pullbacks.
   Failure mode: **unproved**; evidence: **structural_argument**. The
   actual finite-power encoder, original rule-input pullback,
   `ruleInputIso` and conclusion equation are constructed. Positive
   finite-record nil/cons/singleton laws and conditional functionality
   are proved. The valid proof-tree carrier and arbitrary-algebra
   evaluator/uniqueness are still required. Different child conclusions
   and the parent conclusion share only the external parameter; treating
   them as one formula fiber would change the endofunctor. Downstream:
   the concrete generated-theory and soundness applications remain open.
   Severity: major for full completion; repairable by the remaining
   typed construction.

## (C) Minor issues

**Resolved integration collision.** Anchor: the new
`V46SyntacticSyntaxSorts` and `V46SyntacticSyntaxRefillLaws` imports.
Failure mode: **irreproducible** before the repair; evidence:
**toy_test**, the combined import rejected duplicate generated local
instance names. The Sorts instance now has an explicit unique name and
its build and strict checks were rerun successfully. No hypothesis or
mathematical definition changed. Severity: minor; resolved.

**Resolved documentation-token rejection.** The first full run passed all
263 Lean commands, but its final unchanged source scan matched an ordinary
English verb in the Evaluation documentation. Rephrasing that sentence
changed no definition or proof. The failed run was preserved and the
complete verifier repeated. Severity: minor; resolved by a prose change.

## (D) Cross-section consistency failures

No additional inconsistency was confirmed in the reviewed endpoints.
The following distinctions were checked against the actual types.

- `term_substitution_absent` and `formula_substitution_absent` quantify
  over arbitrary generalized elements in an arbitrary regular, finitary
  extensive category with the stated categorical syntax. The false
  membership fibers and formula admissibility lift are constructed.
- Decidable equality for arbitrary represented variable objects is an
  actual diagonal pullback, then transported through the proved
  equivalences. It does not assume decidable membership of a Σ₁ carrier.
- Exponential pairing and inverse equations hold at all elements of all
  PA models. Standard primitive-recursive certificates are separately
  proved. The recursive gamma comparison uses actual inverse program
  classes and the direction `gamma_Q.inv ≫ f ≫ gamma_R.hom`.
- Numerical list initiality uses the standard true theory comparison and
  ordinary computable totality. Its external categorical equivalence does
  not assert a uniform computable transformer on arbitrary program indices.
- The literal category `WalkingSpan ⥤ NumericalTuples.Object` has actual
  regular/extensive instances and an ordinary monic-span comparison.
  The additional restriction-category structures checked in the coded
  fork presentation are reported in that presentation.
- A separate source review of State, Evaluation, Sorts, Simulation,
  Interpretation and Fold, with their Checks, confirmed the internal
  induction, typed domains and over-parameter scope. Positive Σ₁ records
  never branch on the negation of arbitrary Σ₁ coefficient membership. The PA run theorem assumes local step
  functionality; it does not assert that PA proves the functionality of
  every operation whose totality was proved only in T.
- The fixed standard graph constructions for B_T do not establish all
  C(M) realizations with nonstandard indices or model parameters. Those
  later model-local instances remain separate obligations.

## (E) Acceptance conditions, non-negotiable

1. Build the combined entry point and both statement audits, retain all
   previously audited declarations, and audit the transitive axioms of
   every new production declaration. Failure rejects this proof batch.
2. Keep all effective hypotheses, concrete instances and open endpoints
   explicit in the correspondence table. Failure rejects a full-coverage
   claim.
3. Complete the uniform trace comparison before identifying the printed
   computation presentation. Until then that identification is pending.
4. Prove constructor laws, algebra-Hom uniqueness and slice initiality
   before claiming Proposition 5.5 or its transported syntax instances.
5. Construct the typed finite-derivation evaluator and its initiality
   before claiming Lemma 5.8 or the dependent concrete theory instances.
6. Match every tested input to committed bytes and confirm the pushed
   remote ref and Downloads copies. Failure precludes a delivery claim.

## (F) Not checked / uncertainty log

The full manuscript, novelty, independent kernel replay, registry
verification and PDF layout were not reviewed here. Ignored continuation
drafts are not counted as proved. The separate model-local semantic,
arithmetic Γ-instance, indexed-family, Miller uniformity and cosheaf
inference-initiality obligations remain as listed in the table.

Strongest confirmed blocker to full completion: concrete syntax and
derivation initiality remain unproved. Strongest suspected but unconfirmed
issue: the remaining model-local comparisons may require additional
uniform coding machinery; no false manuscript assertion is established.
Most important unchecked work: the resulting concrete soundness and
arithmetic comparison chain. The scoped conclusions rely on available
source and compiler evidence; a judgment on the whole manuscript would
require material outside this review. Final recommendation: **unknown**
for the complete manuscript formalization.
