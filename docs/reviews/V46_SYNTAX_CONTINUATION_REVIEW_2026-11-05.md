# Author-side review of the syntax continuation

Scope: the 124 Lean source/check files added after `4cde20bb86ed`, their
required imports, changed correspondence rows and existing reports. The
completed 5.5/5.8 results are retained. This scoped review follows the
HostileRefereeGPT — Cat/Rec instructions and includes collaborating-agent
source/type checks. It is not an independent kernel replay or whole-paper
certification. The existing full integration verifier passed all 510 commands; final
source, axiom and committed-byte evidence is in the accompanying verification JSON.

The independent review of `3f53b33` inspected source and recorded evidence.
It did not independently rerun Lean or establish completion of v46, and found
no confirmed mathematical drift in that snapshot. Its distinctions remain:
evaluator uniqueness is not initiality; 5.8 needs arbitrary-rule initiality;
object coding and uniform trace comparison are separate; the arithmetic
application needs its categorical comparison. Rows 9.1/B.10 retain the
corrected numerical tuple status. Manuscript prose revisions are deferred.

## (A) Kill-shots / hard blockers

No mathematical counterexample or confirmed hypothesis drift was found in
the inspected new endpoints. The retained 5.5 and 5.8 universal properties
use constructed algebras and original typed rule pullbacks. The open
comparisons and applications below prevent a full-v46 completion claim.

## (B) Major weaknesses

1. **Uniform computation composition/specialization is still unproved.**
   Anchor: Lemma 5.1, `lem:arithmetized-evaluation`,
   `05-syntactic-recursion-category.tex`. Failure mode: **unproved**;
   evidence: **structural_argument**. The actual trace predicate now has a
   primitive-recursive certificate and a PA defining-program graph
   comparison. Internal history prefix/lookup comparison also holds at
   arbitrary stages, indices and inputs. The missing endpoints are uniform
   composition and specialization, PA-total parameter-index programs and
   their production graph/index equations. Native computation identifies
   only the standard primitive-recursive denotation; it is not the proof of
   the all-model PA equations. Exponential/parity object coding is complete.

2. **Categorical substitution and TotalSplit operation comparison remain.**
   Anchor: Proposition 5.7, `prop:st-substitution-realization`,
   `05a-internal-syntax.tex`. Failure mode: **unproved**;
   evidence: **absence_in_text** at the remaining final endpoints. Actual
   PA numerical algorithms, primitive-recursive certificates, typed
   preservation, raw constructor equations and independent FF/success
   equivalence are proved. Actual append/member/delete and FV agree with
   their categorical folds through proved Hom/uniqueness arguments. The
   actual sentence image is T-provably plain Fm with FV=0. Standard numerical
   substitution and recursive named FreeFor also agree. Still required:
   the actual parameterized substitution algebra Hom, its stable-initiality
   comparison, the success/admissibility pullback comparison, and genuine
   list/Boolean/option/substitution transport through chosen TotalSplit
   isomorphisms. A preimage object's raw code is not assumed to be the
   original variable or formula code. Fold-transport helper lemmas alone do
   not close this obligation.

3. **Complete coded soundness and the arithmetic application remain.**
   Anchors: 5.9, 6.5–6.6, 6.9 and 7.1–7.3. Failure mode: **unproved**;
   evidence: **structural_argument**. Constructed proof initiality now gives
   structural formula/sentence closure and leastness, source ranges and
   idempotent representations. The standard named-code bijection and actual
   numerical substitution comparison are proved. Standard induction on the
   constructed derivation carrier, four actual coded scheme validities,
   both rule validities and formula-level validity-negation disjointness are also proved.
   Distribution, instantiation and equality-substitution validity through
   their actual parameter fibers, followed by the actual derivation validity
   factor, its unique sentence restriction and the actual sentence-negation preimage comparison are still required. Only
   that factor can instantiate the existing ultrapower transport. The
   Gamma predicates, diagonal bounds, partial search lift and categorical
   comparison application remain necessary; importing arithmetic
   incompleteness is not a replacement.

## (C) Minor issues

**Import placement repaired.** The first full integration run failed at
`CategoricalEssentialIncompleteness.lean:430`: 19 new imports followed the
module documentation command. Moving them into the initial import block is
the complete repair. No proof statement or body changed. The failed run,
source snapshot and logs remain in
`.codex-work/verify-20261105T125509Z-nDj91A`.

**Elaboration cost controlled without changing mathematics.** Concrete
carrier aliases and expanded numeric graphs caused ordinary-budget
normalization failures. Opaque generic arithmetic/geometry helpers and
saturated rewrites avoid those expansions. The propositional semantic
calculation uses an abstract model functor, then immediately instantiates
its implication/negation clauses with the proved actual constructor laws.
No Lean limit or linter was disabled and no conclusion was added as an
application premise. Failed drafts and logs remain preserved.

## (D) Cross-section consistency

- Syntax initiality retains the manuscript polynomial, named variables,
  ordered children, arbitrary coefficients, arbitrary parameter families
  and arbitrary operations proved total in T. It requires no consistency,
  c.e., soundness, standardness or PA/primitive-recursive target operations.
- The numerical algorithms have separate PA-level and primitive-recursive
  proofs. The equal-binder branch keeps the original body even if its
  recursive result fails. The independent free-for recursion is not defined
  to mean successful substitution.
- The standard syntax bijection preserves names, labels and order. It does
  not identify nonstandard words with external finite trees. No binder-name
  erasure is used as equality of syntax presentations.
- Each child in the original rule pullback has its own conclusion. The
  standard node-count theorem bounds every such child. Constructor cases
  follow from the actual initial structure isomorphism and finite coproduct
  preservation, not from an assumption of Set initiality preservation.
- The general standard-induction helper explicitly assumes N models T; its
  soundness application uses PA. Semantic K and arithmetic code M/N remain
  distinct. Validity-negation disjointness retains nonempty K.
- Literal Sent is the image of the actual sentence inclusion on formula
  coordinates. The chosen sentence pullback carrier need not use those
  coordinates. Source program graphs remain PA-functional independently of
  ambient T-total operation graphs.
- Fixed standard parameter-free graphs do not cover arbitrary nonstandard
  indices or model parameters. External consistency of Gamma does not give
  a PA proof of consistency. Keep M elementarily equivalent to N where the
  arithmetic theorem requires it. The search lift remains partial.

## (E) Acceptance conditions

1. Pass the existing combined build, both statement audits, every strict
   production/check replay and the transitive axiom audit. Retain all
   earlier audited declarations and only the permitted axiom union.
2. Compare all tested inputs with committed bytes; confirm the ordinary main
   push and remote ref, then check committed-byte Downloads copies.
3. Keep the precise remaining 5.1, 5.7, 5.9 and 6.5–7.3 obligations separate.
   Do not count declarations, evaluator uniqueness, standard extensionality
   or transport interfaces as completed manuscript results.
4. Continue the principal logical chain after delivery. Defer later indexed,
   numerical-inference, Miller and cosheaf applications while it is unfinished.

Full verification exited 0 in `.codex-work/verify-20261105T125741Z-QgX9an`. All 763 tested
input hashes match proof commit `5a361496f90f5bc20907182d35a883097959f63c`;
the ordinary push and remote ref were checked. The delivery receipt records
the final report commit and six copied-byte hashes. No unfinished draft is counted.
