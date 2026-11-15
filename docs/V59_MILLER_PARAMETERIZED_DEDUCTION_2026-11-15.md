# Lemma 9.6: Miller syntax and parameterized deduction

Lemma 9.6 is complete. The count is **73 of 77 numbered results proved**,
with Corollary 9.8 next. Manuscript v59, its source, PDF, archive and manifest
remain unchanged.

## Constructed proof

Write D_a = Tot(Split(E_a)).
`Miller.Derivation.Parameterized.uniformInitial` constructs an initial
finite-rule algebra in every slice of the uniform carrier category, with
arbitrary coefficient families and arbitrary target algebra operations.
`algebra` and `initial` construct the corresponding algebras in the actual
D_a. They use the existing concrete Miller derivation algebras and the
proved `SliceInference.algebraEquivalence` for the full inference functor.
The comparison retains parameter, rule and ordered child-conclusion labels.
Folds preserve conclusions and constructors; uniqueness covers every
underlying morphism with those equations.

These are morphisms of the original uniform category. Their representing
programs have common domains and values across all representations. No
fixed representation or ordinary recursive extension of a target operation
is supplied. The existing arbitrary-coefficient word and list constructions
and their transport through `Total.pointPresentation` remain the basis of
the syntax and evaluation proofs.

`Miller.ParameterizedDeduction.numbers` is the actual full numerical
variable object. `numbers_source_full` and `numbers_domain` prove that its
support is all natural numbers and its domain is the identity.
`nullaryPresentations` constructs syntax and stable lists for an arbitrary
object X of D_a as the nullary predicate labels, with empty function-symbol
coefficients and numerical variables. Its initial proof family is indexed
only by sentence axiom subobjects.

For a constructed syntax S, a parameter object P and any axiom subobject
A of P × S.sentenceObject, `axiomArrow` gives A its canonical projection to P;
its underlying morphism is exactly A.arrow, and it is monic. `rules` gives
the actual seven logical schemes, generalization and ordered modus ponens
in the parameter slice. `printedRules` has the literal type
`RulePresentation (P ⨯ S.algebra.a.2) 2`, so its inference functor acts on
the printed category D_a/(P × Fm). Its rule conclusions retain the parameter
of their rule instances.

`printedAlgebra` and `printedInitial` construct the finite-derivation
initial algebra there for every such A. This covers the nullary language
and all bounded finite signatures with arbitrary coefficient objects,
including every recursive signature in the printed proposition. Arbitrary
parameter-dependent axioms and target algebras are retained. No deduction
initiality is an input. The existing generation of arbitrary axiom
presentations through regular images is preserved.

`printedStatement` assembles the complete result without added hypotheses.
The independent Checks modules state the full quantifiers, the numerical
variable domain, syntax/list stability, both slice formulations, actual
axiom morphisms, parameter preservation, constructor equations and
uniqueness. The two producers and two Checks modules passed four targeted
strict elaborations and twenty principal axiom reports before the proof
commit.

## Verification

Proof commit: `fe124f6f458439aa34135b0d2c48c13bdf27dd18`. All **16 incremental commands** passed,
including **8 strict elaborations**, the project build, both statement
audits, parser tests, manuscript gate and both complete transitive axiom
audits. The current audit covers **998 production modules**
and **30,089 declarations**. The retained audit covers
**1,274 declarations**. All twenty principal reports and both
complete audits use only `propext`, `Quot.sound` and `Classical.choice`.
All sixteen dependency worktrees remained clean and pinned;
356 source-provenance pins were checked. All
**2,517 measured inputs** remained unchanged and matched the proof
commit.

The controlled delta contains four new Lean files, four production/audit
entry points and the selected correspondence table. Previous incremental
inputs were matched to their published proof commit before comparison;
its full-replay baseline reference is preserved. The
[machine-readable record](V59_MILLER_PARAMETERIZED_DEDUCTION_VERIFICATION_2026-11-15.json) includes command hashes, audit coverage,
principal reports, the targeted checks and the controlled source delta.
The raw record is
`.codex-work/v59-miller-parameterized-20261115/incremental-verification/verification.json`,
SHA-256 `642e8c842255c35a89eeb9b8f12239e19431e78564ee094b816eb5eebb033401`.

This is completed **incremental verification**. The last completed
[full v59 replay](V59_FULL_VERIFICATION_2026-11-14.md) remains the
1,798-command run at `8df18834734179186459d3c4c34d4c0cf20b6194`.

## Next obligation

Corollary 9.8 applies the completed Miller parameterized constructions to
every consistent internal sentence theory extending the expanded field
theory. Construct the associated category, essential incompleteness for
all closed consistent slice extensions, theorem/refutation inseparability,
the Boolean no-total-extension witness and the comparison functors for
inclusions of consistent theories. Construct the common logical theorem point
through every extension, as supplied by 0 = 0 in the printed proof.
Reuse Theorems 5.2–5.3 and the completed
Miller theory results. Preserve the printed Miller-sequence assumption,
subobject-only initiality, Boolean conventions and all extension quantifiers.
The four remaining numbered obligations are 9.8, 10.7, 10.8 and 10.9.
