## (A) Kill-shots / hard blockers

This is an author-side, AI-assisted source and correspondence audit applying
the HostileRefereeGPT — Cat/Rec workflow. It concerns the continuation from
`a5d369b3ce3ab161cdd5b87e530a182ea9787db9` in the author's repository,
not confidential third-party evaluation. The manuscript is v46, publication
`558a20eed4c62d59eada05f5500cf233671078e9`; PDF pages below are one-based.
The [source manifest](V46_CONTINUATION_SOURCE_SHA256.txt) fixes the 28 new
production files reviewed through principal proof bodies, public types and
their dependency interfaces. This is not an independent kernel replay.

**A1. Full-v46 completion remains unproved.** Anchor: PDF p.16,
Proposition 5.5, “for every object P,” and p.42, Lemma 8.1,
“one oracle program.” Claim assessed: that the entire manuscript has been
formalized. Failure mode: **unproved**. Evidence:
**absence_in_text / structural_argument**. The continuation constructs the
regular extensive syntactic total category and its model functors, but does
not construct the required syntax/list/inference initial algebras in every
parameter slice. The abstract initiality assumptions of Definition A.1 are
not concrete existence proofs. There is still no completed Miller category
with one program having the same domain and values at every representation
of a fixed sequence. These missing constructions block the corresponding
applications and a full-completion claim. Severity: **major** for
formalization completeness; repairable by the specific constructions in the
correspondence table. This is not a counterexample to the manuscript.

No false theorem or hidden strengthening was confirmed in the completed
continuation results. Their final compilation and axiom evidence are recorded
in the [continuation report](../V46_CONTINUATION_2026-11-03.md).

## (B) Major weaknesses

**B1. The unnumbered substitution laws remain open.** Anchor: PDF p.57,
Appendix A.3, the displayed admissibility-subobject equation and the paragraph
beginning “Identity substitution.” Claim assessed: full realization of named
substitution and its free-for semantics. Failure mode: **unproved** for that
larger claim. Evidence: **absence_in_text / structural_argument**. The
numbered Proposition A.3 is now constructed: its actual parameter-slice
algebra, original-component algebra morphism, unique fold, option-valued
formula operation and complemented success pullback are proved. This
resolves the prior review's missing-construction finding for A.3. Membership
of concatenation is also proved. Membership of deletion, the quantified
admissibility-subobject identity, and identity/absent-variable substitution
still need proofs. The capture test's occurrence-list meaning is not supplied
by the existence of its Boolean-valued morphism alone. Downstream impact:
concrete substitution realization and semantic substitution. Severity:
**major** for those pending claims; repairable without withdrawing the
numbered A.3 construction.

**B2. Standard decoded-code soundness still needs its concrete instance.**
Anchor: PDF p.24, Lemma 6.5 and Proposition 6.6, and pp.26–27, Theorem 6.9.
Claim assessed: soundness of the generated arithmetic sentence theory in its
arithmetic ultrapower. Failure mode: **unproved** for the full application.
Evidence: **structural_argument / absence_in_text**. The actual arithmetic
quotient, Łoś theorem, natural comparison and its canonical-domain and
recursive-carrier versions are now constructed. The transport theorem still
takes a standard validity inclusion, a standard proof-to-validity factor and
their disjointness as inputs. Constructing these for decoded named syntax,
all seven logical schemes and finite derivations remains necessary.
Consequently the full theorem is not certified by the transport helper.
Downstream impact: Theorem 6.9 and the categorical arithmetic comparison and
uniform-family applications. Severity: **major**; repairable by 5.4–5.8 and
6.5–6.6 followed by the implemented transport.

The previous review's remaining endpoint axiom-closure and Miller
representation-independence findings remain open; unchanged applications
were not re-audited here.

## (C) Minor issues

The old correspondence row wrote `U ⋙ G_N`, which is ill-typed in Lean's
diagrammatic convention. It now writes `G_N ⋙ U`, matching the actual
natural-isomorphism type. The manuscript's functional composition notation
was not changed.

The first complete verification attempt exhibited an entry-file import
placement error: new imports followed a module documentation command.
Moving them into the opening import block repairs this reproducibility
failure. No mathematical proof, hypothesis, source pin or dependency revision
was changed to obtain this repair. The failed run is retained separately.

## (D) Cross-section consistency failures

No confirmed inconsistency was found in the completed proof chain. The
following checks delimit the recovered statements.

1. **Proposition 4.1, PDF p.8.** The new `Par(D,Mono)` is an actual quotient
   of monic-left-leg spans, with composition by pullback and equality by
   span isomorphism. Only pullbacks are required for its category and four
   restriction axioms. `D ≌ Tot(Par D)` and restriction splittings are
   constructed. Regularity of D is used for the image range. The regular-epi
   cancellation argument works against partial maps, using pullback-domain
   descent, not only total arrows. Each ordinary mono has its explicit
   inverse span. `interpreted_theory` therefore proves the ordinary monic
   validity-subobject factorization and consistency implication without an
   inverse supplied as an additional field. Coproduct/zero structures used
   by the interpretation are retained as target data of the given range
   functor; they are not inferred from arbitrary regularity of D.

2. **Lemma 5.3, PDF p.12.** Objects are all one-variable Σ₁ predicates;
   morphisms are Σ₁ graphs with T proofs of support and unique totality,
   modulo T-provable uniform graph equality. The realization is full,
   faithful and essentially surjective under only `T ≥ PA`. Images are
   actual existential predicates with represented witness-search sections.
   Arbitrary monomorphisms are compared over their codomain with these
   inclusions, yielding every total-split mono's partial inverse.
   Terminal, product and equalizer universal properties supply finite
   limits; selected sections give kernel-pair coequalizers and stable
   regular epis. Finite sums are actual false/tagged predicates.

3. **Extensivity in 5.3.** An all-model bijective arrow has a represented
   converse Σ₁ graph: surjectivity proves its totality, injectivity proves
   uniqueness, and both inverse identities are proved in T. The functor
   to the family of all Type-0 arithmetic T-model interpretations therefore
   reflects isomorphisms. Pointwise finite-limit and binary-sum preservation
   permits the Mathlib extensive-category criterion. No consistency,
   computable-enumerability or chosen standard-model premise is introduced.
   For inconsistent T the model index is empty and provable graph equality
   collapses the hom sets; this case is compatible with the argument.

4. **Proposition 6.4, PDF p.23.** The model functions are characterized by
   the original interpreted graph on all elements of M. Their chosen-domain
   functor has literal domains of the interpreted restriction idempotents.
   The existing gamma coding equivalence is lifted through these domains
   to recursively interpreted products and coproducts. The graph equation
   quantifies every total-split morphism. Finite limits, finite coproducts
   and regular images are proved for the predicate, total, coded-domain and
   recursive-domain functors; image comparison equations are over their
   actual interpreted codomains.

5. **Lemmas 6.7–6.8, PDF pp.25–26.** Germs modulo a proper ultrafilter
   define the actual set functor. Equalizer and subset recovery fill outside
   an ultrafilter-large set using one coordinate from that set; no
   inhabitedness of an arbitrary subset is assumed. Finite-tag selection
   proves coproduct preservation, including empty carriers. Arithmetic has
   coordinate operations, native quotient equality and ultrafilter strict
   order. Łoś is proved for all finite formulas, with universal/existential
   steps ranging over the whole quotient. The predicate comparison sends
   a family to the same arithmetic class and is natural for arbitrary
   represented graphs. Extending through the proved equivalence and the
   two actual domain comparisons gives the natural isomorphism for the
   manuscript's original recursively interpreted carriers. Inverses are
   components of constructed natural isomorphisms, not assumed data.

6. **Proposition A.3 and Theorem A.6, PDF pp.57 and 60.** The substitution
   algebra retains original and computed components in the same parameter
   slice. At an equal-name quantifier it returns the original quantified
   body, even if recursive substitution failed. Its original projection
   is proved an algebra morphism, hence its fold is the identity. All
   seven actual axiom-scheme morphisms and their prescribed parameter
   pullbacks/fibers are constructed. `generated_firstOrder_theory` applies
   the proved image theorem to these actual rules, with exactly the stated
   initial-inference-algebra hypothesis. It does not construct that initial
   algebra in an application.

7. **Karoubi restriction, PDF p.4 and Corollary B.9, p.67.** For an arbitrary
   idempotent e, R4 and `e ≫ f = f` give commutation of e with the underlying
   restriction of f. The relative restriction is `e ≫ rst f`; all four
   axioms require only a restriction category. In partial maps, a constant
   retraction on a two-element set is a non-restriction idempotent; the
   formula correctly returns e as the restriction of the identity on
   `(X,e)`. Conjugation by total isomorphisms transfers preservation through
   a natural isomorphism and an inverse equivalence. The actual fork
   inclusion and Karoubi equivalence preserve this restriction operation.

8. **Lemma 5.4, PDF p.15, achieved fragment.** An arbitrary unary Σ₁
   condition has a PA-equivalent bounded-matrix witness-vector formula.
   The pinned `sigmaOne_skolem_vec` proof constructs witnesses by internal
   arithmetic induction, so nonstandard lengths are covered. Strict bounds
   on both vector reads are justified by `nth_lt_self`; the nil case has
   length zero and a vacuous bounded body. Finite Π₁ tag tests give a valid
   conditional-case fragment. Actual primitive-recursive pair tags and
   payload readers are constructed, with all-PA-model semantics. The
   conditional version leaves unrecognized tags unchecked; the separately
   constructed `selectedTaggedList` explicitly requires a tag in `Fin k`.
   A PA-Π₁ presentation for an arbitrary primitive-recursive tag reader is
   still unconstructed. The table therefore retains the full printed lemma
   as pending, while recording the proved unary and canonical tagged parts.

As a structural check of the generic partial-map scope, the two-object
category `0 < 1` has pullbacks and regular images: `Par(1,1)` has the two
domain idempotents, and its total subcategory recovers `0 < 1`, without
inventing a total map `1 → 0`. This is a source-level check, not a separate
executed Lean test.

## (E) Acceptance conditions, non-negotiable

1. The complete verifier must pass on fixed integrated sources, including
   old pins/audits and every new declaration's transitive axioms. Failure
   rejects the verified-batch claim.
2. Reports must retain the exact tested source identity and committed-byte
   delivery evidence. Failure rejects the reproducibility/delivery claim.
3. A full-v46 claim requires concrete parameter-slice syntax/list/inference
   initiality and proved named-variable/code/derivation comparisons.
4. It also requires decoded standard soundness, the partial proof-search
   lift, categorical arithmetic chain and indexed-family constructions.
5. It requires the representation-independent Miller program and category,
   and the remaining cosheaf inference/axiom-closure obligations. If 3–5
   are unmet, the full-v46 claim must remain withdrawn.

## (F) Not checked / uncertainty log

All new principal statements and their application boundaries were reviewed;
this is not an exhaustive human-style line audit of every auxiliary proof.
Compilation is not independent-kernel certification. Novelty, registry
verification and an independent kernel replay were not performed. No
manuscript prose or PDF was changed, and no new full-manuscript
Knuth–Larrabee–Roberts review is claimed. The manuscript and pinned dependency
integrity checks remain part of the project verifier.

Final self-audit: the strongest confirmed blocker is missing concrete
parameter-slice initiality for a full-v46 claim. No stronger suspected
mathematical blocker was confirmed in the completed batch. The most important
unchecked application is the representation-independent Miller realization.
The recommendation does not rely on unavailable referee material: **reject a
full-v46 completion claim** while accepting only the scoped results and
verification evidence explicitly reported.
