# Categorical implication to essential incompleteness

Focused author-side audit under the HostileReferee skill. Reviewed source:
`manuscript/essential_incompleteness_via_local_connectedness_v2.tex`.
Snapshot SHA-256: `7d134f58d42e86728f8d9ddeeefbe4dd8269d24e9086171d55dae5155d6af288`.
Scope: Theorem `thm:local-lifting`, its classical instance, Corollary
`cor:domain-incompleteness`, and the arithmetic section. No manuscript
edits were made by this reviewer.

## (A) Kill-shots / hard blockers

No mathematical blocker is confirmed in the current categorical
implication. The source already contains the missing general corollary
and its fully typed arithmetic application. The implication is:

1. The range-functor lifting theorem applies to
   `J: Rec -> Pfn`. Singleton domains establish local connectedness of
   the target; subsets split domains; partial injections have partial
   inverses; inverse images preserve unions. Each complementary pair of
   c.e. source domains is decidable, so its tagged-input selection map is
   partial recursive and total. This verifies the precise lifting
   hypothesis. The output is the inseparable pair `a,b` on `N` determined
   by the even and odd outputs of the chosen universal self-application.
2. Pass to `Split(Rec)`. The embedding is fully faithful on `N`, so its
   domains and complementary pairs are unchanged. Thus `a,b` remain
   inseparable. The splitting contains the recursive sentence carrier
   `S` and the c.e. carrier `Prf_T` of finite proofs from a c.e. theory.
3. The conclusion map `c_T: Prf_T -> S` is total on its stated carrier.
   Its range `t_T` is exactly the c.e. theorem domain. Negation is a total
   map `nu: S -> S`; the refutation domain is `nu* t_T`.
4. Numeral substitution is a total map
   `theta: N -> S`, `n |-> code(alpha(n))`. The exact finite computation
   trace of any member of `A` gives a PA-proof of `alpha(n)`. A trace for
   a member of `B` gives a PA-proof of `beta(n)`, and PA proves their
   incompatibility from determinism and even/odd disjointness. Therefore
   `a <= theta* t_PA` and `b <= theta* nu* t_PA`.
5. Theory extension gives `t_PA <= t_T`. Consistency gives
   `t_T (nu* t_T)=0`. If T were complete, then
   `t_T join nu* t_T=1_S`. Pullback along the total `theta` preserves
   zero, meets, joins and top. Hence `theta* t_T` and
   `theta* nu* t_T` would be complementary domains separating `a,b`,
   contrary to step 1.

Evidence: derivation and structural argument. No soundness of T is used.
No independent invocation of the classical recursive-inseparability
 theorem is needed: that pair is obtained from `thm:local-lifting`.

## (B) Major weaknesses

**Abstract dependency remains misleading in the reviewed snapshot.**
Anchor: abstract, “For the arithmetic application, interpreting programs
in all countable models ... We prove a categorical inseparability theorem
and apply it to this functor. Finite computations then give ...”.
Failure mode: ambiguous / inconsistent_use. Evidence: the arithmetic
proof explicitly uses `J: Rec -> Pfn`, whereas the preceding abstract
sentences identify the model-family functor `F_T: S_T -> D_T` as the
functor giving that application. These are different theorem instances;
the current text leaves the latter-to-incompleteness implication
unstated because it is not the argument proved in the body. Severity:
major exposition/dependency defect, repairable by naming the classical
instance first and presenting `F_T` as another application of the same
categorical theorem. This does not invalidate the current arithmetic
proof.

Concrete repair: state that the theorem applied to the classical
recursion category supplies inseparable domains, that numeral
substitution puts them inside the arithmetic theorem and refutation
domains, and that hypothetical completeness contradicts their
inseparability by inverse image. Only then describe the faithful
model-family functor and the nonnumerical application.

The stronger conclusion proposed after this snapshot is also valid:
for every consistent domain `t >= t_0`, the pair `t,nu* t` is inseparable
on `S`. Indeed, if complementary `c,c'` on S satisfy `t <= c` and
`nu* t <= c'`, their inverse images along theta are complementary and
contain a,b. This contradicts inseparability. Coverage is impossible as
an immediate consequence, since a complementary pair separates itself.
For arithmetic, this proves recursive inseparability of the full theorem
and refutation sets, not only their numeral-instance inverse images.

## (C) Minor issues

The arithmetic section currently begins “Take b ... in Corollary
`cor:pair`”, which first points to the syntactic category, although the
argument immediately and correctly establishes the classical instance
independently. Prefer choosing the parity isomorphism directly in `Rec`,
and then noting that the same programs define the syntactic pair.
Evidence: absence of a needed dependency on `cor:pair`; no theorem error.

The finite-computation claim is sufficient as written under the declared
programming-system assumptions. An explicit formula for `alpha` and
`beta` would improve the reader's verification: they assert respectively
that the deterministic self-application computation halts with output
`2m` or `2m+1`, for some `m`. This makes the PA proof of incompatibility
and both numeral-instance inclusions visible without a separate
arithmetization appendix.

## (D) Cross-section consistency failures

The abstract defect above is the only confirmed mismatch in this focused
scope. The Introduction already separates the classical theorem instance
from the model-family construction.

The general domain corollary has exactly the required hypotheses:
`theta` is total, so its inverse image preserves top; binary joins are
preserved along total arrows by hypothesis; the map `nu` is total, so
it represents ordinary negation on the whole sentence object. No
involution law for `nu` is required by the contradiction. It would be
unnecessary to assume a double-negation identity on sentence codes.

The claims about `S_T` must remain distinct. Internal inseparability in
`S_T` alone does not establish logical incompleteness. The source itself
correctly notes that true arithmetic is complete and its corresponding
syntactic category still has inseparable domains. External completeness
of a c.e. T decides each standard numeral instance, but that is not a
uniform T-proof of a complementary source-domain decomposition. The
present proof avoids this unsupported step by using effective proof
ranges in `Split(Rec)`.

## (E) Acceptance conditions, non-negotiable

1. Retain Corollary `cor:domain-incompleteness` with its typed maps and
   join-preserving inverse-image hypothesis; its displayed contradiction
   must remain part of the paper. Without it, the intended categorical
   implication would again be implicit.
2. Retain the full verification that `J: Rec -> Pfn` satisfies the
   lifting theorem. Do not cite numerical inseparability as an independent
   input in place of that theorem application.
3. Retain the proof carrier, its conclusion map and range, and both
   finite-computation inequalities. Consistency must imply disjointness,
   and hypothetical completeness must imply the coverage equation on
   the sentence object. Without these data, the incompleteness
   application is unproved.
4. Correct the abstract to agree with the actual dependency of the
   arithmetic proof. Do not replace J with F_T in the argument without
   constructing and proving the additional effective comparison.

## (F) Not checked / uncertainty log

This review does not re-audit the three-point construction, the
appendices, historical novelty, or all cited literature. It did read the
local-connectedness theorem and its proof, but its principal independent
check is the passage from its classical instance to arithmetic
incompleteness. No Lean verification was performed. The fixed acceptable
programming system and PA verification of its trace, composition and
parameterization operations are explicitly stipulated background; their
implementation was not independently formalized.

Strongest confirmed blocker: the abstract's dependency claim needs
revision; no blocker is confirmed in the current mathematical chain.
Strongest suspected but unconfirmed blocker: none identified in this
scope. Most important unchecked material: the other application and its
appendices. No conclusion in this focused check depends on unavailable
private notes. Final recommendation: **unknown as a publication decision;
the current categorical implication is proved, subject to the explicit
programming-system assumptions, and its abstract must describe it
accurately**.
