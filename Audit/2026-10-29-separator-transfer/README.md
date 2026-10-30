# The existing S_T construction and separator transfer

This review starts from the valid unprimed syntactic categories S_T for
consistent c.e. extensions T of PA. It retains their uniform proof quotient
and chosen Turing morphism. It excludes the invalid pointwise quotients S'_T.

The extension functor has direction Q_(T,T'):S_T→S_T'. Its preservation of
identity and zero makes the corresponding sets of program representatives
I_T,Z_T increase under extension. A fixed primitive recursive compiler sends
the ordinary inseparable diagonal pair into I_PA,Z_PA. Consistency keeps
the enlarged pairs disjoint, while completeness would decide I_T by
searching for its defining equality or the negation of that equality.
Separators therefore pull back in the required direction.

This calculation uses the effective presentations of the actual categories.
It constructs no functor on all arrows S_T→Rec. The additional domain
observation E_T([D])={n:T proves D(numeral n)} is well-defined and monotone,
but binary-join preservation is not assumed. External consistency and
external proof-search totality remain distinct from their internal proofs.

- [Construction review and proofs](CONSTRUCTION_REVIEW.md).
- [Primary-source check and reconstructed categorical laws](SYNTACTIC_SOURCE_CHECK.md).
- [Author-side hostile mathematical audit](HOSTILE_REVIEW.md).
- [Mathematical-writing review](WRITING_REVIEW.md); its access limitation
  concerning the governing writing source is recorded there.
- [Verification and scope](VERIFICATION.md).
- [Other theories and precomplete equivalence relations](OTHER_THEORIES.md)
  gives the interpretation construction S_(T,theta)=S_(T^theta), applications
  to ACA_0, finite set theory and HA, and the related inseparable-class
  argument for c.e. lambda theories. See its
  [mathematical audit](OTHER_THEORIES_HOSTILE_REVIEW.md),
  [writing review](OTHER_THEORIES_WRITING_REVIEW.md), and
  [verification record](OTHER_THEORIES_VERIFICATION.md).

For the PA benchmark, the actual quotient functors, fixed compiler,
observation domains, and their consistency/completeness implications are
established. No range completion, finite-stage union, or new syntax algebra
is needed for this benchmark. The general nonnumerical construction of
parameterized computational proof observations remains open. It is a question
about extending the scope: existence of the compatible presentation is
sufficient for the theories already covered, and need not follow from every
recursion category. The established three-point computational cosheaf
category remains a test for further nonnumerical instances, with selected
computational domains. The earlier conditional results remain unchanged.
