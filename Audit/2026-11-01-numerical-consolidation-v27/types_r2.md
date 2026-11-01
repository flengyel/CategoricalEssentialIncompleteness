# Numerical-foundation consolidation: dependency and type review, round 2

I checked only the repairs identified in `types_r1.md` and repeated the two exact preservation comparisons affected by the consolidation.

All identified repairs are present:

- §9 declares objects as `C=(m,C_0)` before using the carrier notation `|C|=C_0`. The abbreviation by a subset is restricted to c.e. subsets, and membership, subset, image and elementwise expressions are explicitly carrier expressions.
- A c.e. subfunctor is defined by typed component objects, component carrier inclusions and the restricted component morphisms. The inclusions form the stated natural transformation.
- The dimension `m(A)` is the first coordinate of the fixed object `A=(m,A_0)`, including when the carrier is empty.
- The evaluation-functor subsection cites `prop:numerical-structure` for the construction of `Q_num`.

The numerical first-order proof and arithmetic code-comparison tail, beginning at `Choose the variable object V=(1,N)`, remain byte-equivalent to the version-26 tail. The fork-specific regularity, descent-naturality, finite-probe and extensivity block remains unchanged.

No dependency or type issue remains from this scoped review. No manuscript edits, new whole-paper review, compilation claim or Lean verification is asserted by this report.
