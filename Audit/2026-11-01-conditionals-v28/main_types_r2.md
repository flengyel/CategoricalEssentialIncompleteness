# Version 28: application types and dependencies, closure

The three local findings in `main_types_r1.md` are resolved in the inspected source:

1. Appendix C's opening now identifies `thm:comparison`, which has the existence-of-lift premise.
2. Proposition `prop:missing-lift` explicitly states that `F` is a faithful range functor, as its proof establishes.
3. The introduction now says that disjoint-domain joins supply complementary conditionals. It does not claim they lift an arbitrary target morphism of the comparison theorem.

The Miller branch construction explicitly types the two complementary restriction idempotents in the source category `E_a`. The introduction states the required preservation of joins by **total** inverse images. The opening of §3 describes complementary conditionals as an inseparability criterion without claiming that every arithmetic comparison uses this form of lift.

No outstanding mathematical, typing, orientation or dependency finding remains within this source review's scope. The new corollary uses the comparison theorem and range agreement without a local-connectedness hypothesis. The source conditionals in the syntactic, numerical, Miller, cosheaf and endpoint applications match it. Nonzeroness and target join preservation remain explicit. Appendix C's `P=F(1_A)`, `N=F(1_{A^c})` orientation is correct.

The exact source-preservation checks are recorded in the first report: the first-order, family, numerical code-comparison, soundness and ultrapower arguments, as well as the cosheaf theory/observation arguments, remain unchanged. The retained local-connectedness properties of the concrete categories have not been used as missing premises of the revised logical arguments.

This closes the source-level application review. It does not establish compilation or rendering, certify every theorem in the paper, assess the separate note, or verify Lean code. No manuscript files were edited by this reviewer.
