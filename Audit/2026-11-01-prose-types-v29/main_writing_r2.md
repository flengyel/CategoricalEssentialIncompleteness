# Mathematical-writing recheck of the version 29 repairs

The repairs close the findings from `main_writing_r1.md`. No further correction is required within this recheck's scope.

## Scope

Read `tmp/review29/main_repairs.diff` and the corresponding current passages in `output/manuscript/local_connectedness`. This recheck applies the KLR source principles already consulted for the first report. It does not reopen unchanged sections or propose additional polish.

## Closure

| First-round finding | Current repair | Status |
|---|---|---|
| Proposition C.1 did not identify its separated pair in its statement. | The statement quantifies `tau_K:N x N -> N` as a partial Turing morphism and `b:N -> N+N` as an isomorphism, and displays both restriction idempotents before asserting separability. | Closed. The pair and quantifiers no longer depend on discovering them in the proof. |
| The introduction's roadmap placed the incompleteness corollary in Section 3 and used a “Sections 6–D” interval. | The roadmap follows the manuscript's actual order, distinguishes Sections 3 and 4, and names the faithful model family among the appendices. | Closed. |
| Appendix D attributed a source conditional hypothesis to the interpretation functor and described it indirectly through target images. | Corollary D.2 starts with the quantified theory. Its proof gives the typed source morphism `ell_c:U -> U+U` and both branch equations, then states the target join law and nonzero-identity hypothesis separately. | Closed. |
| The endpoint application used unexplained “switching sections.” | It refers to the existing numerical construction, gives `ell_c:W -> W+W` and both branch equations, and uses fullness to obtain the morphism in `K_2`. The referenced numerical subsection has the added label. | Closed without duplicating the numerical search proof. |
| Categorical inseparability was called “recursive inseparability” before the numerical application. | The opening now says “inseparability of restriction idempotents.” | Closed. |
| “Range agreement” differed from the earlier name of the law. | The proof says “the agreement law for ranges.” | Closed. |
| The tag-exchange description could suggest an already tagged input object. | The preview now describes agreement with coproduct injections on complementary source domains. | Closed. The displayed equations remain the exact mathematical condition. |

The removal of splitness, local connectedness, and weak choice from the Appendix C proof's target-property paragraph preserves the proposition's stated claims: the remaining paragraph verifies precisely the preservation, zero-reflection, nonzero-identity, and total inverse-image properties asserted there.

## Limits of this recheck

No source edits were made. No compilation or rendered-page inspection was performed by this agent. No independent verification of external literature or of unchanged mathematical claims is asserted. No new theorem-blocking defect was found in the inspected repairs.
