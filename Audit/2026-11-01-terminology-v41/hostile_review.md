## (A) Kill-shots / hard blockers

None found in the changed passages examined.

## (B) Major weaknesses

None found in the changed passages examined.

## (C) Minor issues

No must-fix local typing, scope, or equivalence defect was found in the installed wording. The changes consistently distinguish a restriction idempotent from an ordinary partial function's set of defined inputs and from an explicit monic input subobject.

## (D) Cross-section consistency failures

None found in the checked changes.

- **Abstract and introduction, Miller extension class:** the new wording has the quantifier order “for every consistent extension, if there exists a single oracle program that semidecides its axiom set using every binary representation as oracle, then the extension is incomplete.” The program can depend on the extension, and the same program must work for all representations. This is equivalent to the earlier one-program/every-representation condition; it does not replace it by one potentially different program for each representation.
- **Introduction, categorical setting:** `R` is a recursion category; `S` is its completion by splitting restriction idempotents; `D` has all objects of `S` and precisely the morphisms whose restriction idempotents equal the source identities. The introduction names the restriction idempotent completion at the first use of `S=Split(R)` and the category of total morphisms at the first use of `D=Tot(S)`. The later formulas for `B_T` and `D_a` use these already defined operations. The partial-function analogy distinguishes a partial identity from the subset through which it splits. The first introductory paragraph is byte-for-byte unchanged.
- **Introduction, theory and comparison descriptions:** theorem/refutation and diagonal pairs are now called restriction idempotents. Their order, meet, inverse-image and join operations still have the same types. No new set interpretation of an arbitrary restriction category is asserted. The image/range identification retains its partial-inverse hypothesis.
- **§2, definitions and historical terminology:** the total-morphism category is named and explicitly retains all objects of the restriction category. The restriction idempotent completion is named when its notation is introduced; its object, morphism, and identity equations are unchanged. The short note distinguishes the manuscript's terminology from the earlier use of “domain.” The Cockett–Lack §2.1.1 and Heller §5 terminology was checked directly in the cached primary texts; those passages support the note.
- **§3, comparison overview:** source and target data remain pairs of restriction idempotents. Inverse images of the target pair under the interpreted total source morphism are restriction idempotents in the target; saying both are zero matches Theorem 3.1. This does not assume splitness of the target.
- **§8, initiality proof:** evaluation terminates on every input in the two displayed source objects. Calling the resulting evaluation morphisms total is equivalent to the earlier assertion that their defined-input sets are exactly those source carriers. The retained representation-independent domains and values refer to the numerical partial functions.
- **§6 and §§7.1, 7.4–7.5:** inverse images preserve joins of restriction idempotents; in the numerical partial-function realization those joins are partial identities on unions of c.e. subsets. The statement about the function on `D_e` distinguishes its defined-input set from the equation `bar f=e`, and the separate equation `f=dfe` ensures target membership. The renamed arithmetic lemma and comparison conclusion preserve their mathematical content.
- **§9, complementary pair:** `c,c'` belong to `R_X`, while their splittings through the inclusions `m:C→V` and `m':C'→V` are explicitly taken in `A=Par(E,Mono)`. This does not assert that `R_X` is split. The component carriers are c.e. subsets; the inverse of the copairing is computed by their parallel membership searches. The resulting total conditional on `V` belongs to `R_X` by its established fullness. The later refutation component is correctly a partial identity on the indicated inverse-image set.
- **Version metadata:** the preamble change is confined to the version number.

## (E) Acceptance conditions, non-negotiable

No additional mathematical correction is required by this scoped review. The changed paragraphs preserve the hypotheses and categorical versus set-theoretic distinctions checked above.

## (F) Not checked / uncertainty log

Scope: all changed passages in the eleven TeX files below were compared with frozen version 40 and checked in their relevant local contexts. This is a terminology and local mathematical-typing review, not a fresh proof audit of the whole paper. Compilation and rendered-page checks were not performed by this reviewer.

| Changed source | SHA-256 |
| --- | --- |
| `abstract.tex` | `fb8d0a45696f2e196ca68783672b9940bdb7a278e5f670fab85d6aa76bc1ac3d` |
| `preamble.tex` | `1fa38b5ed11f9964b7093972a9c9798f81ce4f8eadc529db12f801da232b8faf` |
| `sections/01-introduction.tex` | `caff1941a920e17d77edc6b2d75bdfe468be7905955bc20173885a52d93d78d6` |
| `sections/02-categorical-preliminaries.tex` | `b63a65aa953669be4444610d2048b111f9c27ce10344cbae84bdd353acec8fdb` |
| `sections/03-sections-and-inseparability.tex` | `26175f2da0198a7710748e57083aa7490f0f1295fb5ebd5dfbc457ae8a5caae2` |
| `sections/04-miller-sequences.tex` | `9e24d7332b4c6cff89ca74b1c8c8cbb0b559bccd305e7142141c2c70aa6b9b83` |
| `sections/06-interpretation-in-models.tex` | `57be993cc95e618b0bf7ba9b9da652173145b4a64015717a349dbbc18e5bf122` |
| `sections/08-essential-incompleteness-of-arithmetic.tex` | `abf8ed7a20fb312bcc5e15ac3734f6943404d5fd99ff40ba654812bf6fe352e3` |
| `sections/08c-numerical-realization.tex` | `861e34e3a588c9e07ae1b6fbb622d6ff4568d22a6db9fcacd988f572445f4188` |
| `sections/08d-numerical-incompleteness.tex` | `1c50baab15f666707d5bda718abc6d2787b2427b098c52a3d42294d37457a6fc` |
| `sections/09-three-point-space.tex` | `7ab696ccfae2653c23abf16e6f4875cbefb44acbf983896bed72b6e2c6203bfb` |

The final named definitions of `Split` and `Tot` in the introduction and §2.1 were reread after the user clarified that defined notation should be retained; their types and antecedents agree. The first introductory paragraph was compared directly and found unchanged. The final local wording “Without the lifting hypothesis, this pair can be separable” was checked against its immediate antecedent, the pair of restriction idempotents determined by a source Turing morphism; it preserves the Appendix C comparison. Direct primary-text consultation in this pass was limited to the Cockett–Lack and Heller terminology supporting the short historical note; other citations were not newly audited.

Strongest confirmed blocker: none within this scope. Strongest suspected unconfirmed blocker: none within this scope. Most important unchecked material: a full re-audit of the unchanged body proofs. The scoped conclusion does not depend on unavailable material. Final recommendation on the whole manuscript: **unknown**; no concrete mathematical or typing objection remains in the changed passages on the evidence examined.
