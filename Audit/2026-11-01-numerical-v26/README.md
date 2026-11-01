# Numerical realization and incompleteness reviews

Version 26 revises Proposition 7.7 and separates the two mathematical purposes of the former numerical subsection:

- **§7.4, The numerical realization:** prove that the category of c.e. numerical carriers realizes Appendix A, construct its logical objects, and compare its proof codes with the standard interpretation of the syntactic construction.
- **§7.5, Numerical incompleteness:** obtain the numerical inseparable pair and apply the incompleteness criterion to the realized theorem and refutation domains.

The existing numeral-instance and theory-extension subsection is now §7.6. Proposition 7.7 retains its number and label.

The initial audit found omitted comparison functors, algebra structures, fold equations, and coding interfaces. The revised proof supplies them. Later reviews distinguished actual interpreted rule instances from the numerical labels stored in derivation trees. The final text gives both conversions and an inverse computable relabeling of valid proof trees preserving their conclusions.

All three final reports pass their stated local scope, with no concrete finding outstanding. Five snapshots record the initial review, substantive repairs, the scalar-label correction, and final wording closure. The general constructions and image theorem of Appendix A are used by reference. The appendix's mathematical source is unchanged.

| Review | Initial | Second | Third | Fourth | Final closure |
| --- | --- | --- | --- | --- | --- |
| Hostile referee | [1](hostile_r1.md) | [2](hostile_r2.md) | [3](hostile_r3.md) | [4](hostile_r4.md) | [5: PASS](hostile_r5.md) |
| Mathematical Writing | [1](writing_r1.md) | [2](writing_r2.md) | [3](writing_r3.md) | [4](writing_r4.md) | [5: PASS](writing_r5.md) |
| Explicit types and dependencies | [1](types_r1.md) | [2](types_r2.md) | [3](types_r3.md) | [4](types_r4.md) | [5: PASS](types_r5.md) |

- [Corrections and preserved dependencies](resolution.md)
- [Build and artifact verification](verification.md)

The abstract, introduction, Appendix A, and the previously reviewed §§7.2–7.3 are unchanged. No Lean source was changed or verified. The final disposition concerns the numerical subsections and their inspected dependencies, rather than the whole manuscript or completion of formalization.
