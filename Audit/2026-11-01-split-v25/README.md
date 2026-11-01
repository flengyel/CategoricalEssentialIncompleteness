# Reviews of the separated arithmetic subsections

Version 25 separates the former §7.2 into two subsections with distinct mathematical purposes:

- **§7.2, An indexed family of arithmetic theories:** construct the family, prove its numeral-fiber comparison in Proposition 7.5, and give the arithmetic predicate representing the family image.
- **§7.3, Uniform independent sentences:** use that family and predicate to prove Theorem 7.6.

The theorem statement and proof explicitly refer to the objects and predicate imported from §7.2. Theorem numbers and mathematical content are preserved. Later subsections are now §7.4, The numerical realization, and §7.5, Numeral instances and theory extension.

Three independent agents reviewed the split text and then the corrected final snapshot. The first round identified one local terminology issue: `Prov(e,z)` is a provability predicate because the derivation code is existentially quantified. That phrase was corrected. All three second-round reports give a scoped PASS, with no unresolved concrete finding.

| Review | First round | Final review |
| --- | --- | --- |
| Hostile referee | [Round 1](hostile_r1.md) | [Round 2: PASS](hostile_r2.md) |
| Mathematical Writing | [Round 1](writing_r1.md) | [Round 2: PASS](writing_r2.md) |
| Explicit types and dependencies | [Round 1](types_r1.md) | [Round 2: PASS](types_r2.md) |

The reviews distinguish categorical constructions from their numerical and semantic applications. Objects and morphisms in the total restriction splitting, its slices, and its algebra categories remain separately typed from external indices, formulas, sentence codes, sets, and models. The general constructions of Appendix A remain used by reference.

The review procedure is to correct concrete findings and rerun the hostile-referee and Mathematical Writing checks on the resulting text until no finding remains unresolved before proceeding to Lean formalization. This review has reached that local endpoint for §§7.2–7.3. It is not a whole-paper certification or a successful Lean formalization.

- [Changes and dependencies](resolution.md)
- [Build and artifact verification](verification.md)

The abstract, introduction, and modular Appendix A are unchanged. The standalone appendix is re-exported with the matching version number. No Lean source was changed.
