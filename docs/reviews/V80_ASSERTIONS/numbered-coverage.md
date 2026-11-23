# Named environments at v80

I traversed all 25 TeX files recursively from `manuscript/latex/main.tex` using the source blobs in commit `d80a23b07406dc0e44b010a7d78f2318980b6046`. For each theorem-like or proof environment I compared the inclusive source interval with the union of the TeX line ranges in the first column of the six dossiers. The 22 content files have dossier ranges. The three other inputs are the driver, preamble and bibliography. Duplicate or overlapping rows count once. The checker ignored blank lines and isolated begin/end or label commands when testing mathematical content.

| Environment | Count | With at least one matching row |
|---|---:|---:|
| Theorem | 18 | 18 |
| Lemma | 19 | 19 |
| Proposition | 27 | 27 |
| Corollary | 13 | 13 |
| Definition | 3 | 3 |
| Proof | 77 | 77 |
| Total | 157 | 157 |

All 80 statement/definition opening lines are covered. Of the 77 proof opening lines, 76 are covered literally. The exception is the bare proof marker at `03-sections-and-inseparability.tex:48`; the proof's first substantive line at 49 has its own row. Thirty environment intervals contain a physical line outside the six dossiers' first-column ranges. In 24 of these intervals only whitespace or structural markers fall outside. In six intervals the following nine substantive source lines are missing from the literal ranges. The rows below supply their content and evidence. Basenames in the TeX column are relative to `manuscript/latex/sections/`; Lean basenames are relative to `Lean/CategoricalEssentialIncompleteness/`.

| TeX file and missing lines | Assertion and source match |
|---|---|
| `05a-internal-syntax.tex:311` | The induction constructs the finite vector of witnesses for all entries. `V46FiniteSigmaOne.lean:69–99,146–156` gives the witness vector and applies it to the bounded formula, including nonstandard list lengths. This supplements the 280–310 range; it leaves the separately reported selector issue unchanged. |
| `08-essential-incompleteness-of-arithmetic.tex:161–162` | The bracket denotes the partial identity on the truth set in the particular model, for either sign. `PartialFunctions.lean:34,121–124` defines the partial identity and set idempotent; the two exact truth sets occur on the respective sides of `V46NamedArithmeticProofSearchPrinted.lean:67–93`. |
| `08c-numerical-realization.tex:174` | The domain of the partial inverse is the coded image **in the codomain** $Q(C)$. `V46NumericalTuplesStructure.lean:69–88` constructs the inverse in the indicated direction and proves both identities; its restriction is precisely the composite with the included mono. |
| `08-essential-incompleteness-of-arithmetic.tex:441–442` | Applying the signed-theory equivalence to the diagonal pair and the just-proved consistency gives essential incompleteness of the generated signed theory. `V46ArithmeticSignedEssential.lean:59`, `V46ArithmeticSignedTotal.lean:151`, `V46ArithmeticSignedTheory.lean:32`; the general implication is `V46SignedFirstOrderIncompleteness.lean:29–39`. |
| `08-essential-incompleteness-of-arithmetic.tex:478` | The original functor is faithful, sends each $f$ to the constant family of $f$ and carries the evaluator to the claimed evaluator with the product comparison. `V46ArithmeticAssociatedStructure.lean:175–202` states faithfulness, the underlying value and the evaluator comparison. |
| `08-essential-incompleteness-of-arithmetic.tex:516–517` | The final invocation supplies the conclusions about the slice-extension functors and closed theories. `V46ArithmeticAssociatedCategories.lean:98–127` instantiates the arithmetic result. Compare `V46PartialSliceChangeBase.lean:75,95` and `V46AssociatedIncompleteness.lean:57–73` for the general assertions. |

Together the six dossiers and these rows assign a source range to every substantive line **inside the 157 named environments**. This is a line-location check. It does not establish that an assertion is true, that its cited declaration matches its stated hypotheses, that a cited proof replayed, or that prose outside the environments has been exhaustively reconciled.
