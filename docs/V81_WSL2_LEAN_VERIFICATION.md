# WSL2 Lean verification of manuscript v81

The clean proof source `73c2e4fa2bc633a3af012b1c4f85a7882018f962` adds the numerical membership claim in the proof of Proposition 8.8 to the 77 numbered results and their supporting declarations. All 39 targeted commands passed. The official serial full replay was in progress when this report was issued. [Proof source](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/73c2e4fa2bc633a3af012b1c4f85a7882018f962) · [Targeted command and axiom receipt](reviews/V81_WSL2_AUDITS/tested-73c2e4f/targeted.json.gz) · [Active correspondence](../FORMALIZATION_STATUS_V81.md)

## Proposition 8.8

For every finite arity bound and recursive unary function-symbol and relation-symbol supports through that bound, Lean constructs a total decision procedure on every natural-number input for each of the two word predicates. The finite-signature check obtains a Boolean decision program for terms and another for formulas, under exactly the printed support assumptions. Both the polynomial induction and the specialization to the actual numerical objects depend only on `propext`, `Classical.choice` and `Quot.sound`. [Printed proof](../manuscript/latex/sections/08c-numerical-realization.tex#L292) · [Recursive membership](../Lean/CategoricalEssentialIncompleteness/V46NumericalSyntaxMembership.lean) · [Two decision programs](../Lean/CategoricalEssentialIncompleteness/V46NumericalSyntaxMembershipChecks.lean)

The targeted run compiled both new modules, the twelve Cockett–Hofstra modules, the Wißmann factorization declaration and its independent check, and the two named checks for Theorem 4.7 and Corollary 8.10. It then checked 35,094 transitive axiom entries across 1,174 production modules. The six parser tests passed and the manuscript PDF copies and source archive matched the v81 manifest. [Command-by-command receipt](reviews/V81_WSL2_AUDITS/tested-73c2e4f/targeted.json.gz)

## Manuscript findings

The six outstanding §1 historical conclusions are Heller 9.2, Lengyel 21 and corrected 26, van Dijk–Gietelink Oldenziel 5.19 and 5.20, and Bauer–Hanson 6.4. The two directions of Cockett–Hofstra 4.9 have checked proofs at their cited types. The supplied v82 TeX patch covers the abstract, the nonzero identity in §1, the source page before Corollary 8.4, effective extensibility in §8.3, and the two meanings of the letter in Appendix C. The active manuscript selects v81. [Remaining original inferences](reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md) · [Manuscript return and five proposed passages](reviews/V81_MANUSCRIPT_RETURN/README.md)

## Earlier verification

The v81 full replay at `830d03a5adcf144a003feb36f88bd06e0c5b0cf5` passed all 2,073 commands. At `98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885` the wrapper exited 1 because its final scan matched an English verb in a docstring. All 2,087 subprocesses in that run passed. The full replay of `6775f0b3a5fb668f9390b21440f3f6c57bc65930` stopped during command 14 after the same docstring was confirmed in its sources. Its 31 targeted commands passed. [Completed v81 replay](V81_WSL2_LEAN_VERIFICATION_830d03a.md) · [Failed wrapper and original JSON](V81_WSL2_LEAN_VERIFICATION_98f8d0d.md) · [Interrupted replay](reviews/V81_WSL2_AUDITS/tested-6775f0b/superseded-run.json)
