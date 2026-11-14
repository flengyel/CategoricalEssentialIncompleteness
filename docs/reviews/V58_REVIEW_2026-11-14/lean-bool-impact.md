# Lean impact of the Boolean clarifications in v58

Compared against live repository commit `df66b19853e6b243170725619bfabb71f4741065`, `flengyel/CategoricalEssentialIncompleteness`. Each Lean file used below was fetched at that exact commit. Its returned blob SHA was checked against the recursive Git tree for the same commit. The files and SHAs are recorded in `lean-bool-source-manifest.json`; the source is retrievable at the pinned commit.

## Conclusion

**Neither Boolean clarification requires a Lean code change or a changed theorem statement.** The existing implementation already assigns true to the second coproduct injection and already interprets nullary-language universal quantification by the second projection. An existing statement-check module explicitly checks both the equality value and the quantifier equation. This is a source-level impact determination; no fresh Lean build or axiom audit was run in this task.

## Appendix B: truth is the second summand

The v58 manuscript replaces the local first-summand equality convention with the Appendix A convention: equality is the inverse image of `t:1→Two`, and the proof of B.10 now calls it the second summand.

| Actual Lean declaration | Exact source | Evidence |
|---|---|---|
| `CategoricalEssentialIncompleteness.Two.point` | `Lean/CategoricalEssentialIncompleteness/CharacteristicArrows.lean:40` | `false => coprod.inl`; `true => coprod.inr` on lines 41–42. |
| `CategoricalEssentialIncompleteness.LocalConnectedness.Fork.EqualityDecision` | `Lean/CategoricalEssentialIncompleteness/ForkObstruction.lean:35` | `center_eq`, `left_eq`, and `right_eq` on lines 41–43 require the decision to equal `true` exactly for equal elements. |
| `CategoricalEssentialIncompleteness.LocalConnectedness.Fork.EqualityDecision.leftMap_injective` | `Lean/CategoricalEssentialIncompleteness/ForkObstruction.lean:45` | Naturality and the true-fiber equality conditions imply injectivity of the first endpoint map. |
| `CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.universal_no_decidable_equality` | `Lean/CategoricalEssentialIncompleteness/EffectiveForkUniversal.lean:100` | Applies that injectivity theorem to the codes of `(0,0,0,0)` and `(0,1,0,0)` and derives `0=1`. |
| `CategoricalEssentialIncompleteness.LocalConnectedness.fork_not_restriction_equivalent` | `Lean/CategoricalEssentialIncompleteness/ForkNonEquivalence.lean:26` | Independently proves the other B.10 assertion from the terminal-support cardinalities. |

The Lean equality obstruction is formulated for all set-valued natural decisions on the coded fork, so it excludes computable internal decisions in particular. This strengthening already existed before the manuscript correction; v58 does not strengthen or weaken the requested statement. The connection between the coproduct convention and the `Bool` decision convention is explicit in `Two.point`.

## Corollary 4.8: universal quantification is the second projection

The revised proof specifies the operation `pi_2:V×Two→Two` rather than giving only its source and target.

| Actual Lean declaration | Exact source | Evidence |
|---|---|---|
| `CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.algebra` | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanValuation.lean:34` | The term carrier is terminal and formula carrier is `Two`; equality uses the constant `true` on line 40, and the final quantifier summand is `prod.snd` on line 43. |
| `CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.equality_value` | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanValuation.lean:50` | Proves `S.equalityConstructor ≫ valuation S d = Two.constant ... true`. |
| `CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.quantifier_value` | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanValuation.lean:90` | Proves `S.quantifierConstructor ≫ valuation S d = prod.snd ≫ valuation S d`. |
| Existing statement checks | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanValuationChecks.lean:25` and `:29` | The equality-value and exact quantifier-value equations are both checked by examples using the named theorems. Lines 32–37 list their axiom-print commands. |
| `CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.rule_value` | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanTheoryClosure.lean:55` | The generalization branch rewrites by `quantifier_value`, so closure uses the projection equation in its proof. |
| `CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation.sentenceTheory` | `Lean/CategoricalEssentialIncompleteness/V46NullaryBooleanSentenceTheory.lean:31` | The sentence theory is the `true` fiber; `refutation_fiber` at line 38 identifies the false fiber. |
| `CategoricalEssentialIncompleteness.V46.SignedFirstOrder.booleanTheory_consistent` and `.booleanTheory_complete` | `Lean/CategoricalEssentialIncompleteness/V46SignedBooleanExtension.lean:35` and `:39` | These use the constructed valuation to prove consistency and completeness. |
| `CategoricalEssentialIncompleteness.V46.SignedFirstOrder.essential_incomplete_iff_inseparable` | `Lean/CategoricalEssentialIncompleteness/V46SignedFirstOrderIncompleteness.lean:29` | The requested Corollary 4.8 equivalence is stated with the complete nullary presentation, consistency hypothesis, and restriction-subobject comparison. |

The code implements the projection rather than assuming an unspecified quantifier operation. The Boolean-valuation constructor has exactly the nullary-language scope used by the manuscript; it does not silently claim quantifier erasure for arbitrary first-order interpretations.

## Documentation

No new Lean definition, theorem, or statement check is required for these two edits. Preserve the existing declaration names and the current true/false convention. The active manuscript metadata and correspondence table already identify v58. A fresh build and axiom check, if required by the release workflow, remains a separate verification step; this report does not claim it was run.

One adjacent documentation detail remains outside these mathematical corrections: comments in `ForkObstruction.lean` and `ForkNonEquivalence.lean` still refer to an older “Proposition A.9” numbering. Those comments may be synchronized to current B.10, but they do not change the statements or proofs and are not needed to make v58's Boolean conventions correct.
