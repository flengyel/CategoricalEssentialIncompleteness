/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Unions
import PCats.Ranges
import PCats.NCoproducts

/-!
# Ranges of countable copairings are stable unions

Heller's proposition that the range operation preserves countable coproducts,
in the form the manuscript's remark on `rPΣ`-categories records:
`ran [qₙ] = ⋁ ran qₙ`.

The two halves need different hypotheses, and the split is the point of
separating `IsUnion` from `IsStableUnion` in `PCats.Unions`.

* `ran_ncopair_isUnion` needs ranges and an `ℕ`-ary coproduct only. Each
  `ran qₙ` lies below `ran [qₙ]` because `qₙ = ιₙ [qₙ]`, and the joint
  clause reduces along the injections to the range clause for each `qₙ`.
* `ran_ncopair_isStableUnion` needs `IsRP` and `CountablyDistributive`.
  Stability is the statement for `1_W ⊠ -`, and identifying the range of the
  transformed copairing uses `nearProd_id_ncopair` together with
  `HasRanges.ran_comp_of_section`, with `undistribL` supplied explicitly as
  the section of `δ^L`. No inverse is selected, so `Classical.choice` does
  not enter.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct NCoprodStruct HasNCoproducts

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [HasRanges C] [NCoprodStruct C] [HasNCoproducts C]

namespace HasRanges

/-- `ran [qₙ]` is a union of the `ran qₙ`. -/
theorem ran_ncopair_isUnion {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    DomSemilattice.IsUnion
      (⟨ran (ncopair q), rst_ran _⟩ : DomSemilattice Q)
      fun n => (⟨ran (q n), rst_ran _⟩ : DomSemilattice Q) := by
  constructor
  · intro n
    change ran (q n) ≫ ran (ncopair q) = ran (q n)
    rw [← ninj_ncopair q n]
    exact ran_comp_le _ _
  · intro R β β' h
    change ran (ncopair q) ≫ β = ran (ncopair q) ≫ β'
    apply ran_uniq
    apply hom_ext
    intro n
    have hn : q n ≫ β = q n ≫ β' := by
      calc q n ≫ β = (q n ≫ ran (q n)) ≫ β := by rw [comp_ran]
        _ = q n ≫ ran (q n) ≫ β := Category.assoc _ _ _
        _ = q n ≫ ran (q n) ≫ β' := by rw [h n]
        _ = (q n ≫ ran (q n)) ≫ β' := (Category.assoc _ _ _).symm
        _ = q n ≫ β' := by rw [comp_ran]
    rw [← Category.assoc, ninj_ncopair, ← Category.assoc, ninj_ncopair]
    exact hn

/-- The union is stable. -/
theorem ran_ncopair_isStableUnion [IsRP C] [CountablyDistributive C]
    {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    DomSemilattice.IsStableUnion
      (⟨ran (ncopair q), rst_ran _⟩ : DomSemilattice Q)
      fun n => (⟨ran (q n), rst_ran _⟩ : DomSemilattice Q) := by
  constructor
  · exact ran_ncopair_isUnion q
  · intro W
    have hbase := ran_ncopair_isUnion fun n => nearProd_map (𝟙 W) (q n)
    have hcomp :
        (fun n => (⟨ran (nearProd_map (𝟙 W) (q n)), rst_ran _⟩ :
            DomSemilattice (nearProd W Q)))
          = fun n =>
            (⟨ran (q n), rst_ran _⟩ : DomSemilattice Q).leftTimes W := by
      funext n
      apply DomSemilattice.ext'
      change ran (nearProd_map (𝟙 W) (q n)) = nearProd_map (𝟙 W) (ran (q n))
      rw [IsRP.ran_nearProd_map, ran_id]
    have htot :
        (⟨ran (ncopair fun n => nearProd_map (𝟙 W) (q n)), rst_ran _⟩ :
            DomSemilattice (nearProd W Q))
          = (⟨ran (ncopair q), rst_ran _⟩ : DomSemilattice Q).leftTimes W := by
      apply DomSemilattice.ext'
      change ran (ncopair fun n => nearProd_map (𝟙 W) (q n))
        = nearProd_map (𝟙 W) (ran (ncopair q))
      rw [← ran_comp_of_section (CountablyDistributive.distribL W U)
            (CountablyDistributive.undistribL W U)
            (CountablyDistributive.undistribL_distribL W U),
        ← CountablyDistributive.nearProd_id_ncopair,
        IsRP.ran_nearProd_map, ran_id]
    rw [← hcomp, ← htot]
    exact hbase

end HasRanges

end CategoryTheory
