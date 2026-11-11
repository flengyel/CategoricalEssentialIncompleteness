/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.PCat

/-!
# The erratum to Lemma 24 and Claim 25

Lemma A and Corollary B of the erratum to *More existence theorems for recursion
categories*, APAL 125 (2004) 1–41, correcting the proof of Lemma 24 at the
passage from p. 23 to p. 24 and the proof of Claim 25 on pp. 24–25.

Two points are corrected there: a suppressed associator, and two auxiliary
diagrams containing the triangle `X ⊠ X --p₁--> X --Δ--> X ⊠ X` with hypotenuse
labelled `1`, which does not commute.

The first point is settled by type-checking alone. Under Heller's left-bracketed
convention `(Δ ⊠ 1) ≫ (1 ⊠ p₁)` is not a composable pair — `Δ ⊠ 1` lands in
`(X ⊠ X) ⊠ X` and `1 ⊠ p₁` starts from `X ⊠ (X ⊠ X)` — so the reading on which
the associator is a matter of notation is not available here.

The identities are stated and proved in the whole `P`-category. In the corrected
proof of Claim 25 they are applied to total morphisms, hence in `C_T`. The
component comparison used below is `eq_partialPairing_of_proj`; only totality of
`Δ` is required.

Corollary B(i) is `PCategory.diag_assoc`, already proved in `PCats.PCat`, where
it is what makes `rst_comm'` go through.
-/

@[expose] public section

universe v u

namespace CategoryTheory

namespace Erratum

open PCategoryStruct PCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- Lemma A: `ass (Δ ⊠ 1) = ⟨p₀, 1⟩ : X ⊠ X ⟶ X ⊠ (X ⊠ X)`. -/
theorem assoc_diag_nearProd_id (X : C) :
    nearProd_map (diag X) (𝟙 X) ≫ assoc X X X
      = partialPairing (p0 X X) (𝟙 (nearProd X X)) := by
  have h0 : (nearProd_map (diag X) (𝟙 X) ≫ assoc X X X) ≫ p0 X (nearProd X X)
      = p0 X X := by
    rw [Category.assoc, assoc_p0, ← Category.assoc, p0_nat, Category.assoc,
      diag_p0, Category.comp_id]
  have h1 : (nearProd_map (diag X) (𝟙 X) ≫ assoc X X X) ≫ p1 X (nearProd X X)
      = 𝟙 (nearProd X X) := by
    rw [Category.assoc, assoc_p1, comp_partialPairing, ← Category.assoc, p0_nat,
      Category.assoc, diag_p1, Category.comp_id, p1_proj_domain_id,
      diag_isTotal, nearProd_id, Category.id_comp, partialPairing_p0_p1]
  exact eq_partialPairing_of_proj h0 h1

/-- Corollary B(i), typed coassociativity: `ass (Δ ⊠ 1) Δ = (1 ⊠ Δ) Δ`. -/
theorem coassoc (X : C) :
    partialPairing (diag X) (𝟙 X) ≫ assoc X X X = partialPairing (𝟙 X) (diag X) :=
  diag_assoc X

/-- Corollary B(ii): `(Δ ⊠ p₁) ass (Δ ⊠ 1) = Δ ⊠ 1`. -/
theorem diag_nearProd_p1_absorb (X : C) :
    nearProd_map (diag X) (𝟙 X) ≫ assoc X X X
        ≫ nearProd_map (diag X) (p1 X X)
      = nearProd_map (diag X) (𝟙 X) := by
  rw [← Category.assoc, assoc_diag_nearProd_id,
    partialPairing_comp_nearProd_map, Category.id_comp,
    nearProd_eq_partialPairing (diag X) (𝟙 X), Category.comp_id]

/-- Corollary B(iii): `(1 ⊠ p₁) ass (Δ ⊠ 1) = 1`. -/
theorem id_nearProd_p1_absorb (X : C) :
    nearProd_map (diag X) (𝟙 X) ≫ assoc X X X
        ≫ nearProd_map (𝟙 X) (p1 X X)
      = 𝟙 (nearProd X X) := by
  rw [← Category.assoc, assoc_diag_nearProd_id,
    partialPairing_comp_nearProd_map, Category.comp_id, Category.id_comp,
    partialPairing_p0_p1]

/-- Corollary B(iv): `(1 ⊠ p₁)(Δ ⊠ 1) = Δ ⊠ p₁`, by functoriality of `⊠`. -/
theorem nearProd_p1_factor (X : C) :
    nearProd_map (diag X) (𝟙 (nearProd X X))
        ≫ nearProd_map (𝟙 (nearProd X X)) (p1 X X)
      = nearProd_map (diag X) (p1 X X) :=
  nearProd_comp_id_id_comp (diag X) (p1 X X)

/-- The erratum's "corrected use", carrying an additional factor: for
`k : T ⟶ T'`, `(ass ⊠ 1)((Δ ⊠ 1) ⊠ k) = (ass (Δ ⊠ 1)) ⊠ k`. -/
theorem assoc_nearProd_right {T T' : C} (X : C) (k : T ⟶ T') :
    nearProd_map (nearProd_map (diag X) (𝟙 X)) k
        ≫ nearProd_map (assoc X X X) (𝟙 T')
      = nearProd_map (nearProd_map (diag X) (𝟙 X) ≫ assoc X X X) k := by
  rw [nearProd_comp, Category.comp_id]

end Erratum

end CategoryTheory
