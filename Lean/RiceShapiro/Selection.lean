/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro.Approximation

/-!
# Selection data

Subsection "The extension-witness implication" of the manuscript:
extension-witness selection data, stage-indexed selection data, and the
implication from the second to the first.

Both notions need a pointed `P`-category, since clauses (F4) and (S3) state a
hypothesis `u_k r = 0`.

Two abbreviations follow the manuscript. `entry s k = rst (s k)` is the domain
on which the index family `k` enters `s`, written `u_k` there. Clauses (F2) and
(S1) say that the extension domain receives a particular pairing, which is
`ApproximationDatum.Extends`, so they are stated with it rather than repeated.

The morphisms `F_s(i,k)` and `G_s(i,k)` are `evalAt` at `⟨i, k⟩`, the same
operation used for `ε_i` and `α_a`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {X Y : C}

/-- `u_k = rst (s k)`, the domain on which `k` enters `s`. -/
def entry {I : C} (s : DomSemilattice I) {Z : C} (k : Z ⟶ I) : Z ⟶ Z :=
  rst (k ≫ s.hom)

lemma rst_entry {I : C} (s : DomSemilattice I) {Z : C} (k : Z ⟶ I) :
    rst (entry s k) = entry s k :=
  rst_rst _

/-- Restriction axiom R4 in the form used throughout: `u w = w u_k`. -/
lemma comp_entry {I Z W : C} (s : DomSemilattice I) (w : W ⟶ Z) (k : Z ⟶ I) :
    entry s (w ≫ k) ≫ w = w ≫ entry s k := by
  dsimp [entry]
  rw [Category.assoc]
  exact rst_comp' w (k ≫ s.hom)

namespace ApproximationDatum

variable [Limits.HasZeroMorphisms C] (𝒜 : ApproximationDatum X Y)

/-- An extension-witness selection datum for `s`, clauses (F1)–(F4). -/
structure WitnessSelection (s : DomSemilattice 𝒜.I) where
  /-- `ρ_s : I ⊠ I ⟶ A`. -/
  rho : nearProd 𝒜.I 𝒜.I ⟶ 𝒜.A
  /-- `F_s : (I ⊠ I) ⊠ X ⟶ Y`. -/
  F : nearProd (nearProd 𝒜.I 𝒜.I) X ⟶ Y
  /-- (F1) `rst (ρ_s(i,k)) = u_k`. -/
  f1 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    rst (partialPairing i k ≫ rho) = entry s k
  /-- (F2) the extension domain receives `⟨ρ_s(i,k), i u_k⟩`. -/
  f2 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    𝒜.Extends (partialPairing i k ≫ rho) (entry s k ≫ i)
  /-- (F3) `F_s(i,k)(u_k ⊠ 1) = α(ρ_s(i,k) ⊠ 1)`. -/
  f3 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    nearProd_map (entry s k) (𝟙 X) ≫ evalAt F (partialPairing i k)
      = evalAt 𝒜.approx (partialPairing i k ≫ rho)
  /-- (F4) off `u_k`, the family agrees with `ε_i`. -/
  f4 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    ∀ r : DomSemilattice Z, r.hom ≫ entry s k = 0 →
      nearProd_map r.hom (𝟙 X) ≫ evalAt F (partialPairing i k)
        = nearProd_map r.hom (𝟙 X) ≫ evalAt 𝒜.ev i

/-- A stage-indexed selection datum for `s`, clauses (S1)–(S3). -/
structure StageSelection (s : DomSemilattice 𝒜.I) where
  /-- The object of stages. -/
  N : C
  /-- The total stage-approximation morphism `d : I ⊠ N ⟶ A`. -/
  d : nearProd 𝒜.I N ⟶ 𝒜.A
  /-- `d` is total. -/
  d_total : rst d = 𝟙 (nearProd 𝒜.I N)
  /-- The stage selector `σ_s : I ⟶ N`. -/
  sigma : 𝒜.I ⟶ N
  /-- `rst σ_s = s`. -/
  rst_sigma : rst sigma = s.hom
  /-- `G_s : (I ⊠ I) ⊠ X ⟶ Y`. -/
  G : nearProd (nearProd 𝒜.I 𝒜.I) X ⟶ Y
  /-- (S1) the extension domain receives `⟨d_s(i,k), i u_k⟩`. -/
  s1 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    𝒜.Extends
      (partialPairing (entry s k ≫ i) (k ≫ sigma) ≫ d) (entry s k ≫ i)
  /-- (S2) `G_s(i,k)(u_k ⊠ 1) = α(d_s(i,k) ⊠ 1)`. -/
  s2 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    nearProd_map (entry s k) (𝟙 X) ≫ evalAt G (partialPairing i k)
      = evalAt 𝒜.approx (partialPairing (entry s k ≫ i) (k ≫ sigma) ≫ d)
  /-- (S3) off `u_k`, the family agrees with `ε_i`. -/
  s3 : ∀ {Z : C} (i k : Z ⟶ 𝒜.I), rst i = 𝟙 Z → rst k = 𝟙 Z →
    ∀ r : DomSemilattice Z, r.hom ≫ entry s k = 0 →
      nearProd_map r.hom (𝟙 X) ≫ evalAt G (partialPairing i k)
        = nearProd_map r.hom (𝟙 X) ≫ evalAt 𝒜.ev i

namespace StageSelection

variable {𝒜} {s : DomSemilattice 𝒜.I} (D : 𝒜.StageSelection s)

/-- The candidate `ρ_s = d⟨p₀u, σ_s p₁⟩`, with `u = rst (s p₁)`. -/
def rho : nearProd 𝒜.I 𝒜.I ⟶ 𝒜.A :=
  partialPairing
    (entry s (p1 𝒜.I 𝒜.I) ≫ p0 𝒜.I 𝒜.I) (p1 𝒜.I 𝒜.I ≫ D.sigma) ≫ D.d

/-- Reindexing: `ρ_s(i,k) = d_s(i,k)`. -/
lemma rho_apply {Z : C} (i k : Z ⟶ 𝒜.I) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    partialPairing i k ≫ D.rho
      = partialPairing (entry s k ≫ i) (k ≫ D.sigma) ≫ D.d := by
  have hp1 : partialPairing i k ≫ p1 𝒜.I 𝒜.I = k := by
    rw [p1_partialPairing, hi, Category.id_comp]
  have hp0 : partialPairing i k ≫ p0 𝒜.I 𝒜.I = i := by
    rw [p0_partialPairing, hk, Category.id_comp]
  have hu : partialPairing i k ≫ entry s (p1 𝒜.I 𝒜.I) = entry s k ≫ partialPairing i k := by
    have h := comp_entry s (partialPairing i k) (p1 𝒜.I 𝒜.I)
    rw [hp1] at h
    exact h.symm
  dsimp [rho]
  rw [← Category.assoc, comp_partialPairing]
  congr 2
  · rw [← Category.assoc, hu, Category.assoc, hp0]
  · rw [← Category.assoc, hp1]

/-- A stage-indexed selection datum yields an extension-witness selection
datum. -/
def toWitnessSelection : 𝒜.WitnessSelection s where
  rho := D.rho
  F := D.G
  f1 i k hi hk := by
    rw [D.rho_apply i k hi hk]
    have hd : rst (partialPairing (entry s k ≫ i) (k ≫ D.sigma) ≫ D.d)
        = rst (partialPairing (entry s k ≫ i) (k ≫ D.sigma)) :=
      rst_comp_of_isTotal' _ D.d_total
    have hi' : rst (entry s k ≫ i) = entry s k := by
      rw [rst_comp_of_isTotal' _ hi, rst_entry]
    have hk' : rst (k ≫ D.sigma) = entry s k := by
      dsimp [entry]
      rw [rst_comp_rst_right', D.rst_sigma]
    rw [hd, rst_partialPairing, hi', hk']
    exact RestrictionCategory.rst_idem _
  f2 i k hi hk := by
    rw [D.rho_apply i k hi hk]; exact D.s1 i k hi hk
  f3 i k hi hk := by
    rw [D.rho_apply i k hi hk]; exact D.s2 i k hi hk
  f4 i k hi hk r hr := D.s3 i k hi hk r hr

end StageSelection

end ApproximationDatum

end CategoryTheory
