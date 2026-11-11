/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro.Selection
public import RiceShapiro.ParameterizedRecursion
public import RiceShapiro.UpwardClosure

/-!
# Existence of extension witnesses

The manuscript's theorems on the existence of selected extension witnesses and
the pointwise Rice–Shapiro equivalence.

`existsExtensionWitness` constructs, for a received total index family `i`, a
total approximation parameter `a` with `ba = a` for `b = rst (s q)` and
`a ≼ i`. The four clauses of the selection datum play separate roles: (F4)
makes the entry domain of the fixed point dense, (F1) makes `a` total, (F2)
gives the extension relation, and (F3) identifies the selected computation.

`pointwiseRiceShapiro` combines it with `upwardClosure`.

Dense-domain totality is assumed only for the object at hand:
`existsExtensionWitness` uses it on `Z`, and `pointwiseRiceShapiro`
additionally uses it on `Z ⊠ X` for the reverse implication, which goes through
route (ii). The Di Paola–Heller fixed-point principle is the explicit hypothesis
`HasImportedParameterizedRecursion`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory DomSemilattice

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

namespace ApproximationDatum

variable {X Y : C} {𝒜 : ApproximationDatum X Y} {s : DomSemilattice 𝒜.I}

namespace WitnessSelection

variable (D : 𝒜.WitnessSelection s) {Z : C} (i : Z ⟶ 𝒜.I)

/-- `F_s(⟨i p₀, p₁⟩ ⊠ 1_X)`, the family to which parameterized recursion is
applied. -/
def recursionFamily : nearProd (nearProd Z 𝒜.I) X ⟶ Y :=
  evalAt D.F (partialPairing (p0 Z 𝒜.I ≫ i) (p1 Z 𝒜.I))

omit [RecursionCategory.Prodominical C] in
/-- `⟨i p₀, p₁⟩⟨1_Z, h⟩ = ⟨i, h⟩`. -/
lemma recursionFamily_apply (h : Z ⟶ 𝒜.I) (hh : rst h = 𝟙 Z) :
    evalAt (D.recursionFamily i) (partialPairing (𝟙 Z) h)
      = evalAt D.F (partialPairing i h) := by
  have hp0 : partialPairing (𝟙 Z) h ≫ p0 Z 𝒜.I = 𝟙 Z := by
    rw [p0_partialPairing, hh, Category.id_comp]
  have hp1 : partialPairing (𝟙 Z) h ≫ p1 Z 𝒜.I = h := by
    rw [p1_partialPairing, PCategory.rst_id, Category.id_comp]
  dsimp only [recursionFamily, evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id,
    comp_partialPairing, ← Category.assoc, hp0, Category.id_comp, hp1]

end WitnessSelection

/-- Existence of a selected extension witness. -/
theorem existsExtensionWitness (D : 𝒜.WitnessSelection s)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    {Z : C} (i : Z ⟶ 𝒜.I) (hi : rst i = 𝟙 Z) (hsi : i ≫ s.hom = i)
    (hdenseZ : ∀ d : DomSemilattice Z, IsDense d → d.hom = 𝟙 Z) :
    ∃ a : Z ⟶ 𝒜.A, rst a = 𝟙 Z ∧ a ≫ entry s q = a ∧ 𝒜.Extends a i := by
  obtain ⟨h, hh, hfix0⟩ :=
    parameterizedRecursion hImported hTuring (D.recursionFamily i)
  have hh' : rst h = 𝟙 Z := hh
  have hfix : evalAt 𝒜.ev h = evalAt D.F (partialPairing i h) := by
    rw [hfix0, D.recursionFamily_apply i h hh]
  -- (F4): the entry domain of `h` is dense.
  have hdense : IsDense (entryDomain s h) := by
    intro d hd
    have h4 := D.f4 i h hi hh d hd
    have heq : evalAt 𝒜.ev (d.hom ≫ h) = evalAt 𝒜.ev (d.hom ≫ i) := by
      rw [evalAt_comp, evalAt_comp, hfix]
      exact h4
    have hrd : ∀ j : Z ⟶ 𝒜.I, rst j = 𝟙 Z → rst (d.hom ≫ j) = d.hom := by
      intro j hj
      rw [rst_comp_of_isTotal' _ hj, d.isDomain]
    have hri : (d.hom ≫ i) ≫ s.hom = d.hom ≫ i := by
      rw [Category.assoc, hsi]
    have hrh : (d.hom ≫ h) ≫ s.hom = d.hom ≫ h :=
      (hs _ _ (by rw [hrd h hh, hrd i hi]) heq).mpr hri
    have hzero : d.hom ≫ h = 0 := by
      rw [← hrh, Category.assoc, ← entryDomain_comp, ← Category.assoc, hd,
        Limits.zero_comp]
    have hx := hrd h hh
    rw [hzero, rst_zero] at hx
    exact hx.symm
  have hu : (entryDomain s h).hom = 𝟙 Z := hdenseZ _ hdense
  have hentry : entry s h = 𝟙 Z := hu
  refine ⟨partialPairing i h ≫ D.rho, ?_, ?_, ?_⟩
  · -- (F1)
    rw [D.f1 i h hi hh, hentry]
  · -- (F3), the fixed point, and the uniform index equation.
    have h3 := D.f3 i h hi hh
    rw [hentry, PCategory.nearProd_id, Category.id_comp, ← hfix] at h3
    have hstep : evalAt 𝒜.ev h
        = evalAt 𝒜.ev ((partialPairing i h ≫ D.rho) ≫ q) :=
      calc evalAt 𝒜.ev h
          = evalAt 𝒜.approx (partialPairing i h ≫ D.rho) := h3
        _ = nearProd_map (partialPairing i h ≫ D.rho) (𝟙 X) ≫ 𝒜.approx := rfl
        _ = nearProd_map (partialPairing i h ≫ D.rho) (𝟙 X)
              ≫ evalAt 𝒜.ev q := by rw [hq.2]
        _ = evalAt 𝒜.ev ((partialPairing i h ≫ D.rho) ≫ q) :=
            (evalAt_comp _ _ _).symm
    have hah : rst (partialPairing i h ≫ D.rho) = 𝟙 Z := by
      rw [D.f1 i h hi hh, hentry]
    have hrq : rst ((partialPairing i h ≫ D.rho) ≫ q) = 𝟙 Z := by
      rw [rst_comp_of_isTotal' _ hq.1, hah]
    have hhs : h ≫ s.hom = h := by
      have hx := entryDomain_comp s h
      rwa [hu, Category.id_comp, eq_comm] at hx
    have hqs : ((partialPairing i h ≫ D.rho) ≫ q) ≫ s.hom
        = (partialPairing i h ≫ D.rho) ≫ q :=
      (hs _ _ (by rw [hh', hrq]) hstep).mp hhs
    have hent : entry s ((partialPairing i h ≫ D.rho) ≫ q) = 𝟙 Z := by
      dsimp only [entry]
      rw [hqs, hrq]
    have hce := comp_entry s (partialPairing i h ≫ D.rho) q
    rwa [hent, Category.id_comp, eq_comm] at hce
  · -- (F2)
    have h2 := D.f2 i h hi hh
    rwa [hentry, Category.id_comp] at h2

end ApproximationDatum

section Pointwise

variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]

namespace ApproximationDatum

variable {X Y : C} {𝒜 : ApproximationDatum X Y} {s : DomSemilattice 𝒜.I}

/-- The pointwise Rice–Shapiro equivalence. The forward implication is
`existsExtensionWitness`; the reverse is `upwardClosure`, which uses route
(ii). -/
theorem pointwiseRiceShapiro (D : 𝒜.WitnessSelection s) (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    {Z : C} (i : Z ⟶ 𝒜.I) (hi : rst i = 𝟙 Z)
    (hdenseZX : ∀ d : DomSemilattice (nearProd Z X), IsDense d
      → d.hom = 𝟙 (nearProd Z X))
    (hdenseZ : ∀ d : DomSemilattice Z, IsDense d → d.hom = 𝟙 Z) :
    i ≫ s.hom = i ↔
      ∃ a : Z ⟶ 𝒜.A, rst a = 𝟙 Z ∧ a ≫ entry s q = a ∧ 𝒜.Extends a i := by
  constructor
  · intro hsi
    exact existsExtensionWitness D hImported hTuring q hq hs i hi hsi hdenseZ
  · rintro ⟨a, ha, hba, hai⟩
    exact 𝒜.upwardClosure s a i cd hImported hTuring q hq hs ha hi hba hai
      hdenseZX hdenseZ

end ApproximationDatum

end Pointwise

end CategoryTheory
