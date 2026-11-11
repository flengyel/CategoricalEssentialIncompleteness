/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro.CaseLaws
public import RiceShapiro.ParameterizedRecursion

/-!
# Dense upward closure

The manuscript's theorem "dense upward closure" and its corollary "upward
closure".

`ExtensionalUnderRestriction 𝒜 s` is the hypothesis that membership in `s`
depends on an index only through the indexed morphism and the restriction, for
index families that need not be total.

`denseUpwardClosure`: if `a` and `i` are total, `ba = a` for `b = rst (s q)`
with `q` a uniform index morphism, and `a ≼ i`, then `rst (s i)` is dense.
`upwardClosure` concludes `s i = i` when the dense domains on the source are
total.

Both use route (ii) of the manuscript's lemma on complements and total inverse
images, through `caseJoin_of_dense`, and both take the Di Paola–Heller
fixed-point principle as the explicit hypothesis
`HasImportedParameterizedRecursion`. The two dense-totality assumptions concern
`Z ⊠ X` and `Z` separately.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory DomSemilattice

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]
variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

namespace DomSemilattice

/-- `rst (s i)` as a domain on the source of `i`. -/
def entryDomain {I Z : C} (s : DomSemilattice I) (i : Z ⟶ I) :
    DomSemilattice Z :=
  ⟨entry s i, rst_entry s i⟩

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
@[simp] lemma entryDomain_hom {I Z : C} (s : DomSemilattice I) (i : Z ⟶ I) :
    (entryDomain s i).hom = entry s i := rfl

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `s i = i (rst (s i))`, the restriction axiom for `i` and `s`. -/
lemma entryDomain_comp {I Z : C} (s : DomSemilattice I) (i : Z ⟶ I) :
    (entryDomain s i).hom ≫ i = i ≫ s.hom := by
  have hx := PCategory.rst_comp' i s.hom
  rwa [s.isDomain] at hx

end DomSemilattice

namespace ApproximationDatum

open DomSemilattice

variable {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)

/-- Membership in `s` depends on an index only through the indexed morphism and
the restriction. No totality is assumed of the index families. -/
def ExtensionalUnderRestriction : Prop :=
  ∀ {Z : C} (i j : Z ⟶ 𝒜.I), rst i = rst j →
    evalAt 𝒜.ev i = evalAt 𝒜.ev j → (i ≫ s.hom = i ↔ j ≫ s.hom = j)

variable {Z : C} (a : Z ⟶ 𝒜.A) (i : Z ⟶ 𝒜.I)

/-- `Φ = Case_s(⟨⟨a p₀, i p₀⟩, p₁⟩ ⊠ 1_X)`. -/
def caseFamily (cd : 𝒜.CaseData) : nearProd (nearProd Z 𝒜.I) X ⟶ Y :=
  𝒜.caseAt s (p0 Z 𝒜.I ≫ a) (p0 Z 𝒜.I ≫ i) (p1 Z 𝒜.I) cd

omit [HasCoproducts C] [RecursionCategory.Prodominical C] in
/-- `⟨⟨a p₀, i p₀⟩, p₁⟩⟨1_Z, h⟩ = ⟨⟨a, i⟩, h⟩`. -/
lemma caseFamily_apply (cd : 𝒜.CaseData) (h : Z ⟶ 𝒜.I) (hh : rst h = 𝟙 Z) :
    evalAt (𝒜.caseFamily s a i cd) (partialPairing (𝟙 Z) h)
      = 𝒜.caseAt s a i h cd := by
  have hp0 : partialPairing (𝟙 Z) h ≫ p0 Z 𝒜.I = 𝟙 Z := by
    rw [p0_partialPairing, hh, Category.id_comp]
  have hp1 : partialPairing (𝟙 Z) h ≫ p1 Z 𝒜.I = h := by
    rw [p1_partialPairing, PCategory.rst_id, Category.id_comp]
  dsimp only [caseFamily, caseAt, param, evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id,
    comp_partialPairing, comp_partialPairing, ← Category.assoc, hp0,
    Category.id_comp, ← Category.assoc, hp0, Category.id_comp, hp1]

/-- Dense upward closure. -/
theorem denseUpwardClosure (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z)
    (hba : a ≫ entry s q = a) (hai : 𝒜.Extends a i)
    (hdenseZX : ∀ d : DomSemilattice (nearProd Z X), IsDense d
      → d.hom = 𝟙 (nearProd Z X)) :
    IsDense (entryDomain s i) := by
  obtain ⟨h, hh, hfix0⟩ :=
    parameterizedRecursion hImported hTuring (𝒜.caseFamily s a i cd)
  have hfix : evalAt 𝒜.ev h = 𝒜.caseAt s a i h cd := by
    rw [hfix0, 𝒜.caseFamily_apply s a i cd h hh]
  have hjoin := 𝒜.caseJoin_of_dense a i h cd ha hi hh hdenseZX
  -- `u = rst (s h)` and `v = rst (s i)`.
  have hsh : ((entryDomain s h).hom ≫ h) ≫ s.hom
      = (entryDomain s h).hom ≫ h := by
    rw [entryDomain_comp, Category.assoc, s.idem]
  have hentry : evalAt 𝒜.ev ((entryDomain s h).hom ≫ h)
      = evalAt 𝒜.ev ((entryDomain s h).hom ≫ i) := by
    rw [evalAt_comp, evalAt_comp, hfix]
    exact 𝒜.case_law_entry s a i h cd ha hi hh hjoin hai
  have hrst : ∀ j : Z ⟶ 𝒜.I, rst j = 𝟙 Z →
      rst ((entryDomain s h).hom ≫ j) = (entryDomain s h).hom := by
    intro j hj
    rw [rst_comp_of_isTotal' _ hj, (entryDomain s h).isDomain]
  have hsi : ((entryDomain s h).hom ≫ i) ≫ s.hom
      = (entryDomain s h).hom ≫ i :=
    (hs _ _ (by rw [hrst h hh, hrst i hi]) hentry).mp hsh
  have hle : entryDomain s h ≤ entryDomain s i := by
    have hx := PCategory.rst_comp' (entryDomain s h).hom (i ≫ s.hom)
    rw [← Category.assoc, hsi, hrst i hi, (entryDomain s h).idem] at hx
    exact hx.symm
  refine IsDense.mono hle ?_
  intro d hd
  have hlaw := 𝒜.case_law_zero s a i h cd ha hi hh hjoin d hd
  rw [DomSemilattice.rightTimes_hom] at hlaw
  have hda : evalAt 𝒜.ev (d.hom ≫ h)
      = evalAt 𝒜.ev ((d.hom ≫ a) ≫ q) :=
    calc evalAt 𝒜.ev (d.hom ≫ h)
        = nearProd_map d.hom (𝟙 X) ≫ evalAt 𝒜.ev h := evalAt_comp _ _ _
      _ = nearProd_map d.hom (𝟙 X) ≫ 𝒜.caseAt s a i h cd := by rw [hfix]
      _ = nearProd_map d.hom (𝟙 X) ≫ evalAt 𝒜.approx a := hlaw
      _ = nearProd_map (d.hom ≫ a) (𝟙 X) ≫ 𝒜.approx :=
          (evalAt_comp 𝒜.approx d.hom a).symm
      _ = nearProd_map (d.hom ≫ a) (𝟙 X) ≫ evalAt 𝒜.ev q := by rw [hq.2]
      _ = evalAt 𝒜.ev ((d.hom ≫ a) ≫ q) := (evalAt_comp _ _ _).symm
  have hqs : ((d.hom ≫ a) ≫ q) ≫ s.hom = (d.hom ≫ a) ≫ q := by
    have hx : entry s q ≫ q = q ≫ s.hom := by
      have hy := PCategory.rst_comp' q s.hom
      rwa [s.isDomain] at hy
    calc ((d.hom ≫ a) ≫ q) ≫ s.hom = (d.hom ≫ a) ≫ q ≫ s.hom :=
          Category.assoc _ _ _
      _ = (d.hom ≫ a) ≫ entry s q ≫ q := by rw [hx]
      _ = (d.hom ≫ a ≫ entry s q) ≫ q := by
          simp only [Category.assoc]
      _ = (d.hom ≫ a) ≫ q := by rw [hba]
  have hrstd : ∀ j : Z ⟶ 𝒜.I, rst j = 𝟙 Z → rst (d.hom ≫ j) = d.hom := by
    intro j hj
    rw [rst_comp_of_isTotal' _ hj, d.isDomain]
  have hrstq : rst ((d.hom ≫ a) ≫ q) = d.hom := by
    rw [rst_comp_of_isTotal' _ hq.1, rst_comp_of_isTotal' _ ha, d.isDomain]
  have hdh : (d.hom ≫ h) ≫ s.hom = d.hom ≫ h :=
    (hs _ _ (by rw [hrstd h hh, hrstq]) hda).mpr hqs
  have hdh0 : d.hom ≫ h = 0 := by
    rw [← hdh, Category.assoc, ← entryDomain_comp, ← Category.assoc, hd,
      Limits.zero_comp]
  have := hrstd h hh
  rw [hdh0, rst_zero] at this
  exact this.symm

/-- Upward closure. -/
theorem upwardClosure (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z)
    (hba : a ≫ entry s q = a) (hai : 𝒜.Extends a i)
    (hdenseZX : ∀ d : DomSemilattice (nearProd Z X), IsDense d
      → d.hom = 𝟙 (nearProd Z X))
    (hdenseZ : ∀ d : DomSemilattice Z, IsDense d → d.hom = 𝟙 Z) :
    i ≫ s.hom = i := by
  have hdense := 𝒜.denseUpwardClosure s a i cd hImported hTuring q hq hs ha hi
    hba hai hdenseZX
  have htot : (entryDomain s i).hom = 𝟙 Z := hdenseZ _ hdense
  have hx := entryDomain_comp s i
  rwa [htot, Category.id_comp, eq_comm] at hx

end ApproximationDatum

end CategoryTheory
