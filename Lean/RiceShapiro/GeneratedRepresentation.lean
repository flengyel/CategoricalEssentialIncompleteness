/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import RiceShapiro.WitnessExistence
public import RiceShapiro.ExtensionFamilies

/-!
# The generated-domain representation

The manuscript's proposition on representation on index families and the
categorical Rice–Shapiro representation theorem.

`TotalLe` and `TotalEquiv` compare domains on total index families only.
`TotalMorphismsJointlyEpimorphicOnDomains` is the hypothesis under which that
comparison becomes the domain order, in `TotalLe.le` and `TotalEquiv.eq`.

`observationalRiceShapiro` identifies `s` with `υ(rst (s q))` on total index
families; `categoricalRiceShapiroRepresentation` upgrades this to an equality
of domains, converting ordinary extensionality to extensionality under
restriction by `extensionalUnderRestriction_of_extensional`.

Total range lifting is assumed only for `genHom (entryDomain s q)`. Neither
final theorem assumes `IsRP C`.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory DomSemilattice

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

namespace DomSemilattice

/-- `d ⪯ e` on total index families: every total `i` received by `d` is
received by `e`. -/
def TotalLe {I : C} (d e : DomSemilattice I) : Prop :=
  ∀ {Z : C} (i : Z ⟶ I), rst i = 𝟙 Z → i ≫ d.hom = i → i ≫ e.hom = i

/-- `d ≡ e` on total index families. -/
def TotalEquiv {I : C} (d e : DomSemilattice I) : Prop :=
  TotalLe d e ∧ TotalLe e d

end DomSemilattice

/-- Total morphisms are jointly epimorphic on domains: two morphisms agreeing
after every total morphism received by `d` agree after `d`. -/
def TotalMorphismsJointlyEpimorphicOnDomains (C : Type u) [Category.{v} C]
    [PCategoryStruct C] [PCategory C] : Prop :=
  ∀ {Z W : C} (d : DomSemilattice Z) (f g : Z ⟶ W),
    (∀ {T : C} (r : T ⟶ Z), rst r = 𝟙 T → r ≫ d.hom = r → r ≫ f = r ≫ g) →
      d.hom ≫ f = d.hom ≫ g

namespace DomSemilattice

/-- Comparison on total index families implies the domain order. -/
theorem TotalLe.le {I : C} {d e : DomSemilattice I} (h : TotalLe d e)
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C) : d ≤ e := by
  have hx : d.hom ≫ e.hom = d.hom ≫ 𝟙 I := by
    refine hjoint d e.hom (𝟙 I) ?_
    intro T r hr hrd
    rw [Category.comp_id]
    exact h r hr hrd
  rw [Category.comp_id] at hx
  exact hx

/-- Equivalence on total index families implies equality of domains. -/
theorem TotalEquiv.eq {I : C} {d e : DomSemilattice I} (h : TotalEquiv d e)
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C) : d = e :=
  le_antisymm (TotalLe.le h.1 hjoint) (TotalLe.le h.2 hjoint)

end DomSemilattice

namespace ApproximationDatum

variable {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)

/-- Ordinary extensionality implies extensionality under restriction. -/
theorem extensionalUnderRestriction_of_extensional
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C)
    (hs : Extensional 𝒜.ev s) : 𝒜.ExtensionalUnderRestriction s := by
  have key : ∀ {Z : C} (i j : Z ⟶ 𝒜.I), rst i = rst j →
      evalAt 𝒜.ev i = evalAt 𝒜.ev j → i ≫ s.hom = i → j ≫ s.hom = j := by
    intro Z i j hrij hev hi
    have hR1 : rst j ≫ j = j := RestrictionCategory.rst_comp_self j
    have hcond : ∀ {T : C} (r : T ⟶ Z), rst r = 𝟙 T →
        r ≫ (⟨rst j, rst_rst j⟩ : DomSemilattice Z).hom = r →
        r ≫ (j ≫ s.hom) = r ≫ j := by
      intro T r hr hrd
      have hrd' : r ≫ rst j = r := hrd
      have hti : rst (r ≫ i) = 𝟙 T := by
        rw [rst_comp_rst_right', hrij, hrd', hr]
      have htj : rst (r ≫ j) = 𝟙 T := by
        rw [rst_comp_rst_right', hrd', hr]
      have hevr : evalAt 𝒜.ev (r ≫ i) = evalAt 𝒜.ev (r ≫ j) := by
        rw [evalAt_comp, evalAt_comp, hev]
      have hri : (r ≫ i) ≫ s.hom = r ≫ i := by rw [Category.assoc, hi]
      have hrj := (hs (r ≫ i) (r ≫ j) hti htj hevr).mp hri
      rw [← Category.assoc]
      exact hrj
    have hjoin := hjoint (⟨rst j, rst_rst j⟩ : DomSemilattice Z)
      (j ≫ s.hom) j hcond
    calc j ≫ s.hom = (rst j ≫ j) ≫ s.hom := by rw [hR1]
      _ = rst j ≫ j ≫ s.hom := Category.assoc _ _ _
      _ = rst j ≫ j := hjoin
      _ = j := hR1
  intro Z i j hrij hev
  exact ⟨fun hi => key i j hrij hev hi, fun hj => key j i hrij.symm hev.symm hj⟩

end ApproximationDatum

section Representation

variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]
variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

namespace ApproximationDatum

variable {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)

/-- Representation on total index families: `s` and `υ(rst (s q))` receive the
same total index families. -/
theorem observationalRiceShapiro (D : 𝒜.WitnessSelection s) (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    (hdense : ∀ {Z : C} (d : DomSemilattice Z), IsDense d → d.hom = 𝟙 Z)
    (hlift : HasTotalRangeLifting (𝒜.genHom (entryDomain s q))) :
    TotalEquiv s (𝒜.gen (entryDomain s q)) := by
  constructor
  · intro Z i hi hsi
    exact (𝒜.mem_gen_iff (entryDomain s q) hlift i hi).mpr
      ((pointwiseRiceShapiro D cd hImported hTuring q hq hs i hi
        (fun d => hdense d) (fun d => hdense d)).mp hsi)
  · intro Z i hi hgi
    exact (pointwiseRiceShapiro D cd hImported hTuring q hq hs i hi
      (fun d => hdense d) (fun d => hdense d)).mpr
      ((𝒜.mem_gen_iff (entryDomain s q) hlift i hi).mp hgi)

/-- The categorical Rice–Shapiro representation: an extensional domain equals
the domain generated by `rst (s q)`. -/
theorem categoricalRiceShapiroRepresentation (D : 𝒜.WitnessSelection s)
    (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : Extensional 𝒜.ev s)
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C)
    (hdense : ∀ {Z : C} (d : DomSemilattice Z), IsDense d → d.hom = 𝟙 Z)
    (hlift : HasTotalRangeLifting (𝒜.genHom (entryDomain s q))) :
    s = 𝒜.gen (entryDomain s q) :=
  TotalEquiv.eq
    (𝒜.observationalRiceShapiro s D cd hImported hTuring q hq
      (𝒜.extensionalUnderRestriction_of_extensional s hjoint hs) hdense hlift)
    hjoint

end ApproximationDatum

end Representation

end CategoryTheory
