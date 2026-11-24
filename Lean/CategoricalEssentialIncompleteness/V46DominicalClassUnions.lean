/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DominicalPrecompleteness

/-!
# Inseparability of unions of classes in a dominical category

Bernardi's Definition 3 expresses a union of classes by annihilation on
the near product with each disjoint domain. His Theorem 2 rules out
a complemented separator between two nonzero disjoint such domains.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.DiPaolaHeller CategoryTheory.PCategoryStruct
open CategoryTheory.PCategory CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoryTheory.Limits CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.DominicalPrecompleteness

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [HasZeroMorphisms C]

/-- Bernardi's Definition 3 for a domain on the square of the fixed object. -/
def UnionOfClasses {X : C} (η : Idem (nearProd X X)) (e : Idem X) : Prop :=
  ∀ d : Idem X, e.hom ≫ d.hom = 0 → nearProd_map e.hom d.hom ≫ η.hom = 0

variable [CoprodStruct C] [CategoryTheory.HasCoproducts C]

private theorem branches [RestrictionZero C] [RestrictionCoproducts C] [Ranges C]
    [HasChoice C] (hd : Dominical C) {X : C} (a b e d : Idem X) (cover : Complementary a b)
    (f g : X ⟶ X) (tf : DiPaolaHeller.IsTotal f) (tg : DiPaolaHeller.IsTotal g)
    (fe : f ≫ e.hom = f) (gd : g ≫ d.hom = g) :
    ∃ ψ : X ⟶ X, DiPaolaHeller.IsTotal ψ ∧
      (a.hom ≫ ψ) ≫ e.hom = a.hom ≫ ψ ∧ (b.hom ≫ ψ) ≫ d.hom = b.hom ≫ ψ := by
  obtain ⟨s, ts, ha, hb⟩ := DominicalDiagonal.complementary_section a b cover
  let p := copair f g
  have ptotal : DiPaolaHeller.IsTotal p := by
    apply (hd.isTotal_iff_rst_eq_id _).mpr
    change RestrictionCategory.rst (copair f g) = _
    rw [restrict_copair, (hd.isTotal_iff_restrictionTotal f).mp tf,
      (hd.isTotal_iff_restrictionTotal g).mp tg, coprod_id]
  have left : (summand0 X X).hom ≫ p ≫ e.hom = (summand0 X X).hom ≫ p := by
    apply CategoryTheory.HasCoproducts.hom_ext <;>
      simp only [p, ← Category.assoc, i0_summand0, i1_summand0, i0_copair, fe, zero_comp]
  have right : (summand1 X X).hom ≫ p ≫ d.hom = (summand1 X X).hom ≫ p := by
    apply CategoryTheory.HasCoproducts.hom_ext <;>
      simp only [p, ← Category.assoc, i0_summand1, i1_summand1, i1_copair, gd, zero_comp]
  have agreement (c : Idem X) (q : Idem (coprod X X)) (z : Idem X)
      (fiber : Idem.pull s q = c) (supported : q.hom ≫ p ≫ z.hom = q.hom ≫ p) :
      (c.hom ≫ s ≫ p) ≫ z.hom = c.hom ≫ s ≫ p := by
    have comm := Idem.pull_commute s q
    rw [fiber] at comm
    calc (c.hom ≫ s ≫ p) ≫ z.hom = (c.hom ≫ s) ≫ p ≫ z.hom := by simp only [Category.assoc]
         _ = s ≫ q.hom ≫ p := by rw [comm, Category.assoc, supported]
         _ = c.hom ≫ s ≫ p := by rw [← Category.assoc, ← comm, Category.assoc]
  exact ⟨s ≫ p, DiPaolaHeller.IsTotal.comp ((hd.isTotal_iff_restrictionTotal s).mpr ts) ptotal,
    agreement a _ e ha left, agreement b _ d hb right⟩

omit [CoprodStruct C] [CategoryTheory.HasCoproducts C] in
private theorem empty_branch [RestrictionZero C] {X : C}
    (η : Idem (nearProd X X)) (e a : Idem X) (closed : UnionOfClasses η e)
    (disjoint : e.hom ≫ a.hom = 0) (ψ g : X ⟶ X)
    (branch : (a.hom ≫ ψ) ≫ e.hom = a.hom ≫ ψ)
    (fixed : DiPaolaHeller.IsTotal (g ≫ partialPairing ψ (𝟙 X) ≫ η.hom)) :
    Idem.pull g a = ⊥ := by
  let u := g ≫ a.hom
  have ua : u ≫ a.hom = u := by simp only [u, Category.assoc, a.idem]
  have ue : (u ≫ ψ) ≫ e.hom = u ≫ ψ := by
    simpa only [u, Category.assoc] using congrArg (fun k => g ≫ k) branch
  have range : partialPairing (u ≫ ψ) u ≫ nearProd_map e.hom a.hom = partialPairing (u ≫ ψ) u := by
    rw [partialPairing_comp_nearProd_map, ue, ua]
  have zero : u ≫ partialPairing ψ (𝟙 X) ≫ η.hom = 0 := by
    rw [← Category.assoc, comp_partialPairing, Category.comp_id, ← range, Category.assoc,
      closed a disjoint, comp_zero]
  apply Idem.ext
  exact fixed (Idem.pull g a).hom (by rw [← Category.assoc, Idem.pull_commute]; exact zero)

/-- Bernardi's Theorem 2 with his quantification over all disjoint domains. -/
theorem class_unions_inseparable [HasChoice C] (hd : Dominical C) {X : C}
    (τ : nearProd X X ⟶ X) (universal : IsTuringMorphism τ) (η : Idem (nearProd X X))
    (complete : Precomplete η) (e d : Idem X) (ce : UnionOfClasses η e) (cd : UnionOfClasses η d)
    (hne : e.hom ≠ 0) (hnd : d.hom ≠ 0) (disjoint : e.hom ≫ d.hom = 0) :
    letI : RestrictionZero C := DominicalDiagonal.zeroRestriction hd
    letI : Ranges C := DominicalDiagonal.rangesOfChoice
    Inseparable e d := by
  let : RestrictionZero C := DominicalDiagonal.zeroRestriction hd
  let : Ranges C := DominicalDiagonal.rangesOfChoice
  change Inseparable e d
  refine ⟨Idem.ext disjoint, ?_⟩
  rintro ⟨a, b, cover, ea, db⟩
  obtain ⟨f, tf, fd⟩ := exists_total_in_domain hd d hnd X
  obtain ⟨h, th, he⟩ := exists_total_in_domain hd e hne X
  obtain ⟨ψ, tψ, da, eb⟩ := branches hd a b d e cover f h tf th fd he
  obtain ⟨g, tg, eq⟩ := fixed_point τ universal η complete ψ
  have fixed : DiPaolaHeller.IsTotal (g ≫ partialPairing ψ (𝟙 X) ≫ η.hom) :=
    (hd.isTotal_iff_rst_eq_id _).mpr (eq.trans ((hd.isTotal_iff_rst_eq_id (g ≫ ψ)).mp (tg.comp tψ)))
  have ad : d ⊓ a = ⊥ := le_antisymm ((inf_le_inf db le_rfl).trans_eq cover.symm.disjoint) bot_le
  have be : e ⊓ b = ⊥ := le_antisymm ((inf_le_inf ea le_rfl).trans_eq cover.disjoint) bot_le
  have za := empty_branch η d a cd (congrArg Idem.hom ad) ψ g da fixed
  have zb := empty_branch η e b ce (congrArg Idem.hom be) ψ g eb fixed
  have gz := DominicalDiagonal.zero_of_empty_preimages cover g za zb
  have idz := tg (𝟙 X) (by rw [gz, comp_zero])
  exact hne (by calc e.hom = 𝟙 X ≫ e.hom := (Category.id_comp _).symm
                     _ = 0 := by rw [idz, zero_comp])

end CategoricalEssentialIncompleteness.V46.DominicalPrecompleteness
