/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DominicalClassUnions

/-! # Di Paola–Heller and Bernardi at a fixed Turing object -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.DiPaolaHeller CategoryTheory.PCategoryStruct
open CategoryTheory.CoprodStruct CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.DominicalLiteratureChecks

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [Limits.HasZeroMorphisms C]

theorem nonzero_turing_object [CoprodStruct C] [CategoryTheory.HasCoproducts C]
    (hd : Dominical C) (sections : @HasChoice C _ _ hd.toPCategory) {X : C}
    (τ : nearProd X X ⟶ coprod X X)
    (track : ∀ p : nearProd X X ⟶ coprod X X, ∃ h : X ⟶ X, IsTotal h ∧
      nearProd_map h (𝟙 X) ≫ τ = p) (nonzero : 𝟙 X ≠ (0 : X ⟶ X)) :
    letI : PCategory C := hd.toPCategory
    letI : HasChoice C := sections
    letI : RestrictionZero C := DominicalDiagonal.zeroRestriction hd
    letI : Ranges C := DominicalDiagonal.rangesOfChoice
    let a := Idem.pull (diag X ≫ τ) (summand0 X X)
    let b := Idem.pull (diag X ≫ τ) (summand1 X X)
    a ⊓ b = ⊥ ∧ ∀ c d : Idem X, c ⊓ d = ⊥ → c ⊔ d = ⊤ → a ≤ c → b ≤ d → False := by
  let : PCategory C := hd.toPCategory
  let : HasChoice C := sections
  let : RestrictionZero C := DominicalDiagonal.zeroRestriction hd
  let : Ranges C := DominicalDiagonal.rangesOfChoice
  have h := DominicalDiagonal.inseparable hd τ track nonzero
  exact ⟨h.disjoint, fun c d meet join ha hb => h.no_separator ⟨c, d, ⟨meet, join⟩, ha, hb⟩⟩

theorem fixed_point_for_partial_endomorphisms (hd : Dominical C) {X : C}
    (τ : nearProd X X ⟶ X) (universal : IsTuringMorphism τ)
    (η : nearProd X X ⟶ nearProd X X) (domain : rst η = η)
    (totalize : ∀ p : X ⟶ X, ∃ h : X ⟶ X, IsTotal h ∧ rst (partialPairing p h ≫ η) = rst p)
    (φ : X ⟶ X) : ∃ g : X ⟶ X, IsTotal g ∧
      rst (g ≫ partialPairing φ (𝟙 X) ≫ η) = rst (g ≫ φ) := by
  let : PCategory C := hd.toPCategory
  exact DominicalPrecompleteness.fixed_point τ universal ⟨η, domain⟩ totalize φ

theorem inseparable_class_unions [CoprodStruct C] [CategoryTheory.HasCoproducts C]
    (hd : Dominical C) (sections : @HasChoice C _ _ hd.toPCategory) {X : C}
    (τ : nearProd X X ⟶ X) (universal : IsTuringMorphism τ)
    (η : nearProd X X ⟶ nearProd X X) (domain : rst η = η)
    (totalize : ∀ p : X ⟶ X, ∃ h : X ⟶ X, IsTotal h ∧ rst (partialPairing p h ≫ η) = rst p) :
    letI : PCategory C := hd.toPCategory
    letI : HasChoice C := sections
    letI : RestrictionZero C := DominicalDiagonal.zeroRestriction hd
    letI : Ranges C := DominicalDiagonal.rangesOfChoice
    ∀ e d : Idem X,
      (∀ c : Idem X, e.hom ≫ c.hom = 0 → nearProd_map e.hom c.hom ≫ η = 0) →
      (∀ c : Idem X, d.hom ≫ c.hom = 0 → nearProd_map d.hom c.hom ≫ η = 0) →
      e.hom ≠ 0 → d.hom ≠ 0 → e.hom ≫ d.hom = 0 → Inseparable e d := by
  let : PCategory C := hd.toPCategory
  let : HasChoice C := sections
  intro e d ce cd ne nd disjoint
  exact DominicalPrecompleteness.class_unions_inseparable hd τ universal ⟨η, domain⟩
    totalize e d ce cd ne nd disjoint

end CategoricalEssentialIncompleteness.V46.DominicalLiteratureChecks

open CategoricalEssentialIncompleteness.V46

#print axioms DominicalDiagonal.complementary_section
#print axioms DominicalDiagonal.inseparable
#print axioms DominicalPrecompleteness.fixed_point
#print axioms DominicalPrecompleteness.exists_total_in_domain
#print axioms DominicalPrecompleteness.class_unions_inseparable
#print axioms DominicalLiteratureChecks.nonzero_turing_object
#print axioms DominicalLiteratureChecks.fixed_point_for_partial_endomorphisms
#print axioms DominicalLiteratureChecks.inseparable_class_unions
