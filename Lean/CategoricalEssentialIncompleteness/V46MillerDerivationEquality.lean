/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxComparison
public import CategoricalEssentialIncompleteness.V46MillerSyntaxChildren
public import CategoricalEssentialIncompleteness.V46MillerTotalRegular
public import CategoricalEssentialIncompleteness.V46SyntacticDecidableVariables
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Actual internal numerical equality on every uniform carrier

The full numerical carrier has its ordinary equality test under the
proved finite-geometry comparison. Every arbitrary uniform carrier
embeds by the identity on values; monomorphism cancellation transports
the actual diagonal pullback. No coefficient predicate is decided.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.Miller.Derivation

section FunctorEquality
variable {C D : Type} [Category C] [Category D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]

def terminalIso : F.obj (⊤_ C) ≅ ⊤_ D := asIso (terminalComparison F)

def booleanIso : F.obj ((⊤_ C) ⨿ (⊤_ C)) ≅ (⊤_ D) ⨿ (⊤_ D) :=
  (asIso (coprodComparison F (⊤_ C) (⊤_ C))).symm ≪≫
    coprod.mapIso (terminalIso F) (terminalIso F)

theorem booleanIso_inr :
    F.map (coprod.inr : ⊤_ C ⟶ (⊤_ C) ⨿ (⊤_ C)) ≫ (booleanIso F).hom=
      (terminalIso F).hom ≫ coprod.inr := by
  change F.map coprod.inr ≫ (inv (coprodComparison F (⊤_ C) (⊤_ C)) ≫
    coprod.map (terminalComparison F) (terminalComparison F))=_
  rw [← Category.assoc,map_inr_inv_coprodComparison,coprod.inr_map]
  rfl

def mappedEquality {V : C} (E : DecidableVariables V) : DecidableVariables (F.obj V) where
  test := inv (prodComparison F V V) ≫ F.map E.test ≫ (booleanIso F).hom
  diagonal := by
    apply (F.map_isPullback E.diagonal).of_iso (Iso.refl _)
      (asIso (prodComparison F V V)) (terminalIso F) (booleanIso F)
    · apply prod.hom_ext <;> simp [Category.assoc,← F.map_comp]
    · exact CategoryTheory.Limits.terminalIsTerminal.hom_ext _ _
    · change F.map E.test ≫ (booleanIso F).hom =
        prodComparison F V V ≫ inv (prodComparison F V V) ≫ F.map E.test ≫ (booleanIso F).hom
      rw [IsIso.hom_inv_id_assoc]
    · exact booleanIso_inr F
end FunctorEquality

section SubobjectEquality
variable {D : Type} [Category D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (i : X ⟶ V) [Mono i] (E : DecidableVariables V)

def inducedTest : X ⨯ X ⟶ Two D := prod.map i i ≫ E.test

theorem inducedTest_true_iff {W : D} (f : W ⟶ X ⨯ X) :
    f ≫ inducedTest i E=Two.constant W true ↔ f ≫ prod.fst=f ≫ prod.snd := by
  have h := E.test_true_iff ((f ≫ prod.fst) ≫ i) ((f ≫ prod.snd) ≫ i)
  rw [cancel_mono] at h
  have hm : f ≫ prod.map i i=prod.lift ((f ≫ prod.fst) ≫ i) ((f ≫ prod.snd) ≫ i) := by
    apply prod.hom_ext <;> simp only [Category.assoc,prod.map_fst,prod.map_snd,prod.lift_fst,prod.lift_snd]
  unfold inducedTest
  rw [← Category.assoc,hm]
  exact h

def subobjectEquality : DecidableVariables X where
  test := inducedTest i E
  diagonal := by
    let d := prod.lift (𝟙 X) (𝟙 X)
    have hd : d ≫ inducedTest i E=terminal.from X ≫ coprod.inr :=
      (inducedTest_true_iff i E d).mpr (by simp [d])
    refine IsPullback.of_isLimit (c := PullbackCone.mk d (terminal.from X) hd) ?_
    refine PullbackCone.IsLimit.mk hd (fun s => s.fst ≫ prod.fst) ?_ ?_ ?_
    · intro s
      have he : s.fst ≫ prod.fst=s.fst ≫ prod.snd := by
        apply (inducedTest_true_iff i E s.fst).mp
        change s.fst ≫ inducedTest i E=terminal.from s.pt ≫ coprod.inr
        exact s.condition.trans (congrArg (fun k => k ≫ coprod.inr) (terminal.hom_ext s.snd (terminal.from s.pt)))
      apply prod.hom_ext
      · simp [d]
      · simpa [d,Category.assoc] using he
    · intro s
      exact terminal.hom_ext _ _
    · intro s m hm _
      have he := congrArg (fun k => k ≫ prod.fst) hm
      simpa [d,Category.assoc] using he
end SubobjectEquality

variable {P : Uniform.Family}

def numbers : Total.TotalCategory P := (Syntax.predicateFunctor P).obj Syntax.Raw.topCarrier

def inclusion (X : Total.TotalCategory P) : X ⟶ numbers :=
  ⟨Total.totalFromFunction id Computable.id (by
      intro n _
      exact (Syntax.Raw.mapped_coefficient_support Syntax.Raw.topCarrier n).mpr (by simp [Syntax.Raw.topCarrier])),
    Total.totalFromFunction_total _ _ _⟩

instance inclusion_mono (X : Total.TotalCategory P) : Mono (inclusion X) := by
  have hm : Mono (inclusion X).hom := Total.mono_of_total_injective (inclusion X).hom (inclusion X).property (by
    intro x x' y h h'
    have hs : ∀ n ∈ X.obj.support,id n ∈ (numbers (P := P)).obj.support := by
      intro n _
      exact (Syntax.Raw.mapped_coefficient_support Syntax.Raw.topCarrier n).mpr (by simp [Syntax.Raw.topCarrier])
    exact ((Total.mem_totalFromFunction (X := X.obj) (Y := (numbers (P := P)).obj) id Computable.id hs x y).mp h).2.symm.trans
      ((Total.mem_totalFromFunction (X := X.obj) (Y := (numbers (P := P)).obj) id Computable.id hs x' y).mp h').2)
  exact (wideSubcategoryInclusion (isTotal (C := Total.Carrier P))).mono_of_mono_map hm

def equality (X : Total.TotalCategory P) : DecidableVariables X :=
  subobjectEquality (inclusion X)
    (mappedEquality (Syntax.predicateFunctor P)
      (SyntacticDecidableVariables.decidableVariables 𝗣𝗔 Syntax.Raw.topCarrier))

end CategoricalEssentialIncompleteness.V46.Miller.Derivation
