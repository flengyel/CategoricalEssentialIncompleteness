/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46DecidableVariablesTransport
import CategoricalEssentialIncompleteness.TwoBoolean

/-! # Boolean constants and branches under the actual equivalence -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open DecidableVariables.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

@[reassoc] theorem booleanIso_inl :
    E.functor.map (coprod.inl : ⊤_ C ⟶ Two C) ≫ (booleanIso E).hom =
      (terminalIso E).hom ≫ coprod.inl := by
  change E.functor.map coprod.inl ≫
    (inv (coprodComparison E.functor (⊤_ C) (⊤_ C)) ≫
      coprod.map (terminalComparison E.functor) (terminalComparison E.functor)) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]
  rfl

@[reassoc] theorem booleanIso_point (b : Bool) :
    E.functor.map (Two.point b : ⊤_ C ⟶ Two C) ≫ (booleanIso E).hom =
      (terminalIso E).hom ≫ Two.point b := by
  cases b
  · exact booleanIso_inl E
  · exact DecidableVariables.Transport.booleanIso_inr E

theorem map_constant (X : C) (b : Bool) :
    E.functor.map (Two.constant X b) ≫ (booleanIso E).hom =
      Two.constant (E.functor.obj X) b := by
  unfold Two.constant
  rw [Functor.map_comp,Category.assoc,booleanIso_point,← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

omit [Regular D] in
/-- Images of the two actual source fibers remain jointly epimorphic.
No identity of chosen source and target fiber codes is used. -/
theorem map_hom_ext {X : C} (χ : X ⟶ Two C) {Y : D}
    {f g : E.functor.obj X ⟶ Y}
    (h₀ : E.functor.map (Two.fiberι χ false) ≫ f = E.functor.map (Two.fiberι χ false) ≫ g)
    (h₁ : E.functor.map (Two.fiberι χ true) ≫ f = E.functor.map (Two.fiberι χ true) ≫ g) : f = g := by
  let h := isColimitOfPreserves E.functor (Two.fibersIsColimit χ)
  apply h.hom_ext
  rintro ⟨i⟩
  cases i
  · exact h₀
  · exact h₁

theorem map_branch {X Y : C} (χ : X ⟶ Two C) (f g : X ⟶ Y) :
    E.functor.map (Two.branch χ f g) =
      Two.branch (E.functor.map χ ≫ (booleanIso E).hom)
        (E.functor.map f) (E.functor.map g) := by
  have h (b : Bool) :
      E.functor.map (Two.fiberι χ b) ≫ E.functor.map (Two.branch χ f g) =
        E.functor.map (Two.fiberι χ b) ≫
          Two.branch (E.functor.map χ ≫ (booleanIso E).hom)
            (E.functor.map f) (E.functor.map g) := by
    have hb : E.functor.map (Two.fiberι χ b) ≫
        (E.functor.map χ ≫ (booleanIso E).hom) = Two.constant (E.functor.obj (Two.Fiber χ b)) b := by
      rw [← Category.assoc,← Functor.map_comp,Two.fiberι_comp,map_constant]
    rw [← Functor.map_comp,Two.fiberι_branch,Functor.map_comp]
    rw [Two.comp_branch _ _ _ _ b hb]
    cases b <;> rfl
  exact map_hom_ext E χ (h false) (h true)

/-- General precomposition of the categorical branch, proved on the
actual fibers of the composite classifier. -/
theorem branch_precomp {X Y Z : D} (χ : X ⟶ Two D) (f g : X ⟶ Y) (k : Z ⟶ X) :
    k ≫ Two.branch χ f g = Two.branch (k ≫ χ) (k ≫ f) (k ≫ g) := by
  have h (b : Bool) :
      Two.fiberι (k ≫ χ) b ≫ (k ≫ Two.branch χ f g) =
        Two.fiberι (k ≫ χ) b ≫ Two.branch (k ≫ χ) (k ≫ f) (k ≫ g) := by
    have hb : (Two.fiberι (k ≫ χ) b ≫ k) ≫ χ = Two.constant (Two.Fiber (k ≫ χ) b) b := by
      rw [Category.assoc,Two.fiberι_comp]
    rw [← Category.assoc,Two.comp_branch χ f g _ b hb,Two.fiberι_branch]
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Category.assoc]
  exact Two.hom_ext (k ≫ χ) (h false) (h true)

/-- Inclusion of the true fiber is the order on the internal Boolean
classifiers. The proof uses the Boolean algebra of generalized truth values. -/
theorem classifier_le_of_true {X : C} (f g : X ⟶ Two C)
    (h : Two.fiberι f true ≫ g = Two.constant (Two.Fiber f true) true) : f ≤ g := by
  apply inf_eq_left.mp
  apply Two.hom_ext f
  · simp only [Two.inf_def,Two.comp_binary,Two.fiberι_comp]
    change (⊥ : Two.Fiber f false ⟶ Two C) ⊓ (Two.fiberι f false ≫ g) = ⊥
    exact bot_inf_eq _
  · simp only [Two.inf_def,Two.comp_binary,Two.fiberι_comp,h]
    change (⊤ : Two.Fiber f true ⟶ Two C) ⊓ ⊤ = ⊤
    exact inf_idem _

private theorem equality_true_fiber {V : C} (a b : DecidableVariables V) :
    Two.fiberι a.test true ≫ b.test = Two.constant (Two.Fiber a.test true) true := by
  let i := Two.fiberι a.test true
  have hc : i ≫ a.test = terminal.from (Two.Fiber a.test true) ≫ coprod.inr :=
    Two.fiberι_comp a.test true
  let lift := a.diagonal.lift i (terminal.from _) hc
  have hl : lift ≫ prod.lift (𝟙 V) (𝟙 V) = i := a.diagonal.lift_fst _ _ hc
  change i ≫ b.test = _
  rw [← hl,Category.assoc,b.diagonal.w]
  exact Two.comp_constant lift true

/-- The diagonal pullback determines internal decidable equality uniquely.
This removes dependence on the selected preimage in the concrete transport. -/
theorem equality_test_unique {V : C} (a b : DecidableVariables V) : a.test = b.test := by
  apply le_antisymm
  · exact classifier_le_of_true a.test b.test (equality_true_fiber a b)
  · exact classifier_le_of_true b.test a.test (equality_true_fiber b a)

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
