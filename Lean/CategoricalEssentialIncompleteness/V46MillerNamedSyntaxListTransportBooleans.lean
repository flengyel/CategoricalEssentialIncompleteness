/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationEquality
public import CategoricalEssentialIncompleteness.V46SyntaxListOperationsTransportBooleans

/-! Boolean operations under the finite-geometry preserving functor. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
open Derivation
variable {C D : Type} [Category C] [Category D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
theorem booleanIso_inl :
    F.map (coprod.inl : ⊤_ C ⟶ Two C) ≫ (booleanIso F).hom =
      (terminalIso F).hom ≫ coprod.inl := by
  change F.map coprod.inl ≫
    (inv (coprodComparison F (⊤_ C) (⊤_ C)) ≫
      coprod.map (terminalComparison F) (terminalComparison F)) = _
  rw [← Category.assoc,map_inl_inv_coprodComparison,coprod.inl_map]
  rfl

theorem booleanIso_point (b : Bool) :
    F.map (Two.point b : ⊤_ C ⟶ Two C) ≫ (booleanIso F).hom =
      (terminalIso F).hom ≫ Two.point b := by
  cases b
  · exact booleanIso_inl F
  · exact Derivation.booleanIso_inr F

theorem map_constant (X : C) (b : Bool) :
    F.map (Two.constant X b) ≫ (booleanIso F).hom =
      Two.constant (F.obj X) b := by
  unfold Two.constant
  rw [Functor.map_comp,Category.assoc,booleanIso_point,← Category.assoc]
  congr 1
  exact terminalIsTerminal.hom_ext _ _

omit [Regular D] [FinitaryExtensive D] [PreservesFiniteLimits F] in
/-- Images of the two source fibers remain jointly epimorphic. No identity of chosen
source and target fiber codes is used. -/
theorem map_hom_ext {X : C} (χ : X ⟶ Two C) {Y : D}
    {f g : F.obj X ⟶ Y}
    (h₀ : F.map (Two.fiberι χ false) ≫ f = F.map (Two.fiberι χ false) ≫ g)
    (h₁ : F.map (Two.fiberι χ true) ≫ f = F.map (Two.fiberι χ true) ≫ g) : f = g := by
  let h := isColimitOfPreserves F (Two.fibersIsColimit χ)
  apply h.hom_ext
  rintro ⟨i⟩
  cases i
  · exact h₀
  · exact h₁

theorem map_branch {X Y : C} (χ : X ⟶ Two C) (f g : X ⟶ Y) :
    F.map (Two.branch χ f g) =
      Two.branch (F.map χ ≫ (booleanIso F).hom)
        (F.map f) (F.map g) := by
  have h (b : Bool) :
      F.map (Two.fiberι χ b) ≫ F.map (Two.branch χ f g) =
        F.map (Two.fiberι χ b) ≫
          Two.branch (F.map χ ≫ (booleanIso F).hom)
            (F.map f) (F.map g) := by
    have hb : F.map (Two.fiberι χ b) ≫
        (F.map χ ≫ (booleanIso F).hom) = Two.constant (F.obj (Two.Fiber χ b)) b := by
      rw [← Category.assoc,← Functor.map_comp,Two.fiberι_comp,map_constant]
    rw [← Functor.map_comp,Two.fiberι_branch,Functor.map_comp]
    rw [Two.comp_branch _ _ _ _ b hb]
    cases b <;> rfl
  exact map_hom_ext F χ (h false) (h true)

/-- Every unary Boolean truth table commutes with the Boolean comparison, including
complementation. -/
theorem map_boolean_unary {X : C} (op : Bool → Bool) (f : X ⟶ Two C) :
    F.map (Two.unary op f) ≫ (booleanIso F).hom =
      Two.unary op (F.map f ≫ (booleanIso F).hom) := by
  rw [SyntaxOperationsTransport.boolean_unary_as_branch,map_branch F,SyntaxOperationsTransport.transport_branch_postcomp,
    map_constant F X (op false),map_constant F X (op true)]
  exact (SyntaxOperationsTransport.boolean_unary_as_branch op (F.map f ≫ (booleanIso F).hom)).symm

/-- Every binary Boolean truth table commutes with the Boolean comparison; no chosen codes
for either truth point are used. -/
theorem map_boolean_binary {X : C} (op : Bool → Bool → Bool) (f g : X ⟶ Two C) :
    F.map (Two.binary op f g) ≫ (booleanIso F).hom =
      Two.binary op (F.map f ≫ (booleanIso F).hom)
        (F.map g ≫ (booleanIso F).hom) := by
  rw [SyntaxOperationsTransport.boolean_binary_as_branch,map_branch F,SyntaxOperationsTransport.transport_branch_postcomp,
    map_boolean_unary F (op false) g,map_boolean_unary F (op true) g]
  exact (SyntaxOperationsTransport.boolean_binary_as_branch op (F.map f ≫ (booleanIso F).hom)
    (F.map g ≫ (booleanIso F).hom)).symm


/-- The concrete target equality is the already constructed image of the diagonal square;
no equality-test comparison is a hypothesis. -/
theorem map_decidable_test {V : C} (S : DecidableVariables V) :
    F.map S.test ≫ (Derivation.booleanIso F).hom=
      prodComparison F V V ≫ (Derivation.mappedEquality F S).test := by
  change F.map S.test ≫ (Derivation.booleanIso F).hom=
    prodComparison F V V ≫ (inv (prodComparison F V V) ≫ F.map S.test ≫ (Derivation.booleanIso F).hom)
  simp only [IsIso.hom_inv_id_assoc]
end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ListTransport
