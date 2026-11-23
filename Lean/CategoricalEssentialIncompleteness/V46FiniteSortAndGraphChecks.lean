/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteBooleanPowers
public import CategoricalEssentialIncompleteness.V46FiniteSortPolynomials
public import CategoricalEssentialIncompleteness.V46SelectorGraph

/-! # Boolean powers, change of base and the supplied selector graph -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
universe u v w
section Categorical
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
example (n : ℕ) : IsColimit (Cofan.mk (finitePower (Two D) n) (BooleanPowers.vertex n)) :=
  BooleanPowers.isColimit n
example {n : ℕ} {Y : D} (f g : finitePower (Two D) n ⟶ Y)
    (h : ∀ b : Fin n → Bool, BooleanPowers.vertex n b ≫ f = BooleanPowers.vertex n b ≫ g) :
    f = g := BooleanPowers.vertex_hom_ext n f g h
example {r : ℕ} {I : Type w} (P : D) (c : I → D) (K : Fin r → FiniteSorts.Expression r I) :
    Functor.pi (fun _ : Fin r => constantFamilyFunctor P) ⋙ FiniteSorts.polynomial (constantFamily P ∘ c) K ≅
      FiniteSorts.polynomial c K ⋙ Functor.pi (fun _ : Fin r => constantFamilyFunctor P) :=
  FiniteSorts.sliceComparison P c K
end Categorical

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment FiniteSigmaOne
example {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier)
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (a : M) :
    (finiteMembership (selectedEntry L D)).val.Evalb ![a] ↔
      ∀ i < len a, ∃ j : Fin s, L.val.Evalb ![nth a i, ORingStructure.numeral j.val] ∧
        (D j).val.Evalb ![nth a i] := selected_entries_model L D a
example {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → Carrier) :
    𝗣𝗔 ⊢ finiteMembershipSentence (selectedEntry L D) := selected_entries_PA L D
