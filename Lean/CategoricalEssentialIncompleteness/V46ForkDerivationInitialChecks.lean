/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInitial


/-! # Initiality on the natural fork of finite derivations -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks
example (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a.left = (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) := rfl
example (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a.hom =
      (⟨ForkSyntax.conclusion a b,ForkSyntax.conclusion_total a b⟩ :
        (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) ⟶ (⟨ForkSyntax.S⟩ : EffectiveFork.Total)) := rfl
example (a b : Idem EffectiveFork.V) : IsInitial (inferenceAlgebra a b) := inferenceInitial a b
example (a b : Idem EffectiveFork.V) : IsInitial (printedAlgebra a b) := printedInitial a b
example (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).str =
      (inferenceIso a b).inv.app (proofSlice a b) ≫ (inferenceAlgebra a b).str :=
  printed_constructor a b
example (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (inferenceAlgebra a b).str.left ≫ (componentProofIso a b j).hom =
      (componentInputIso a b (proofSlice a b) j).hom ≫
        ((nativeRules a b j).inference.map (componentProofSliceIso a b j).hom).left ≫
          (nativeAlgebra a b j).str.left := component_inferenceConstructor_native a b j
example (a b : Idem EffectiveFork.V) (Q : EffectiveFork.Total) (q : Q ⟶ sentenceObject)
    (η : (printedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : proofSlice a b ⟶ Over.mk q,
      (printedH a b).map u ≫ η = (printedAlgebra a b).str ≫ u := printed_unique a b Q q η
example (a b : Idem EffectiveFork.V) : proofSlice a b =
    Over.mk (⟨ForkSyntax.conclusion a b,ForkSyntax.conclusion_total a b⟩ :
      (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) ⟶ (⟨ForkSyntax.S⟩ : EffectiveFork.Total)) := rfl
example (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference) :
    foldCarrier a b B ≫ B.a.hom =
      (⟨ForkSyntax.conclusion a b,ForkSyntax.conclusion_total a b⟩ :
        (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) ⟶ (⟨ForkSyntax.S⟩ : EffectiveFork.Total)) :=
  fold_conclusion a b B
example (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference)
    (m : inferenceAlgebra a b ⟶ B) : m = foldHom a b B := fold_unique a b B m
end CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks
