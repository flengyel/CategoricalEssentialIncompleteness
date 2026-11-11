/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46InferenceFunctor

/-! # Statement checks for the functor of finite derivations -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D] {N : ℕ}
variable (proofs : (R : RuleSystem D N) → Endofunctor.Algebra R.rules.inference)
variable (proofInitial : ∀ R, IsInitial (proofs R))

example : RuleSystem D N ⥤ Arrow D := RuleSystem.derivationFunctor proofs proofInitial

example : RuleSystem.carrierFunctor proofs proofInitial ⟶ RuleSystem.formulaFunctor :=
  RuleSystem.conclusion proofs proofInitial

example {R R' : RuleSystem D N} (τ : R ⟶ R') :
    (RuleSystem.carrierFunctor proofs proofInitial).map τ ≫ (proofs R').a.hom =
      (proofs R).a.hom ≫ τ.formula :=
  (RuleSystem.conclusion proofs proofInitial).naturality τ

example (R : RuleSystem D N) : (𝟙 R : R ⟶ R).formula = 𝟙 R.formula := rfl

example {R R' R'' : RuleSystem D N} (τ : R ⟶ R') (σ : R' ⟶ R'')
    (i : Fin (N + 1)) : (τ ≫ σ).map i = τ.map i ≫ σ.map i := rfl

#print axioms CategoricalEssentialIncompleteness.V46.RuleSystem.derivationFunctor
#print axioms CategoricalEssentialIncompleteness.V46.RuleSystem.carrierFunctor
#print axioms CategoricalEssentialIncompleteness.V46.RuleSystem.conclusion
