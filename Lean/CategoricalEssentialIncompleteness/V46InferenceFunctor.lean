/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46InferenceTranslation
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The functor of initial finite derivations

Rule translations act on finite derivations by their unique folds.
The target arrow category retains the conclusion morphism.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] {N : ℕ}

namespace RulePresentation.Translation

@[ext] theorem ext {F G : D} {R : RulePresentation F N} {R' : RulePresentation G N}
    {τ σ : Translation R R'} (hformula : τ.formula = σ.formula)
    (hmap : ∀ i, τ.map i = σ.map i) : τ = σ := by
  cases τ
  cases σ
  cases hformula
  have h := funext hmap
  cases h
  rfl

end RulePresentation.Translation

/-- A formula object together with its finite ordered rule presentation. -/
structure RuleSystem (D : Type u) [Category.{v} D] [Regular D] (N : ℕ) where
  formula : D
  rules : RulePresentation formula N

namespace RuleSystem

instance : Category.{v} (RuleSystem D N) where
  Hom X Y := RulePresentation.Translation X.rules Y.rules
  id X := RulePresentation.Translation.id X.rules
  comp τ σ := τ.comp σ
  id_comp τ := by
    apply RulePresentation.Translation.ext <;>
      simp [RulePresentation.Translation.comp, RulePresentation.Translation.id]
  comp_id τ := by
    apply RulePresentation.Translation.ext <;>
      simp [RulePresentation.Translation.comp, RulePresentation.Translation.id]
  assoc τ σ ρ := by
    apply RulePresentation.Translation.ext <;>
      simp [RulePresentation.Translation.comp, Category.assoc]

def formulaFunctor : RuleSystem D N ⥤ D where
  obj R := R.formula
  map τ := τ.formula
  map_id _ := rfl
  map_comp _ _ := rfl

variable [HasFiniteCoproducts D]
variable (proofs : (R : RuleSystem D N) → Endofunctor.Algebra R.rules.inference)
variable (proofInitial : ∀ R, IsInitial (proofs R))

/-- The object action is the chosen initial derivation algebra's conclusion.
The morphism action is the proved constructor-preserving translation. -/
def derivationFunctor : RuleSystem D N ⥤ Arrow D where
  obj R := Arrow.mk (proofs R).a.hom
  map {R R'} τ := Arrow.homMk (τ.fold (proofs R) (proofInitial R) (proofs R'))
    τ.formula (τ.fold_conclusion (proofs R) (proofInitial R) (proofs R'))
  map_id R := by
    apply Arrow.hom_ext
    · exact RulePresentation.Translation.fold_id (proofs R) (proofInitial R)
    · rfl
  map_comp {R R' R''} τ σ := by
    apply Arrow.hom_ext
    · exact τ.fold_comp σ (proofs R) (proofInitial R) (proofs R')
        (proofInitial R') (proofs R'')
    · rfl

def carrierFunctor : RuleSystem D N ⥤ D :=
  derivationFunctor proofs proofInitial ⋙ Arrow.leftFunc

/-- Conclusion is natural under the derived translations of finite proofs. -/
def conclusion : carrierFunctor proofs proofInitial ⟶ formulaFunctor where
  app R := (proofs R).a.hom
  naturality {R R'} τ := τ.fold_conclusion (proofs R) (proofInitial R) (proofs R')

end RuleSystem
end CategoricalEssentialIncompleteness.V46
