/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteRuleTransport

/-! # Constructed rule algebras on images under finite-limit preservation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FiniteRuleTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (G : C ⥤ D) [PreservesFiniteLimits G] {F : C} {N : ℕ}
variable (R : RulePresentation F N)

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
theorem inverse_conclusion (Q : Over F) (i : Fin (N + 1)) :
    (ruleObjectIso G R Q i).inv ≫ G.map (R.ruleConclusion Q i) =
      (mappedRules G R).ruleConclusion ((Over.post G).obj Q) i := by
  rw [← ruleObjectIso_conclusion G R Q i, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Each target premise tuple is carried back through the proved pullback
comparison and then evaluated by the original rule algebra. -/
def mappedStructure (Q : Over F) (α : R.inference.obj Q ⟶ Q) :
    (mappedRules G R).inference.obj ((Over.post G).obj Q) ⟶ (Over.post G).obj Q :=
  Over.homMk (Sigma.desc (fun i => (ruleObjectIso G R Q i).inv ≫
    G.map (Sigma.ι (R.ruleObject Q) i ≫ α.left))) (by
      change Sigma.desc (fun i => (ruleObjectIso G R Q i).inv ≫
          G.map (Sigma.ι (R.ruleObject Q) i ≫ α.left)) ≫ G.map Q.hom =
        Sigma.desc ((mappedRules G R).ruleConclusion ((Over.post G).obj Q))
      apply Sigma.hom_ext
      intro i
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      have hc : (Sigma.ι (R.ruleObject Q) i ≫ α.left) ≫ Q.hom = R.ruleConclusion Q i := by
        rw [Category.assoc, Over.w α]
        exact Sigma.ι_comp_desc _ _
      rw [Category.assoc, ← G.map_comp, hc]
      exact inverse_conclusion G R Q i)

def mappedAlgebra (A : Endofunctor.Algebra R.inference) :
    Endofunctor.Algebra (mappedRules G R).inference :=
  ⟨(Over.post G).obj A.a, mappedStructure G R A.a A.str⟩

include G in
theorem map_closed {M : C} (m : M ⟶ F) (hm : ClosedUnder R.inference m) :
    ClosedUnder (mappedRules G R).inference (G.map m) := by
  obtain ⟨α⟩ := hm
  exact ⟨mappedStructure G R (Over.mk m) α⟩

/-- A target rule presentation may change instance labels by a proved
premise-and-conclusion-preserving morphism. Its closure structure is
constructed by composing that morphism with the mapped algebra. -/
theorem map_closed_of_rule_hom (R' : RulePresentation (G.obj F) N)
    (ι : RulePresentation.Hom R' (mappedRules G R))
    {M : C} (m : M ⟶ F) (hm : ClosedUnder R.inference m) :
    ClosedUnder R'.inference (G.map m) := by
  obtain ⟨α⟩ := hm
  exact ⟨ι.inferenceTransformation.app (Over.mk (G.map m)) ≫
    mappedStructure G R (Over.mk m) α⟩

end CategoricalEssentialIncompleteness.V46.FiniteRuleTransport
