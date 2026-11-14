/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MappedRuleAlgebras
public import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The finite diagrams of first-order inference under change of base -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.FirstOrderRuleTransport

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (G : C ⥤ D) [PreservesFiniteLimits G]
variable {V F L S A : C} (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)

def mappedAll : G.obj V ⨯ G.obj F ⟶ G.obj F :=
  inv (prodComparison G V F) ≫ G.map all

def mappedImp : G.obj F ⨯ G.obj F ⟶ G.obj F :=
  inv (prodComparison G F F) ≫ G.map imp

variable {A' : D} (axioms' : A' ⟶ G.obj S)
variable (k : A' ⟶ G.obj A) (hk : k ≫ G.map axioms = axioms')

/-- The target nullary axiom label is carried into the mapped source label;
the unary and binary rules use the inverse product comparisons. -/
def ruleHom : RulePresentation.Hom
    (firstOrderRules (G.map logical) (G.map sentence) axioms'
      (mappedAll G all) (mappedImp G imp))
    (FiniteRuleTransport.mappedRules G (firstOrderRules logical sentence axioms all imp)) where
  map := Fin.cases
    (coprod.desc (G.map (coprod.inl : L ⟶ L ⨿ A)) (k ≫ G.map coprod.inr))
    (Fin.cases (inv (prodComparison G V F))
      (Fin.cases (inv (prodComparison G F F)) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change inv (prodComparison G V F) ≫
        (G.map (prod.snd : V ⨯ F ⟶ F) ≫ 𝟙 _) = prod.snd
      rw [Category.comp_id, inv_prodComparison_map_snd]
    · change inv (prodComparison G F F) ≫
        (G.map (prod.lift (prod.fst : F ⨯ F ⟶ F) imp) ≫
          (FiniteRuleTransport.powerIso G F 2).hom) =
        prod.lift prod.fst (mappedImp G imp)
      rw [FiniteRuleTransport.powerIso_two]
      have hp : G.map (prod.lift (prod.fst : F ⨯ F ⟶ F) imp) ≫
          prodComparison G F F = prod.lift (G.map (prod.fst : F ⨯ F ⟶ F)) (G.map imp) := by
        apply prod.hom_ext
        · rw [Category.assoc, prodComparison_fst, ← G.map_comp,
            prod.lift_fst, prod.lift_fst]
        · rw [Category.assoc, prodComparison_snd, ← G.map_comp,
            prod.lift_snd, prod.lift_snd]
      rw [hp, prod.comp_lift, inv_prodComparison_map_fst]
      rfl
  conclusion i := by
    fin_cases i
    · change coprod.desc (G.map (coprod.inl : L ⟶ L ⨿ A))
          (k ≫ G.map coprod.inr) ≫ G.map (coprod.desc logical (axioms ≫ sentence)) =
        coprod.desc (G.map logical) (axioms' ≫ G.map sentence)
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc, ← G.map_comp, coprod.inl_desc]
      · rw [coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc, ← G.map_comp,
          coprod.inr_desc, G.map_comp, ← Category.assoc, hk]
    · rfl
    · change inv (prodComparison G F F) ≫ G.map (prod.snd : F ⨯ F ⟶ F) = prod.snd
      exact inv_prodComparison_map_snd G

include hk in
theorem map_closed {M : C} (m : M ⟶ F)
    (hm : ClosedUnder (firstOrderRules logical sentence axioms all imp).inference m) :
    ClosedUnder (firstOrderRules (G.map logical) (G.map sentence) axioms'
      (mappedAll G all) (mappedImp G imp)).inference (G.map m) :=
  FiniteRuleTransport.map_closed_of_rule_hom G _ _
    (ruleHom G logical sentence axioms all imp axioms' k hk) m hm

end CategoricalEssentialIncompleteness.V46.FirstOrderRuleTransport
