/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ClosedTheoryTransfer
public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # Rule comparison with the original calculus through a natural retraction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.RetractedRuleComparison

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (B : C ⥤ D) (E : D ⥤ C) [PreservesFiniteLimits B] [PreservesFiniteLimits E]
variable (e : B ⋙ E ≅ 𝟭 C)

def productBackward (X Y : C) : X ⨯ Y ⟶ E.obj (B.obj X ⨯ B.obj Y) :=
  e.inv.app (X ⨯ Y) ≫ E.map (prodComparison B X Y)

omit [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    [PreservesFiniteLimits E] in
theorem productBackward_fst (X Y : C) :
    productBackward B E e X Y ≫ E.map prod.fst = prod.fst ≫ e.inv.app X := by
  rw [productBackward, Category.assoc, ← E.map_comp, prodComparison_fst]
  exact (e.inv.naturality prod.fst).symm

omit [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    [PreservesFiniteLimits E] in
theorem productBackward_snd (X Y : C) :
    productBackward B E e X Y ≫ E.map prod.snd = prod.snd ≫ e.inv.app Y := by
  rw [productBackward, Category.assoc, ← E.map_comp, prodComparison_snd]
  exact (e.inv.naturality prod.snd).symm

omit [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
    [PreservesFiniteLimits E] in
theorem productBackward_operation {X Y Z : C} (op : X ⨯ Y ⟶ Z) :
    productBackward B E e X Y ≫
      E.map (inv (prodComparison B X Y) ≫ B.map op) = op ≫ e.inv.app Z := by
  rw [productBackward, Category.assoc, ← E.map_comp, IsIso.hom_inv_id_assoc]
  exact (e.inv.naturality op).symm

variable {V F L S : C} (logical : L ⟶ F) (sentence : S ⟶ F)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
variable (W : Subobject (B.obj S)) (A : Subobject S)
variable (k : (A : C) ⟶ E.obj (W : D))
variable (hk : k ≫ E.map W.arrow = A.arrow ≫ e.inv.app S)

/-- The original rules map to evaluated slice rules. The axiom labels may
be arbitrary slice subobjects; no constant-family witness is required. -/
def translation : RulePresentation.Translation (firstOrderRules logical sentence A.arrow all imp)
    (FiniteRuleTransport.mappedRules E
      (firstOrderRules (B.map logical) (B.map sentence) W.arrow
        (FirstOrderRuleTransport.mappedAll B all) (FirstOrderRuleTransport.mappedImp B imp))) where
  formula := e.inv.app F
  map := Fin.cases
    (coprod.desc (e.inv.app L ≫ E.map coprod.inl) (k ≫ E.map coprod.inr))
    (Fin.cases (productBackward B E e V F)
      (Fin.cases (productBackward B E e F F) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change productBackward B E e V F ≫ (E.map prod.snd ≫ 𝟙 _) =
        prod.snd ≫ e.inv.app F
      rw [Category.comp_id]
      exact productBackward_snd B E e V F
    · change productBackward B E e F F ≫
          (E.map (prod.lift prod.fst (FirstOrderRuleTransport.mappedImp B imp)) ≫
            (FiniteRuleTransport.powerIso E (B.obj F) 2).hom) =
        prod.lift prod.fst imp ≫ prod.map (e.inv.app F) (e.inv.app F)
      rw [FiniteRuleTransport.powerIso_two]
      change productBackward B E e F F ≫
          (E.map (prod.lift (prod.fst : B.obj F ⨯ B.obj F ⟶ B.obj F)
            (FirstOrderRuleTransport.mappedImp B imp)) ≫
              prodComparison E (B.obj F) (B.obj F)) =
        prod.lift (prod.fst : F ⨯ F ⟶ F) imp ≫ prod.map (e.inv.app F) (e.inv.app F)
      have hp : E.map (prod.lift (prod.fst : B.obj F ⨯ B.obj F ⟶ B.obj F)
          (FirstOrderRuleTransport.mappedImp B imp)) ≫
          prodComparison E (B.obj F) (B.obj F) =
          prod.lift (E.map prod.fst) (E.map (FirstOrderRuleTransport.mappedImp B imp)) := by
        apply prod.hom_ext
        · rw [Category.assoc, prodComparison_fst, ← E.map_comp,
            prod.lift_fst, prod.lift_fst]
        · rw [Category.assoc, prodComparison_snd, ← E.map_comp,
            prod.lift_snd, prod.lift_snd]
      rw [hp, prod.comp_lift, productBackward_fst]
      dsimp only [FirstOrderRuleTransport.mappedImp]
      rw [productBackward_operation]
      apply prod.hom_ext <;> simp

  conclusion i := by
    fin_cases i
    · change coprod.desc (e.inv.app L ≫ E.map coprod.inl) (k ≫ E.map coprod.inr) ≫
          E.map (coprod.desc (B.map logical) (W.arrow ≫ B.map sentence)) =
        coprod.desc logical (A.arrow ≫ sentence) ≫ e.inv.app F
      apply coprod.hom_ext
      · simp only [coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc, ← E.map_comp]
        exact (e.inv.naturality logical).symm
      · simp only [coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc, ← E.map_comp]
        rw [E.map_comp, ← Category.assoc, hk, Category.assoc]
        exact congrArg (fun f => A.arrow ≫ f) (e.inv.naturality sentence).symm
    · exact productBackward_operation B E e all
    · exact productBackward_snd B E e F F

end CategoricalEssentialIncompleteness.V46.RetractedRuleComparison
