/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FirstOrderRuleTransport
public import CategoricalEssentialIncompleteness.V46FiniteLimitSubobjects
public import CategoricalEssentialIncompleteness.V46FirstOrderReflection

/-! # Closed sentence theories under the constructed finite rule comparison -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ClosedTheoryTransfer

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (G : C ⥤ D) [PreservesFiniteLimits G]
variable {V F L S : C} {logical : L ⟶ F} {sentence : S ⟶ F}
variable {all : V ⨯ F ⟶ F} {imp : F ⨯ F ⟶ F}
variable (proofs : (A : Subobject S) →
  Endofunctor.Algebra (firstOrderRules logical sentence A.arrow all imp).inference)
variable (proofInitial : ∀ A, IsInitial (proofs A))
variable (targetProofs : (B : Subobject (G.obj S)) →
  Endofunctor.Algebra (firstOrderRules (G.map logical) (G.map sentence) B.arrow
    (FirstOrderRuleTransport.mappedAll G all) (FirstOrderRuleTransport.mappedImp G imp)).inference)
variable (targetInitial : ∀ B, IsInitial (targetProofs B))

include proofInitial targetInitial in
/-- The target initial derivation algebra folds into the mapped closed
formula image. This gives the direction needed to preserve closed theories. -/
theorem generation_le_image (A : Subobject S) :
    FirstOrderReflection.generated targetProofs (FiniteLimitSubobjects.object G A) ≤
      FiniteLimitSubobjects.object G (FirstOrderReflection.generated proofs A) := by
  let B := FiniteLimitSubobjects.object G A
  let m := image.ι (proofs A).a.hom
  let k := (Subobject.underlyingIso (G.map A.arrow)).hom
  have hk : k ≫ G.map A.arrow = B.arrow := Subobject.underlyingIso_hom_comp_eq_mk _
  have hc : ClosedUnder (firstOrderRules logical sentence A.arrow all imp).inference m :=
    FirstOrderReflection.formula_closed proofs proofInitial A
  have hgm := FirstOrderRuleTransport.map_closed G logical sentence A.arrow all imp
    B.arrow k hk m hc
  obtain ⟨w, hw⟩ := (firstOrder_least_image (G.map logical) (G.map sentence) B.arrow
    (FirstOrderRuleTransport.mappedAll G all) (FirstOrderRuleTransport.mappedImp G imp)
    (targetProofs B) (targetInitial B)).2 (G.map m) hgm
  have hm : imageSubobject (targetProofs B).a.hom ≤ Subobject.mk (G.map m) :=
    Subobject.mk_le_mk_of_comm w hw
  have hb : FirstOrderReflection.generated targetProofs B ≤
      (Subobject.pullback (G.map sentence)).obj (Subobject.mk (G.map m)) := by
    rw [FirstOrderReflection.generated_eq_pullback]
    exact (Subobject.pullback (G.map sentence)).monotone hm
  have he : FiniteLimitSubobjects.object G (FirstOrderReflection.generated proofs A) =
      (Subobject.pullback (G.map sentence)).obj (Subobject.mk (G.map m)) := by
    rw [FirstOrderReflection.generated_eq_pullback, FiniteLimitSubobjects.object_pullback]
    congr 1
    exact FiniteLimitSubobjects.object_mk G m
  exact hb.trans_eq he.symm

include proofInitial targetInitial in
theorem closed_image (A : Subobject S) (hA : FirstOrderReflection.generated proofs A = A) :
    FirstOrderReflection.generated targetProofs (FiniteLimitSubobjects.object G A) =
      FiniteLimitSubobjects.object G A := by
  apply le_antisymm
  · have h := generation_le_image G proofs proofInitial targetProofs targetInitial A
    rwa [hA] at h
  · exact FirstOrderReflection.extensive targetProofs _

/-- The image of a closed theory is closed by the constructed rule-algebra fold, so direct
image defines a functor on the theory categories. -/
def theoryFunctor : FirstOrderReflection.Theory proofs ⥤
    FirstOrderReflection.Theory targetProofs where
  obj T := ⟨FiniteLimitSubobjects.object G T.val,
    closed_image G proofs proofInitial targetProofs targetInitial T.val T.property⟩
  map f := homOfLE (FiniteLimitSubobjects.object_monotone G (leOfHom f))

theorem theoryFunctor_value (T : FirstOrderReflection.Theory proofs) :
    ((theoryFunctor G proofs proofInitial targetProofs targetInitial).obj T).val =
      FiniteLimitSubobjects.object G T.val := rfl

end CategoricalEssentialIncompleteness.V46.ClosedTheoryTransfer
