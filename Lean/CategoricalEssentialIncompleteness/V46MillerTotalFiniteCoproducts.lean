/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalLimits
import CategoricalEssentialIncompleteness.V46MillerTotalCoproducts


/-! # Uniform semidecidable-carrier total splitting: FiniteCoproducts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}

theorem copair_total {X Y Z : (Carrier P)} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hf : isTotal f) (hg : isTotal g) : isTotal (copair f g) := by
  change rst (copair f g)=𝟙 _
  rw [restrict_copair,hf,hg,coprod_id]

def totalCoproduct (X Y : (TotalCategory P)) : (TotalCategory P) := ⟨coproduct X.obj Y.obj⟩
def totalInl (X Y : (TotalCategory P)) : X ⟶ totalCoproduct X Y :=
  ⟨inl X.obj Y.obj,RestrictionCoproducts.total_i0 _ _⟩
def totalInr (X Y : (TotalCategory P)) : Y ⟶ totalCoproduct X Y :=
  ⟨inr X.obj Y.obj,RestrictionCoproducts.total_i1 _ _⟩

def totalCopair {X Y Z : (TotalCategory P)} (f : X ⟶ Z) (g : Y ⟶ Z) : totalCoproduct X Y ⟶ Z :=
  ⟨copair f.hom g.hom,copair_total _ _ f.property g.property⟩

@[simp] theorem totalInl_copair {X Y Z : (TotalCategory P)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    totalInl X Y ≫ totalCopair f g=f := by
  apply WideSubcategory.hom_ext
  exact i0_copair f.hom g.hom

@[simp] theorem totalInr_copair {X Y Z : (TotalCategory P)} (f : X ⟶ Z) (g : Y ⟶ Z) :
    totalInr X Y ≫ totalCopair f g=g := by
  apply WideSubcategory.hom_ext
  exact i1_copair f.hom g.hom

def coproductIsColimit (X Y : (TotalCategory P)) :
    IsColimit (BinaryCofan.mk (totalInl X Y) (totalInr X Y)) :=
  BinaryCofan.isColimitMk (fun s => totalCopair s.inl s.inr)
    (fun _ => totalInl_copair _ _) (fun _ => totalInr_copair _ _) (by
      intro s m hm0 hm1
      apply WideSubcategory.hom_ext
      apply CategoryTheory.HasCoproducts.hom_ext
      · exact congrArg (fun k => k.hom) (hm0.trans (totalInl_copair s.inl s.inr).symm)
      · exact congrArg (fun k => k.hom) (hm1.trans (totalInr_copair s.inl s.inr).symm))

instance totalCoproductHasColimit (X Y : (TotalCategory P)) : HasColimit (Limits.pair X Y) :=
  ⟨⟨_,coproductIsColimit X Y⟩⟩
instance : HasBinaryCoproducts (TotalCategory P) := hasBinaryCoproducts_of_hasColimit_pair (TotalCategory P)

def emptyCarrier : (Carrier P) := ⟨∅,Uniform.Enumerable.of_re (REPred.const False)⟩

theorem empty_zero_eq_id :
    (0 : emptyCarrier (P := P) ⟶ emptyCarrier (P := P))=𝟙 (emptyCarrier (P := P)) := by
  apply val_injective
  apply PFun.ext
  intro x y
  change y ∈ (Part.none : Part ℕ) ↔ y ∈ supportIdentity ∅ x
  simp only [mem_supportIdentity,Set.mem_empty_iff_false,false_and]
  exact ⟨fun h => h.1,False.elim⟩

def initialArrow (X : (TotalCategory P)) : (⟨emptyCarrier⟩ : (TotalCategory P)) ⟶ X :=
  ⟨0,by change rst (0 : emptyCarrier ⟶ X.obj)=𝟙 _
        rw [RestrictionZero.restrict_zero,empty_zero_eq_id]⟩

def initialIsInitial : IsInitial (⟨emptyCarrier⟩ : (TotalCategory P)) :=
  IsInitial.ofUniqueHom initialArrow (by
    intro X f
    apply WideSubcategory.hom_ext
    apply val_ext_on_source
    intro x hx
    exact hx.elim)

instance : HasInitial (TotalCategory P) := initialIsInitial.hasInitial
instance : HasFiniteCoproducts (TotalCategory P) := hasFiniteCoproducts_of_has_binary_and_initial

end CategoricalEssentialIncompleteness.V46.Miller.Total
