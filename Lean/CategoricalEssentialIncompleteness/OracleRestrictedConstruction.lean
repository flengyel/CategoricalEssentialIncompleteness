/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedTuring
public import CategoricalEssentialIncompleteness.OracleRestrictedInclusion
public import CategoricalEssentialIncompleteness.LocalLifting

/-! # The diagonal pair in the oracle-domain category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

variable (S : Set ℕ)
attribute [instance 2000] nativeRestriction

instance restrictionCoproducts : RestrictionCoproducts (Restricted S) where
  total_i0 X Y := totalFromFunction_total (X := X) (Y := coproduct X Y) Sum.inl Computable.sumInl
  total_i1 X Y := totalFromFunction_total (X := Y) (Y := coproduct X Y) Sum.inr Computable.sumInr

theorem rangeFunctor_comparison_hom (X Y : Restricted S) :
    ((rangeFunctor S).comparison X Y).hom=𝟙 _ := comparison_eq_id S X Y

theorem inducedRestriction_eq :
    (PCategory.inducedRestriction : RestrictionCategory (Restricted S))=nativeRestriction := by
  have h : @RestrictionCategory.rst (Restricted S) inferInstance PCategory.inducedRestriction =
      @RestrictionCategory.rst (Restricted S) inferInstance nativeRestriction := by
    funext X Y f
    exact induced_restriction f
  have extR : ∀ R T : RestrictionCategory (Restricted S),
      @RestrictionCategory.rst (Restricted S) inferInstance R =
        @RestrictionCategory.rst (Restricted S) inferInstance T → R=T := by
    intro R T
    cases R
    cases T
    intro he
    cases he
    rfl
  exact extR _ _ h

def parityIso : N S ≅ coprod (N S) (N S) := (codeIso (coproduct (N S) (N S))).symm

theorem parityIso_val : (parityIso S).hom.val=fun (n : ℕ) =>
    Part.some (if n%2=0 then Sum.inl (n/2) else Sum.inr (n/2)) := rfl

/-- A view retaining the exact morphism of the P-category induced idempotent. -/
def fromInduced {X : Restricted S}
    (a : @Idem (Restricted S) inferInstance PCategory.inducedRestriction X) : Idem X :=
  ⟨@Idem.hom _ _ PCategory.inducedRestriction X a,
    (induced_restriction (@Idem.hom _ _ PCategory.inducedRestriction X a)).symm.trans
      (@Idem.restriction _ _ PCategory.inducedRestriction X a)⟩

def pair0 : Idem (N S) :=
  Idem.pull (diagonal (N S) ≫ tau S ≫ (parityIso S).hom) (summand0 (N S) (N S))

def pair1 : Idem (N S) :=
  Idem.pull (diagonal (N S) ≫ tau S ≫ (parityIso S).hom) (summand1 (N S) (N S))

theorem pair0_is_diagonal0 : pair0 S=fromInduced S (diagonal0 (tau S) (parityIso S)) := by
  apply Idem.ext
  simp only [pair0,fromInduced,diagonal0,Idem.pull,Idem.ofRestrict,
    summand0,Idem.sum,Idem.top_hom,Idem.bot_hom]
  exact (induced_restriction _).symm

theorem pair1_is_diagonal1 : pair1 S=fromInduced S (diagonal1 (tau S) (parityIso S)) := by
  apply Idem.ext
  simp only [pair1,fromInduced,diagonal1,Idem.pull,Idem.ofRestrict,
    summand1,Idem.sum,Idem.top_hom,Idem.bot_hom]
  exact (induced_restriction _).symm

theorem support_pull {X Y : Restricted S} (f : X ⟶ Y) (a : Idem Y) :
    support (Idem.pull f a)={x | ∃ y,y ∈ f.val x ∧ y ∈ support a} :=
  PartialFunctions.support_pull f.val (toPfnIdem a)

theorem support_summand0 {X Y : Restricted S} (s : carrier S (coprod X Y)) :
    s ∈ support (summand0 X Y) ↔ ∃ x,s=Sum.inl x := by
  change ((summand0 X Y).hom.val s).Dom ↔ _
  simp only [summand0,Idem.sum_hom,Idem.top_hom,Idem.bot_hom,coprod_map_rawVal,
    id_val,zero_val]
  cases s <;> simp [PartialFunctions.sumMap]

theorem support_summand1 {X Y : Restricted S} (s : carrier S (coprod X Y)) :
    s ∈ support (summand1 X Y) ↔ ∃ y,s=Sum.inr y := by
  change ((summand1 X Y).hom.val s).Dom ↔ _
  simp only [summand1,Idem.sum_hom,Idem.top_hom,Idem.bot_hom,coprod_map_rawVal,
    id_val,zero_val]
  cases s <;> simp [PartialFunctions.sumMap]

theorem support_pair0 (q : ℕ) : q ∈ support (pair0 S) ↔
    oracleDomain S (Nat.unpair q).2 q ∧
      ∃ z,z ∈ ordinaryEval (Nat.unpair q).1 q ∧ z%2=0 := by
  rw [pair0,support_pull]
  change (∃ s,s ∈ (diagonal (N S) ≫ tau S ≫ (parityIso S).hom).val q ∧
    s ∈ support (summand0 (N S) (N S))) ↔ _
  simp only [comp_val,diagonal_val,parityIso_val,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand0]
  change (∃ s,(∃ z : ℕ,z ∈ (tau S).val (q,q) ∧
    s=(if z%2=0 then Sum.inl (z/2) else Sum.inr (z/2))) ∧ ∃ x,s=Sum.inl x) ↔ _
  simp only [mem_tau]
  constructor
  · rintro ⟨s,⟨z,⟨hd,hz⟩,rfl⟩,x,hx⟩
    refine ⟨hd,z,hz,?_⟩
    split_ifs at hx with he <;> omega
  · rintro ⟨hd,z,hz,he⟩
    exact ⟨Sum.inl (z/2),⟨z,⟨hd,hz⟩,by simp [he]⟩,z/2,rfl⟩

theorem support_pair1 (q : ℕ) : q ∈ support (pair1 S) ↔
    oracleDomain S (Nat.unpair q).2 q ∧
      ∃ z,z ∈ ordinaryEval (Nat.unpair q).1 q ∧ z%2=1 := by
  rw [pair1,support_pull]
  change (∃ s,s ∈ (diagonal (N S) ≫ tau S ≫ (parityIso S).hom).val q ∧
    s ∈ support (summand1 (N S) (N S))) ↔ _
  simp only [comp_val,diagonal_val,parityIso_val,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand1]
  change (∃ s,(∃ z : ℕ,z ∈ (tau S).val (q,q) ∧
    s=(if z%2=0 then Sum.inl (z/2) else Sum.inr (z/2))) ∧ ∃ x,s=Sum.inr x) ↔ _
  simp only [mem_tau]
  constructor
  · rintro ⟨s,⟨z,⟨hd,hz⟩,rfl⟩,x,hx⟩
    refine ⟨hd,z,hz,?_⟩
    split_ifs at hx with he <;> omega
  · rintro ⟨hd,z,hz,he⟩
    have hn : z%2≠0 := by omega
    exact ⟨Sum.inr (z/2),⟨z,⟨hd,hz⟩,by simp [hn]⟩,z/2,rfl⟩

theorem mem_range {X Y : Restricted S} (f : X ⟶ Y) (x y : carrier S Y) :
    y ∈ (Ranges.range f).hom.val x ↔ (∃ z,x ∈ f.val z) ∧ y=x :=
  mem_identityOn Y (image f) (image_enumerable f) x y

/-- The image ranges commute with restriction products. -/
theorem range_product {W X Y Z : Restricted S} (f : W ⟶ X) (g : Y ⟶ Z) :
    (Ranges.range (productMap f g)).hom=
      productMap (Ranges.range f).hom (Ranges.range g).hom := by
  apply hom_ext_mem
  intro p q
  rw [mem_range,mem_productMap]
  simp only [mem_range]
  constructor
  · rintro ⟨⟨r,hr⟩,he⟩
    subst q
    obtain ⟨hf,hg⟩ := (mem_productMap f g r p).mp hr
    exact ⟨⟨⟨r.1,hf⟩,rfl⟩,⟨⟨r.2,hg⟩,rfl⟩⟩
  · rintro ⟨⟨⟨x,hx⟩,h0⟩,⟨⟨y,hy⟩,h1⟩⟩
    exact ⟨⟨(x,y),(mem_productMap f g (x,y) p).mpr ⟨hx,hy⟩⟩,Prod.ext h0 h1⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
