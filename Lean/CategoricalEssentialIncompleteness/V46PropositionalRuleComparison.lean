/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInference
public import CategoricalEssentialIncompleteness.V46PropositionalSchemeTransport
public import CategoricalEssentialIncompleteness.V46RetractedClosedTheories

/-! # The three-scheme presentation of Appendix A.6 under change of base -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.PropositionalRuleComparison
open ErasureLogicalSchemes (one two three)

variable {C : Type u₁} [Category.{v₁} C] [Regular C] [FinitaryExtensive C]
variable {S : C} (n : S ⟶ S) (i : S ⨯ S ⟶ S)

abbrev Pair (X : C) := X ⨯ X
abbrev Triple (X : C) := (X ⨯ X) ⨯ X
abbrev Logical (X : C) := (Pair X ⨿ Triple X) ⨿ Pair X

def logical : Logical S ⟶ S := coprod.desc (coprod.desc (one i) (two i)) (three n i)

def rules (A : Subobject S) := ForkInference.rules (coprod.desc (logical n i) A.arrow) i

abbrev Proofs := (A : Subobject S) → Endofunctor.Algebra (rules n i A).inference

def generated (P : Proofs n i) (A : Subobject S) := imageSubobject (P A).a.hom

/-- A general axiom morphism presents its regular image. -/
def generateFrom (P : Proofs n i) {X : C} (a : X ⟶ S) := generated n i P (imageSubobject a)

theorem extensive (P : Proofs n i) (A : Subobject S) : A ≤ generated n i P A := by
  let k := (coprod.inr : (A : C) ⟶ Logical S ⨿ (A : C)) ≫ (rules n i A).nullaryToProof (P A)
  have h : k ≫ (P A).a.hom = A.arrow := by
    dsimp only [k]
    rw [Category.assoc, RulePresentation.nullaryToProof_conclusion]
    exact coprod.inr_desc _ _
  apply Subobject.le_of_comm (k ≫ factorThruImageSubobject (P A).a.hom)
  rw [Category.assoc, imageSubobject_arrow_comp]
  exact h

abbrev Theory (P : Proofs n i) := {A : Subobject S // generated n i P A = A}

variable {D : Type u₂} [Category.{v₂} D] [Regular D] [FinitaryExtensive D]
  (K : C ⥤ D) [PreservesFiniteLimits K] {Y : D}
  (n' : Y ⟶ Y) (i' : Y ⨯ Y ⟶ Y) (σ : Y ⟶ K.obj S)
  (p : Pair Y ⟶ K.obj (Pair S)) (q : Triple Y ⟶ K.obj (Triple S))

def firstLabel (S : C) : Pair S ⟶ Logical S := coprod.inl ≫ coprod.inl
def secondLabel (S : C) : Triple S ⟶ Logical S := coprod.inr ≫ coprod.inl
def thirdLabel (S : C) : Pair S ⟶ Logical S := coprod.inr

@[reassoc (attr := simp)] theorem first_law : firstLabel S ≫ logical n i = one i := by
  simp [firstLabel, logical]
@[reassoc (attr := simp)] theorem second_law : secondLabel S ≫ logical n i = two i := by
  simp [secondLabel, logical]
@[reassoc (attr := simp)] theorem third_law : thirdLabel S ≫ logical n i = three n i := by
  simp [thirdLabel, logical]

def logicalMap : Logical Y ⟶ K.obj (Logical S) :=
  coprod.desc (coprod.desc (p ≫ K.map (firstLabel S)) (q ≫ K.map (secondLabel S)))
    (p ≫ K.map (thirdLabel S))

variable (h₁ : p ≫ K.map (one i) = one i' ≫ σ)
  (h₂ : q ≫ K.map (two i) = two i' ≫ σ)
  (h₃ : p ≫ K.map (three n i) = three n' i' ≫ σ)

omit [PreservesFiniteLimits K] in
include h₁ h₂ h₃ in
theorem logicalMap_law : logicalMap K p q ≫ K.map (logical n i) = logical n' i' ≫ σ := by
  apply coprod.hom_ext
  · apply coprod.hom_ext
    · simpa only [logicalMap, logical, firstLabel, coprod.inl_desc_assoc, coprod.inl_desc,
        Category.assoc, ← K.map_comp] using h₁
    · simpa only [logicalMap, logical, secondLabel, coprod.inr_desc_assoc, coprod.inl_desc_assoc,
        coprod.inr_desc, coprod.inl_desc, Category.assoc, ← K.map_comp] using h₂
  · simpa only [logicalMap, logical, thirdLabel, coprod.inr_desc_assoc, coprod.inr_desc,
      Category.assoc, ← K.map_comp] using h₃

variable (A : Subobject S) (W : Subobject Y) (k : (W : D) ⟶ K.obj (A : C))
  (hk : k ≫ K.map A.arrow = W.arrow ≫ σ)
  (hp : p ≫ K.map (prod.fst : Pair S ⟶ S) = prod.fst ≫ σ)
  (hi : p ≫ K.map i = i' ≫ σ)
  (hr : p ≫ K.map (prod.snd : Pair S ⟶ S) = prod.snd ≫ σ)

/-- The nullary comparison acts on each logical scheme and the axiom subobject.
The unary comparison is unique; the binary one retains the order of the premises. -/
def translation :
    (rules n' i' W).Translation (FiniteRuleTransport.mappedRules K (rules n i A)) where
  formula := σ
  map := Fin.cases (coprod.desc (logicalMap K p q ≫ K.map coprod.inl) (k ≫ K.map coprod.inr))
    (Fin.cases (initial.to _) (Fin.cases p (fun j => Fin.elim0 j)))
  premises j := by
    fin_cases j
    · exact terminal.hom_ext _ _
    · exact initial.hom_ext _ _
    · change p ≫ K.map (prod.lift prod.fst i) ≫ (FiniteRuleTransport.powerIso K S 2).hom =
        prod.lift prod.fst i' ≫ prod.map σ σ
      rw [FiniteRuleTransport.powerIso_two, PropositionalSchemeTransport.map_lift_comparison,
        prod.comp_lift, hp, hi]
      simp
  conclusion j := by
    fin_cases j
    · change coprod.desc _ _ ≫ K.map (coprod.desc (logical n i) A.arrow) =
        coprod.desc (logical n' i') W.arrow ≫ σ
      apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, Category.assoc, ← K.map_comp,
          coprod.inl_desc]
        exact logicalMap_law n i K n' i' σ p q h₁ h₂ h₃
      · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, Category.assoc, ← K.map_comp,
          coprod.inr_desc, hk]
    · exact initial.hom_ext _ _
    · exact hr

/-- Folding derivations bounds their image after the change of formula coordinates. -/
theorem generated_le (P : Proofs n i) (Q : Proofs n' i') (hQ : ∀ W, IsInitial (Q W))
    (τ : (rules n' i' W).Translation (FiniteRuleTransport.mappedRules K (rules n i A))) :
    generated n' i' Q W ≤ (Subobject.pullback τ.formula).obj
      (FiniteLimitSubobjects.object K (generated n i P A)) := by
  let V := FiniteRuleTransport.mappedAlgebra K (rules n i A) (P A)
  have hc : (FiniteLimitSubobjects.object K (generated n i P A)).Factors (K.map (P A).a.hom) := by
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨K.map (factorThruImageSubobject (P A).a.hom) ≫
      (Subobject.underlyingIso (K.map (generated n i P A).arrow)).inv, ?_⟩
    change (_ ≫ (Subobject.underlyingIso _).inv) ≫ (Subobject.mk _).arrow = _
    rw [Category.assoc, Subobject.underlyingIso_arrow, ← K.map_comp]
    exact congrArg K.map (imageSubobject_arrow_comp _)
  have hf := Subobject.factors_of_factors_right (τ.fold (Q W) (hQ W) V) hc
  change (FiniteLimitSubobjects.object K (generated n i P A)).Factors
    (τ.fold (Q W) (hQ W) V ≫ V.a.hom) at hf
  rw [τ.fold_conclusion] at hf
  have ht := pullback_factors τ.formula _ _ hf
  exact imageSubobject_le _ (Subobject.factorThru _ _ ht) (Subobject.factorThru_arrow _ _ ht)

end CategoricalEssentialIncompleteness.V46.PropositionalRuleComparison
