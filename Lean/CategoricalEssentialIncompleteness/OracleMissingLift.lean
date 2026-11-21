/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.OracleRestrictedConstruction
public import CategoricalEssentialIncompleteness.OracleDiagonalSeparator
public import CategoricalEssentialIncompleteness.DisjointJoins

/-! # Complementary separators and the section absent from the source -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted

attribute [instance 2000] nativeRestriction

def separator : Idem (N K) := setIdem (N K) A A_oracle_domains.1
def separatorComplement : Idem (N K) := setIdem (N K) Aᶜ A_oracle_domains.2

theorem separator_complementary : Complementary separator separatorComplement := by
  constructor
  · apply toPfnIdem_injective
    rw [toPfnIdem_inf,toPfnIdem_bot]
    apply PartialFunctions.support_injective
    simp [separator,separatorComplement,PartialFunctions.support_inf]
  · apply toPfnIdem_injective
    rw [toPfnIdem_sup,toPfnIdem_top]
    apply PartialFunctions.support_injective
    simp [separator,separatorComplement,PartialFunctions.support_sup]

theorem pair0_le_separator : pair0 K ≤ separator := by
  apply (support_le_iff _ _).mpr
  intro q hq
  rw [separator,support_setIdem]
  exact ((support_pair0 K q).mp hq).2

theorem pair1_le_separatorComplement : pair1 K ≤ separatorComplement := by
  apply (support_le_iff _ _).mpr
  intro q hq
  rw [separatorComplement,support_setIdem]
  obtain ⟨_,z,hz,he⟩ := (support_pair1 K q).mp hq
  rintro ⟨w,hw,he'⟩
  have hzw : z=w := Part.mem_unique hz hw
  omega

theorem diagonal_pair_separated : ¬ Inseparable (pair0 K) (pair1 K) := by
  intro h
  exact h.no_separator ⟨separator,separatorComplement,separator_complementary,
    pair0_le_separator,pair1_le_separatorComplement⟩

def switchValue (n : ℕ) : ℕ ⊕ ℕ := by
  classical
  exact if n ∈ A then Sum.inr n else Sum.inl n

def missingSection :
    (inclusion K).obj (N K) ⟶ (inclusion K).obj (coprod (N K) (N K)) :=
  fun n => Part.some (switchValue n)

theorem missingSection_total : isTotal missingSection := by
  apply PFun.ext
  intro x y
  change y ∈ rst (C := PartialFunctions.Pfn) missingSection x ↔ y ∈ Part.some x
  simp [PartialFunctions.mem_rst,missingSection]

theorem switchValue_not_computable : ¬ Computable switchValue := by
  intro h
  apply A_not_recursive
  have ht : Computable (fun n => (switchValue n).isRight) := by
    apply (Computable.sumCasesOn h (Computable.const false).to₂
      (Computable.const true).to₂).of_eq
    intro n
    cases switchValue n <;> rfl
  have hd : ComputablePred (fun n => (switchValue n).isRight=true) :=
    ⟨inferInstance,by simpa using ht⟩
  apply hd.of_eq
  intro n
  by_cases hn : n ∈ A <;> simp [switchValue,hn]

/-- No totality assumption on a proposed source lift is used. -/
theorem missingSection_has_no_lift :
    ¬ ∃ l : N K ⟶ coprod (N K) (N K),(inclusion K).map l=missingSection := by
  rintro ⟨l,hl⟩
  have ht : isTotal l := (total_iff l).mpr (by
    intro n
    change (l.val n).Dom
    change l.val=missingSection at hl
    rw [hl]
    exact Part.some_dom _)
  apply switchValue_not_computable
  apply (total_val_partrec l ht).of_eq_tot
  intro n
  change l.val=missingSection at hl
  rw [hl]
  exact Part.mem_some _

theorem missingSection_right :
    ((rangeFunctor K).mapIdem separator).hom ≫ missingSection=
      ((rangeFunctor K).mapIdem separator).hom ≫
        i1 ((inclusion K).obj (N K)) ((inclusion K).obj (N K)) := by
  apply PFun.ext
  intro n y
  change y ∈ (PartialFunctions.partialIdentity _ A n).bind missingSection ↔
    y ∈ (PartialFunctions.partialIdentity _ A n).bind (fun n => Part.some (Sum.inr n))
  simp only [Part.mem_bind_iff,PartialFunctions.mem_identity]
  constructor <;> rintro ⟨x,⟨hx,rfl⟩,hy⟩
  · exact ⟨x,⟨hx,rfl⟩,by simpa [missingSection,switchValue,hx] using hy⟩
  · exact ⟨x,⟨hx,rfl⟩,by simpa [missingSection,switchValue,hx] using hy⟩

theorem missingSection_left :
    ((rangeFunctor K).mapIdem separatorComplement).hom ≫ missingSection=
      ((rangeFunctor K).mapIdem separatorComplement).hom ≫
        i0 ((inclusion K).obj (N K)) ((inclusion K).obj (N K)) := by
  apply PFun.ext
  intro n y
  change y ∈ (PartialFunctions.partialIdentity _ Aᶜ n).bind missingSection ↔
    y ∈ (PartialFunctions.partialIdentity _ Aᶜ n).bind (fun n => Part.some (Sum.inl n))
  simp only [Part.mem_bind_iff,PartialFunctions.mem_identity]
  constructor <;> rintro ⟨x,⟨hx,rfl⟩,hy⟩
  · have hn : x ∉ A := hx
    exact ⟨x,⟨hx,rfl⟩,by simpa [missingSection,switchValue,hn] using hy⟩
  · have hn : x ∉ A := hx
    exact ⟨x,⟨hx,rfl⟩,by simpa [missingSection,switchValue,hn] using hy⟩

theorem missingSection_eq_switchSection : missingSection=
    switchSection ((rangeFunctor K).mapIdem separator)
      ((rangeFunctor K).mapIdem separatorComplement)
      ((rangeFunctor K).map_complementary separator_complementary) := by
  have hs := switchSection_spec ((rangeFunctor K).mapIdem separator)
    ((rangeFunctor K).mapIdem separatorComplement)
    ((rangeFunctor K).map_complementary separator_complementary)
  apply complementary_hom_ext ((rangeFunctor K).map_complementary separator_complementary)
  · exact missingSection_right.trans hs.2.2.1.symm
  · exact missingSection_left.trans hs.2.2.2.symm

def switchProjection : coprod (N K) (N K) ⟶ N K :=
  copair separatorComplement.hom separator.hom

theorem switchProjection_image : (inclusion K).map switchProjection=
    copair ((rangeFunctor K).mapIdem separatorComplement).hom
      ((rangeFunctor K).mapIdem separator).hom := by
  have h := (rangeFunctor K).comparison_copair separatorComplement.hom separator.hom
  rw [rangeFunctor_comparison_hom,Category.id_comp] at h
  exact h

theorem missingSection_is_section :
    SectionOf ((inclusion K).map switchProjection) missingSection := by
  rw [missingSection_eq_switchSection,switchProjection_image]
  exact (switchSection_spec _ _ _).1

theorem missingSection_unique_section (s : (inclusion K).obj (N K) ⟶
    (inclusion K).obj (coprod (N K) (N K)))
    (hs : SectionOf ((inclusion K).map switchProjection) s) : s=missingSection := by
  have hp : PartialMono (copair ((rangeFunctor K).mapIdem separatorComplement).hom
      ((rangeFunctor K).mapIdem separator).hom) :=
    (local_switch ((rangeFunctor K).mapIdem separatorComplement)
    ((rangeFunctor K).mapIdem separator)
    ((rangeFunctor K).map_complementary separator_complementary).symm.disjoint).1
  rw [← switchProjection_image] at hp
  exact hp.section_unique hs missingSection_is_section

theorem specified_switch_has_no_lift : ¬ ∃ l : N K ⟶ coprod (N K) (N K),
    (rangeFunctor K).toFunctor.map l=
      switchSection ((rangeFunctor K).mapIdem separator)
        ((rangeFunctor K).mapIdem separatorComplement)
        ((rangeFunctor K).map_complementary separator_complementary) ≫
          ((rangeFunctor K).comparison (N K) (N K)).hom := by
  rw [rangeFunctor_comparison_hom,Category.comp_id,
    ← missingSection_eq_switchSection]
  exact missingSection_has_no_lift

/-- This is exactly the source-pair lifting premise of the compatible form of the
section-lifting theorem; the partial source lifts are not required to be total. -/
theorem source_section_lifting_fails : ¬ (∀ (c c' : Idem (N K))
    (hc : Complementary c c'),∃ l : N K ⟶ coprod (N K) (N K),
      (rangeFunctor K).toFunctor.map l=
        switchSection ((rangeFunctor K).mapIdem c) ((rangeFunctor K).mapIdem c')
          ((rangeFunctor K).map_complementary hc) ≫
            ((rangeFunctor K).comparison (N K) (N K)).hom) := by
  intro h
  exact specified_switch_has_no_lift (h separator separatorComplement separator_complementary)

def branchA : N K ⟶ coprod (N K) (N K) := separator.hom ≫ i1 (N K) (N K)
def branchComplement : N K ⟶ coprod (N K) (N K) :=
  separatorComplement.hom ≫ i0 (N K) (N K)

theorem branch_restrictions_disjoint :
    Idem.ofRestrict branchA ⊓ Idem.ofRestrict branchComplement=⊥ := by
  have h1 : Idem.ofRestrict branchA=separator := by
    apply Idem.ext
    exact (rst_comp_of_isTotal _ (RestrictionCoproducts.total_i1 _ _)).trans separator.restriction
  have h0 : Idem.ofRestrict branchComplement=separatorComplement := by
    apply Idem.ext
    exact (rst_comp_of_isTotal _ (RestrictionCoproducts.total_i0 _ _)).trans
      separatorComplement.restriction
  rw [h1,h0]
  exact separator_complementary.disjoint

theorem arrowLE_extends {S : Set ℕ} {X Y : Restricted S} {f g : X ⟶ Y}
    (h : ArrowLE f g) : Extends g.val f.val := by
  intro x y hy
  have hm : y ∈ (rst f ≫ g).val x := by
    rw [show rst f ≫ g=f from h]
    exact hy
  obtain ⟨z,hz,hy⟩ := Part.mem_bind_iff.mp hm
  have he : z=x := ((PartialFunctions.mem_rst f.val x z).mp hz).2
  simpa only [he] using hy

theorem branches_have_no_common_upper_bound :
    ¬ ∃ l : N K ⟶ coprod (N K) (N K),ArrowLE branchA l ∧ ArrowLE branchComplement l := by
  rintro ⟨l,hA,hAc⟩
  apply missingSection_has_no_lift
  refine ⟨l,funext (fun n => Part.eq_some_iff.mpr ?_)⟩
  change switchValue n ∈ l.val n
  by_cases hn : n ∈ A
  · apply arrowLE_extends hA n (switchValue n)
    change switchValue n ∈ (separator.hom.val n).bind (fun x => Part.some (Sum.inr x))
    apply Part.mem_bind_iff.mpr
    exact ⟨n,(mem_identityOn (N K) A A_oracle_domains.1 n n).mpr ⟨hn,rfl⟩,
      by simp [switchValue,hn]⟩
  · apply arrowLE_extends hAc n (switchValue n)
    change switchValue n ∈ (separatorComplement.hom.val n).bind (fun x => Part.some (Sum.inl x))
    apply Part.mem_bind_iff.mpr
    exact ⟨n,(mem_identityOn (N K) Aᶜ A_oracle_domains.2 n n).mpr ⟨hn,rfl⟩,
      by simp [switchValue,hn]⟩

theorem no_disjoint_arrow_joins : ¬ DisjointArrowJoins (Restricted K) := by
  intro h
  obtain ⟨l,h1,h0,_⟩ := h.exists_join branchA branchComplement branch_restrictions_disjoint
  exact branches_have_no_common_upper_bound ⟨l,h1,h0⟩

/-- Appendix C, Proposition `prop:missing-lift`. The instances on the literal
`Restricted K` category supply the prodominical recursion, coproduct and range
structure; this theorem records its three claimed failures. -/
theorem missing_lift :
    (∃ c c' : Idem (N K),Complementary c c' ∧ pair0 K ≤ c ∧ pair1 K ≤ c') ∧
    (¬ ∃ l : N K ⟶ coprod (N K) (N K),(inclusion K).map l=missingSection) ∧
    (∃ f g : N K ⟶ coprod (N K) (N K),
      Idem.ofRestrict f ⊓ Idem.ofRestrict g=⊥ ∧
        ¬ ∃ l,ArrowLE f l ∧ ArrowLE g l) :=
  ⟨⟨separator,separatorComplement,separator_complementary,
    pair0_le_separator,pair1_le_separatorComplement⟩,
    missingSection_has_no_lift,
    ⟨branchA,branchComplement,branch_restrictions_disjoint,branches_have_no_common_upper_bound⟩⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted
