/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding

/-! # Model values of the recursive exponential object coding -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.TypedNearProduct FailureOfComposition.TypedCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46

namespace CategoricalEssentialIncompleteness.V46.PrintedObjectCoding

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The manuscript's recursive numerical coding, interpreted in an arbitrary
model of PA. -/
def value : (Q : STObjectCode) → SyntacticModel.interpretedType M Q → M
  | .omega, x => x
  | .product Q R, x => ExponentialPairing.code (value Q x.1) (value R x.2)
  | .coproduct Q _, .inl x => 2 * value Q x
  | .coproduct _ R, .inr x => 2 * value R x + 1

theorem tensor_relation (q r : ProgramQuotient T) (x u y v : M) :
    SyntacticModel.programRelation T M (tensorClass T q r) (Arithmetic.pair x u)
        (Arithmetic.pair y v) ↔
      SyntacticModel.programRelation T M q x y ∧
        SyntacticModel.programRelation T M r u v := by
  induction q, r using Quotient.inductionOn₂ with
  | _ q r => exact eventualGraph_tensorIndex_pair_eval q r x u y v

theorem coproduct_relation (q r : ProgramQuotient T) (x y : M) :
    SyntacticModel.programRelation T M (coprodClass T q r) x y ↔
      (∃ a b : M, x = Arithmetic.pair a 0 ∧ y = Arithmetic.pair b 0 ∧
        SyntacticModel.programRelation T M q a b) ∨
      (∃ a b : M, x = Arithmetic.pair a 1 ∧ y = Arithmetic.pair b 1 ∧
        SyntacticModel.programRelation T M r a b) := by
  induction q, r using Quotient.inductionOn₂ with
  | _ q r => exact eventualGraph_coprodIndex_eval q r x y

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem relation_comp {Q R S : CodedProgramCategory T} (f : Q ⟶ R) (g : R ⟶ S)
    {x y z : M} (hf : SyntacticModel.programRelation T M f.val x y)
    (hg : SyntacticModel.programRelation T M g.val y z) :
    SyntacticModel.programRelation T M (f ≫ g).val x z := by
  rw [comp_val, SyntacticModel.programRelation_mul]
  exact ⟨y, hf, hg⟩

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem inverse_relation {Q R : CodedProgramCategory T} (e : Q ≅ R) (x y : M) :
    SyntacticModel.programRelation T M e.inv.val y x ↔
      SyntacticModel.programRelation T M e.hom.val x y := by
  suffices forward : ∀ {Q R : CodedProgramCategory T} (e : Q ≅ R) (x y : M),
      SyntacticModel.programRelation T M e.hom.val x y →
        SyntacticModel.programRelation T M e.inv.val y x from
    ⟨forward e.symm y x, forward e x y⟩
  intro Q R e x y h
  have hid : SyntacticModel.programRelation T M (e.hom ≫ e.inv).val x x := by
    rw [e.hom_inv_id, id_val, SyntacticModel.object_relation]
    exact ⟨SyntacticModel.arrow_source T M e.hom h, rfl⟩
  rw [comp_val, SyntacticModel.programRelation_mul] at hid
  obtain ⟨z, hz, hiz⟩ := hid
  have he := SyntacticModel.programRelation_functional T M e.hom.val x z y hz h
  exact he ▸ hiz

theorem omegaProduct_value : (omegaProductIso T).hom.val = encodeProgram T := by
  change (omegaCodeIso T).hom.val * (TypedRecursionCategory.omegaProductIso T).hom.val = _
  change encodeProgram T * (TypedRecursionCategory.omegaProductToOmega T).val = _
  rw [TypedRecursionCategory.omegaProductToOmega_val, mul_one]

/-- The actual quotient-program isomorphism realizes every recursive coding
clause, including arbitrary nonstandard entries of products and sums. -/
theorem value_model (Q : STObjectCode) (x : SyntacticModel.interpretedType M Q) :
    SyntacticModel.programRelation T M (isoToOmega T Q).hom.val
      (SyntacticModel.codingEquiv T M Q x).val (value M Q x) := by
  induction Q with
  | omega =>
      change SyntacticModel.programRelation T M (𝟙 (omegaObject T) : omegaObject T ⟶ omegaObject T).val x x
      rw [id_val, SyntacticModel.object_relation]
      exact ⟨memberFormula_omega_eval (M := M) x, rfl⟩
  | product Q R hQ hR =>
      obtain ⟨x, u⟩ := x
      let a := value M Q x
      let b := value M R u
      apply relation_comp T M
        (PCategoryStruct.nearProd_map (isoToOmega T Q).hom (isoToOmega T R).hom)
        (omegaProductIso T).hom
      · change SyntacticModel.programRelation T M
          (tensorClass T (isoToOmega T Q).hom.val (isoToOmega T R).hom.val)
          (Arithmetic.pair (SyntacticModel.codingEquiv T M Q x).val
            (SyntacticModel.codingEquiv T M R u).val) (Arithmetic.pair a b)
        exact (tensor_relation T M _ _ _ _ _ _).mpr ⟨hQ x, hR u⟩
      · rw [omegaProduct_value, encodeProgram_model]
        exact ⟨a, b, rfl, rfl⟩
  | coproduct Q R hQ hR =>
      cases x with
      | inl x =>
          apply relation_comp T M
            (CoprodStruct.coprod_map (isoToOmega T Q).hom (isoToOmega T R).hom)
            (TypedRecursionCategory.omegaCoprodIso T).hom
          · change SyntacticModel.programRelation T M
              (coprodClass T (isoToOmega T Q).hom.val (isoToOmega T R).hom.val)
              (Arithmetic.pair (SyntacticModel.codingEquiv T M Q x).val 0)
              (Arithmetic.pair (value M Q x) 0)
            exact (coproduct_relation T M _ _ _ _).mpr (Or.inl ⟨_, _, rfl, rfl, hQ x⟩)
          · change SyntacticModel.programRelation T M
              (TypedRecursionCategory.omegaCoprodToOmega T).val _ _
            rw [TypedRecursionCategory.omegaCoprodToOmega_val,
              SyntacticModel.programRelation_class,
              TypedRecursionCategory.eventualGraph_normalize_omegaCoprodEncodeIndex_eval]
            exact ⟨(memberFormula_coproduct_left_pair_eval .omega .omega _).mpr
              (memberFormula_omega_eval _), Or.inl ⟨_, rfl, rfl⟩⟩
      | inr x =>
          apply relation_comp T M
            (CoprodStruct.coprod_map (isoToOmega T Q).hom (isoToOmega T R).hom)
            (TypedRecursionCategory.omegaCoprodIso T).hom
          · change SyntacticModel.programRelation T M
              (coprodClass T (isoToOmega T Q).hom.val (isoToOmega T R).hom.val)
              (Arithmetic.pair (SyntacticModel.codingEquiv T M R x).val 1)
              (Arithmetic.pair (value M R x) 1)
            exact (coproduct_relation T M _ _ _ _).mpr (Or.inr ⟨_, _, rfl, rfl, hR x⟩)
          · change SyntacticModel.programRelation T M
              (TypedRecursionCategory.omegaCoprodToOmega T).val _ _
            rw [TypedRecursionCategory.omegaCoprodToOmega_val,
              SyntacticModel.programRelation_class,
              TypedRecursionCategory.eventualGraph_normalize_omegaCoprodEncodeIndex_eval]
            exact ⟨(memberFormula_coproduct_right_pair_eval .omega .omega _).mpr
              (memberFormula_omega_eval _), Or.inr ⟨_, rfl, rfl⟩⟩

theorem inverse_value_model (Q : STObjectCode) (x : SyntacticModel.interpretedType M Q)
    (y : M) :
    SyntacticModel.programRelation T M (isoToOmega T Q).inv.val (value M Q x) y ↔
      y = (SyntacticModel.codingEquiv T M Q x).val := by
  have h := (inverse_relation T M (isoToOmega T Q) _ _).mpr (value_model T M Q x)
  exact ⟨fun hy => SyntacticModel.programRelation_functional T M _ _ _ _ hy h,
    fun he => he.symm ▸ h⟩

include T in
theorem value_bijective (Q : STObjectCode) : Function.Bijective (value M Q) := by
  constructor
  · intro x y he
    have hx := (inverse_value_model T M Q x _).mpr rfl
    have hy := (inverse_value_model T M Q y _).mpr rfl
    rw [← he] at hy
    have hc := SyntacticModel.programRelation_functional T M _ _ _ _ hx hy
    apply (SyntacticModel.codingEquiv T M Q).injective
    exact Subtype.ext hc
  · intro y
    let e := isoToOmega T Q
    have hid : SyntacticModel.programRelation T M (e.inv ≫ e.hom).val y y := by
      rw [e.inv_hom_id, id_val, SyntacticModel.object_relation]
      exact ⟨memberFormula_omega_eval y, rfl⟩
    rw [comp_val, SyntacticModel.programRelation_mul] at hid
    obtain ⟨x, hi, hh⟩ := hid
    let u : SyntacticModel.carrier M Q := ⟨x, SyntacticModel.arrow_target T M e.inv hi⟩
    let a := (SyntacticModel.codingEquiv T M Q).symm u
    have ha := value_model T M Q a
    have hcode : (SyntacticModel.codingEquiv T M Q a).val = x :=
      congrArg Subtype.val ((SyntacticModel.codingEquiv T M Q).apply_symm_apply u)
    rw [hcode] at ha
    exact ⟨a, SyntacticModel.programRelation_functional T M _ _ _ _ ha hh⟩

/-- The recursive gamma map is a bijection on the entire interpreted carrier. -/
def valueEquiv (Q : STObjectCode) : SyntacticModel.interpretedType M Q ≃ M :=
  Equiv.ofBijective (value M Q) (value_bijective T M Q)

/-- Conjugation by the constructed program isomorphisms compares the original
typed graphs with their interpretation in the manuscript's numerical codes. -/
theorem comparison_model {Q R : CodedProgramCategory T} (f : Q ⟶ R)
    (x : SyntacticModel.interpretedType M (objectCode Q))
    (y : SyntacticModel.interpretedType M (objectCode R)) :
    SyntacticModel.programRelation T M ((comparison T).map f).hom.val
        (value M (objectCode Q) x) (value M (objectCode R) y) ↔
      SyntacticModel.programRelation T M f.val
        (SyntacticModel.codingEquiv T M (objectCode Q) x).val
        (SyntacticModel.codingEquiv T M (objectCode R) y).val := by
  change SyntacticModel.programRelation T M
    ((isoToOmega T (objectCode Q)).inv ≫ f ≫ (isoToOmega T (objectCode R)).hom).val _ _ ↔ _
  rw [comp_val, SyntacticModel.programRelation_mul]
  constructor
  · rintro ⟨a, ha, hb⟩
    have he := (inverse_value_model T M (objectCode Q) x a).mp ha
    subst a
    rw [comp_val, SyntacticModel.programRelation_mul] at hb
    obtain ⟨b, hf, hh⟩ := hb
    have hi := (inverse_relation T M (isoToOmega T (objectCode R)) _ _).mpr hh
    have he := (inverse_value_model T M (objectCode R) y b).mp hi
    exact he ▸ hf
  · intro hf
    refine ⟨_, (inverse_value_model T M (objectCode Q) x _).mpr rfl, ?_⟩
    rw [comp_val, SyntacticModel.programRelation_mul]
    exact ⟨_, hf, value_model T M (objectCode R) y⟩

end CategoricalEssentialIncompleteness.V46.PrintedObjectCoding
