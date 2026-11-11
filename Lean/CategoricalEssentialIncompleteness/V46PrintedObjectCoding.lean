/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialProducts
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction
public import FailureOfComposition.TypedRecursionCategory
public import Mathlib.CategoryTheory.InducedCategory

/-! # Formal object codes with exponential products -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.CodedObjectMembership
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.PrintedObjectCoding

abbrev Number : Carrier := memberFormula .omega
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem predicateClass_one (C : Carrier)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M), C.val.Evalb ![x]) :
    predicateClass T C = 1 := by
  apply programClass_ext T
  intro M _ _ x y
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [predicateClass_model, ← objectIdempotent_omega T, SyntacticModel.object_relation]
  simp only [h M x, memberFormula_omega_eval, true_and]

theorem raw_full (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) :
    (productCarrier Number Number).val.Evalb ![x] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  exact (productCarrier_eval Number Number x).mpr
    ⟨π₁ x, π₂ x, (pair_unpair x).symm, memberFormula_omega_eval _, memberFormula_omega_eval _⟩

theorem exponential_full (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) :
    (ExponentialProducts.carrier Number Number).val.Evalb ![x] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  obtain ⟨a, b, hx⟩ := ExponentialPairing.code_surjective x
  exact (ExponentialProducts.carrier_eval Number Number x).mpr
    ⟨a, b, hx, memberFormula_omega_eval _, memberFormula_omega_eval _⟩

def encodeProgram : ProgramQuotient T := (ExponentialProducts.encode T Number Number).programClass
def decodeProgram : ProgramQuotient T := (ExponentialProducts.decode T Number Number).programClass

theorem decode_encode : decodeProgram T * encodeProgram T = 1 := by
  let C : PredicateCategory T := productCarrier Number Number
  let D : PredicateCategory T := ExponentialProducts.carrier Number Number
  let e : (realization T).obj C ≅ (realization T).obj D :=
    (realization T).mapIso (ExponentialProducts.rawProductIso T Number Number)
  have h := e.hom_inv_id
  have hv := congrArg (fun f : (realization T).obj C ⟶ (realization T).obj C =>
    f.hom.hom.val) h
  change decodeProgram T * encodeProgram T = predicateClass T C at hv
  rw [predicateClass_one T C (raw_full T)] at hv
  exact hv

theorem encode_decode : encodeProgram T * decodeProgram T = 1 := by
  let C : PredicateCategory T := ExponentialProducts.carrier Number Number
  let D : PredicateCategory T := productCarrier Number Number
  let e : (realization T).obj D ≅ (realization T).obj C :=
    (realization T).mapIso (ExponentialProducts.rawProductIso T Number Number)
  have h := e.inv_hom_id
  have hv := congrArg (fun f : (realization T).obj C ⟶ (realization T).obj C =>
    f.hom.hom.val) h
  change encodeProgram T * decodeProgram T = predicateClass T C at hv
  rw [predicateClass_one T C (exponential_full T)] at hv
  exact hv

/-- Exponential and square codes are compared by actual inverse program
classes on the original number object. -/
def omegaCodeIso : omegaObject T ≅ omegaObject T where
  hom := omegaArrow T (encodeProgram T)
  inv := omegaArrow T (decodeProgram T)
  hom_inv_id := by
    apply CodedHom.ext
    rw [comp_val, omegaArrow_val, omegaArrow_val, id_val]
    change decodeProgram T * encodeProgram T = objectIdempotent T .omega
    rw [objectIdempotent_omega]
    exact decode_encode T
  inv_hom_id := by
    apply CodedHom.ext
    rw [comp_val, omegaArrow_val, omegaArrow_val, id_val]
    change encodeProgram T * decodeProgram T = objectIdempotent T .omega
    rw [objectIdempotent_omega]
    exact encode_decode T

def omegaProductIso : object T (.product .omega .omega) ≅ omegaObject T :=
  TypedRecursionCategory.omegaProductIso T ≪≫ omegaCodeIso T

theorem encodeProgram_model (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x y : M) :
    SyntacticModel.programRelation T M (encodeProgram T) x y ↔
      ∃ a b : M, x = Arithmetic.pair a b ∧ y = ExponentialPairing.code a b := by
  unfold encodeProgram
  rw [GraphMorphism.programClass_model]
  change (ExponentialProducts.encodeGraph Number Number).val.Evalb ![x, y] ↔ _
  simpa only [Number, memberFormula_omega_eval, true_and] using
    ExponentialProducts.encodeGraph_eval Number Number x y

theorem decodeProgram_model (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (x y : M) :
    SyntacticModel.programRelation T M (decodeProgram T) x y ↔
      ∃ a b : M, x = ExponentialPairing.code a b ∧ y = Arithmetic.pair a b := by
  unfold decodeProgram
  rw [GraphMorphism.programClass_model]
  change (ExponentialProducts.decodeGraph Number Number).val.Evalb ![x, y] ↔ _
  simpa only [Number, memberFormula_omega_eval, and_true] using
    ExponentialProducts.decodeGraph_eval Number Number x y

/-- The formal product step uses exponential pairing, and the formal
sum step uses the existing even/odd coding isomorphism. -/
def isoToOmega : (Q : STObjectCode) → object T Q ≅ omegaObject T
  | .omega => Iso.refl _
  | .product Q R =>
      TypedRecursionCategory.nearProdIso (isoToOmega Q) (isoToOmega R) ≪≫ omegaProductIso T
  | .coproduct Q R =>
      TypedRecursionCategory.coprodIso (isoToOmega Q) (isoToOmega R) ≪≫
        TypedRecursionCategory.omegaCoprodIso T

/-- Every formal label has the same full numerical carrier; its
morphisms are the original quotient programs on omega. -/
abbrev NormalizedCategory :=
  InducedCategory (CodedProgramCategory T) (fun _ : STObjectCode => omegaObject T)

instance normalizedRestriction : RestrictionCategory (NormalizedCategory T) where
  rst f := InducedCategory.homMk (rst f.hom)
  rst_comp_self f := by
    apply InducedCategory.hom_ext
    exact rst_comp_self f.hom
  rst_comm f g := by
    apply InducedCategory.hom_ext
    exact rst_comm f.hom g.hom
  rst_comp_rst f g := by
    apply InducedCategory.hom_ext
    exact rst_comp_rst f.hom g.hom
  rst_comp f g := by
    apply InducedCategory.hom_ext
    exact rst_comp f.hom g.hom

/-- A morphism at any pair of formal labels is exactly an unguarded
quotient program on the full numerical carrier. -/
def homProgramEquiv (Q R : NormalizedCategory T) : (Q ⟶ R) ≃ ProgramQuotient T where
  toFun f := f.hom.val
  invFun a := InducedCategory.homMk (omegaArrow T a)
  left_inv f := by
    apply InducedCategory.hom_ext
    apply CodedHom.ext
    rfl
  right_inv a := rfl

def comparison : CodedProgramCategory T ⥤ NormalizedCategory T where
  obj Q := objectCode Q
  map {Q R} f := InducedCategory.homMk
    ((isoToOmega T (objectCode Q)).inv ≫ f ≫ (isoToOmega T (objectCode R)).hom)
  map_id Q := by
    apply InducedCategory.hom_ext
    change (isoToOmega T (objectCode Q)).inv ≫
      (𝟙 (object T (objectCode Q))) ≫ (isoToOmega T (objectCode Q)).hom = 𝟙 _
    rw [Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by
    apply InducedCategory.hom_ext
    simp [Category.assoc]

instance comparison_faithful : (comparison T).Faithful where
  map_injective {Q R} f g h := by
    have hh := congrArg (fun k : (comparison T).obj Q ⟶ (comparison T).obj R =>
      (isoToOmega T (objectCode Q)).hom ≫ k.hom ≫ (isoToOmega T (objectCode R)).inv) h
    simpa [comparison, Category.assoc] using hh

instance comparison_full : (comparison T).Full where
  map_surjective {Q R} f := by
    refine ⟨(isoToOmega T (objectCode Q)).hom ≫ f.hom ≫
      (isoToOmega T (objectCode R)).inv, ?_⟩
    apply InducedCategory.hom_ext
    simp [comparison, Category.assoc]

instance comparison_essSurj : (comparison T).EssSurj := by
  constructor
  intro Q
  exact ⟨object T Q, ⟨Iso.refl Q⟩⟩

instance comparison_isEquivalence : (comparison T).IsEquivalence := {}

def equivalence : CodedProgramCategory T ≌ NormalizedCategory T :=
  (comparison T).asEquivalence

theorem preserves_restrictions {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (comparison T).map (rst f) = rst ((comparison T).map f) := by
  apply InducedCategory.hom_ext
  change (isoToOmega T (objectCode Q)).inv ≫ rst f ≫
      (isoToOmega T (objectCode Q)).hom =
    rst ((isoToOmega T (objectCode Q)).inv ≫ f ≫ (isoToOmega T (objectCode R)).hom)
  symm
  simpa only [Iso.symm_hom, Iso.symm_inv, Category.assoc] using
    LocalConnectedness.V46.restriction_conjugate
      (isoToOmega T (objectCode Q)).symm f (isoToOmega T (objectCode R))

theorem inverse_preserves_restrictions {Q R : NormalizedCategory T} (f : Q ⟶ R) :
    (equivalence T).inverse.map (rst f) = rst ((equivalence T).inverse.map f) :=
  by
    have hE : ∀ {X Y : CodedProgramCategory T} (g : X ⟶ Y),
        (equivalence T).functor.map (rst g) = rst ((equivalence T).functor.map g) := by
      intro X Y g
      change (comparison T).map (rst g) = rst ((comparison T).map g)
      exact preserves_restrictions T g
    exact LocalConnectedness.V46.equivalence_inverse_preserves (equivalence T) hE f

end CategoricalEssentialIncompleteness.V46.PrintedObjectCoding
