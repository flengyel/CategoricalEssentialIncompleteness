/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.TypedTuringMorphism
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
# The typed `P`-recursion category

The nowhere-defined production program supplies zero morphisms in the typed
program category.  Its empty graph is stable under composition and under the
near product, which gives the maintained prodominical structure.

Every coded object is isomorphic to the number object.  The construction is
external induction on `STObjectCode`: product and coproduct isomorphisms are
lifted from the recursive hypotheses and followed by fixed isomorphisms
`omega product omega ≅ omega` and `omega coproduct omega ≅ omega`.  The latter
uses even--odd coding inside arbitrary models of PA.

These structures, together with the previously proved all-object Turing
factorization, give the concrete `PRecursionCategory` instance.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedRecursionCategory

open CodedObjectMembership ConcreteEmptyGraph ConcreteEvaluator ProofSearch
open SigmaOneRealization TypedProgramCategory TypedNearProduct TypedCoproducts
open TypedTuringMorphism UniformIndexQuotient
open PCategoryStruct CoprodStruct CategoryTheory.RecursionCategory

noncomputable section

/-! ## Zero morphisms -/

/-- The typed zero arrow is represented by the concrete nowhere-defined
production program. -/
def zeroArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) : object T Q ⟶ object T R :=
  arrowOfIndex T Q R concreteEmptyIndex

@[simp] theorem zeroArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    (zeroArrow T Q R).1 =
      classOf T (normalizeIndex Q R concreteEmptyIndex) :=
  arrowOfIndex_val T Q R concreteEmptyIndex

/-- The concrete empty index has no graph point in any model of PA. -/
theorem not_eventualGraph_concreteEmptyIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    ¬(eventualGraph concreteEmptyIndex).val.Evalb ![x, y] := by
  have h := consequence_iff.mp (Theory.Proof.sound eventualGraph_empty)
    M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  simpa using (h x y)

/-- Normalizing the empty program between any two coded objects preserves its
exact empty graph in every model of PA. -/
theorem not_eventualGraph_normalize_empty_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (x y : M) :
    ¬(eventualGraph (normalizeIndex Q R concreteEmptyIndex)).val.Evalb
      ![x, y] := by
  rw [eventualGraph_normalizeIndex_eval]
  rintro ⟨-, h, -⟩
  exact not_eventualGraph_concreteEmptyIndex_eval x y h

/-- A normalized empty program followed by any normalized program is uniformly
equal to the appropriately typed empty program. -/
theorem eqIndex_comp_normalize_empty_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (normalizeIndex R S q)
        (normalizeIndex Q R concreteEmptyIndex))
      (normalizeIndex Q S concreteEmptyIndex) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hz, -⟩
    exact False.elim (not_eventualGraph_normalize_empty_eval Q R x z hz)
  · intro h
    exact False.elim (not_eventualGraph_normalize_empty_eval Q S x y h)

/-- Any normalized program followed by a normalized empty program is uniformly
equal to the appropriately typed empty program. -/
theorem eqIndex_comp_normalize_empty_right
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (normalizeIndex R S concreteEmptyIndex)
        (normalizeIndex Q R q))
      (normalizeIndex Q S concreteEmptyIndex) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, -, hz⟩
    exact False.elim (not_eventualGraph_normalize_empty_eval R S z y hz)
  · intro h
    exact False.elim (not_eventualGraph_normalize_empty_eval Q S x y h)

/-- The typed zero absorbs composition on the left. -/
theorem zeroArrow_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R S : STObjectCode} (f : object T R ⟶ object T S) :
    zeroArrow T Q R ≫ f = zeroArrow T Q S := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T R S f
  rw [← hq]
  apply CodedHom.ext
  rw [comp_val, arrowOfIndex_val, zeroArrow_val, zeroArrow_val,
    mul_classOf, classOf_eq_classOf_iff]
  exact eqIndex_comp_normalize_empty_left T Q R S q

/-- The typed zero absorbs composition on the right. -/
theorem comp_zeroArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R S : STObjectCode} (f : object T Q ⟶ object T R) :
    f ≫ zeroArrow T R S = zeroArrow T Q S := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T Q R f
  rw [← hq]
  apply CodedHom.ext
  rw [comp_val, arrowOfIndex_val, zeroArrow_val, zeroArrow_val,
    mul_classOf, classOf_eq_classOf_iff]
  exact eqIndex_comp_normalize_empty_right T Q R S q

/-- Zero morphisms on the typed program category, selected by the concrete
empty production index. -/
instance codedProgramCategoryHasZeroMorphisms
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Limits.HasZeroMorphisms (CodedProgramCategory T) where
  zero := fun Q R => ⟨zeroArrow T (objectCode Q) (objectCode R)⟩
  comp_zero := by
    intro Q R f S
    exact comp_zeroArrow T f
  zero_comp := by
    intro Q R S f
    exact zeroArrow_comp T f

/-- The empty branch used by the coproduct applications is the categorical
zero selected above. -/
@[simp] theorem emptyArrow_eq_zero
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) :
    emptyArrow T Q R = (0 : object T Q ⟶ object T R) :=
  rfl

/-! ## Prodominical absorption -/

/-- Tensoring on the right with a normalized empty program has an empty
normalized graph. -/
theorem eqIndex_normalize_tensor_empty_right
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (A B X Y : STObjectCode) (q : ℕ) :
    EqIndex T
      (normalizeIndex (.product A X) (.product B Y)
        (tensorIndex (normalizeIndex A B q)
          (normalizeIndex X Y concreteEmptyIndex)))
      (normalizeIndex (.product A X) (.product B Y)
        concreteEmptyIndex) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · rw [eventualGraph_normalizeIndex_eval]
    rintro ⟨-, h, -⟩
    obtain ⟨a, b, -, hb, -⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x y).mp h
    exact False.elim
      (not_eventualGraph_normalize_empty_eval X Y (pi₂ x) b hb)
  · intro h
    exact False.elim
      (not_eventualGraph_normalize_empty_eval
        (.product A X) (.product B Y) x y h)

/-- Tensoring on the left with a normalized empty program has an empty
normalized graph. -/
theorem eqIndex_normalize_tensor_empty_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y A B : STObjectCode) (q : ℕ) :
    EqIndex T
      (normalizeIndex (.product X A) (.product Y B)
        (tensorIndex (normalizeIndex X Y concreteEmptyIndex)
          (normalizeIndex A B q)))
      (normalizeIndex (.product X A) (.product Y B)
        concreteEmptyIndex) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · rw [eventualGraph_normalizeIndex_eval]
    rintro ⟨-, h, -⟩
    obtain ⟨a, b, ha, -, -⟩ :=
      (eventualGraph_tensorIndex_eval _ _ x y).mp h
    exact False.elim
      (not_eventualGraph_normalize_empty_eval X Y (pi₁ x) a ha)
  · intro h
    exact False.elim
      (not_eventualGraph_normalize_empty_eval
        (.product X A) (.product Y B) x y h)

/-- The near product absorbs a zero morphism in its right variable. -/
theorem typed_nearProd_zero_right
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {A B X Y : CodedProgramCategory T} (f : A ⟶ B) :
    nearProd_map f (0 : X ⟶ Y) =
      (0 : nearProd A X ⟶ nearProd B Y) := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T (objectCode A) (objectCode B) f
  rw [← hq]
  change nearProd_map
      (arrowOfIndex T (objectCode A) (objectCode B) q)
      (arrowOfIndex T (objectCode X) (objectCode Y) concreteEmptyIndex) =
    arrowOfIndex T (.product (objectCode A) (objectCode X))
      (.product (objectCode B) (objectCode Y)) concreteEmptyIndex
  rw [nearProd_map_arrowOfIndex]
  apply (arrowOfIndex_eq_iff_eqIndex_normalize T _ _ _ _).mpr
  exact eqIndex_normalize_tensor_empty_right T
    (objectCode A) (objectCode B) (objectCode X) (objectCode Y) q

/-- The near product absorbs a zero morphism in its left variable. -/
theorem typed_nearProd_zero_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {A B X Y : CodedProgramCategory T} (f : A ⟶ B) :
    nearProd_map (0 : X ⟶ Y) f =
      (0 : nearProd X A ⟶ nearProd Y B) := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T (objectCode A) (objectCode B) f
  rw [← hq]
  change nearProd_map
      (arrowOfIndex T (objectCode X) (objectCode Y) concreteEmptyIndex)
      (arrowOfIndex T (objectCode A) (objectCode B) q) =
    arrowOfIndex T (.product (objectCode X) (objectCode A))
      (.product (objectCode Y) (objectCode B)) concreteEmptyIndex
  rw [nearProd_map_arrowOfIndex]
  apply (arrowOfIndex_eq_iff_eqIndex_normalize T _ _ _ _).mpr
  exact eqIndex_normalize_tensor_empty_left T
    (objectCode X) (objectCode Y) (objectCode A) (objectCode B) q

/-- The concrete typed program category is prodominical. -/
instance codedProgramCategoryProdominical
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Prodominical (CodedProgramCategory T) where
  nearProd_zero_right := typed_nearProd_zero_right T
  nearProd_zero_left := typed_nearProd_zero_left T

/-! ## Isomorphisms with the number object -/

/-- The near product carries a pair of isomorphisms to an isomorphism. -/
def nearProdIso
    {C : Type*} [Category C] [PCategoryStruct C] [PCategory C]
    {A B X Y : C} (e : A ≅ B) (f : X ≅ Y) :
    nearProd A X ≅ nearProd B Y where
  hom := nearProd_map e.hom f.hom
  inv := nearProd_map e.inv f.inv
  hom_inv_id := by
    rw [PCategory.nearProd_comp]
    simp only [Iso.hom_inv_id]
    exact PCategory.nearProd_id A X
  inv_hom_id := by
    rw [PCategory.nearProd_comp]
    simp only [Iso.inv_hom_id]
    exact PCategory.nearProd_id B Y

/-- The coded coproduct carries a pair of isomorphisms to an isomorphism. -/
def coprodIso
    {C : Type*} [Category C] [CoprodStruct C] [HasCoproducts C]
    {A B X Y : C} (e : A ≅ B) (f : X ≅ Y) :
    coprod A X ≅ coprod B Y where
  hom := coprod_map e.hom f.hom
  inv := coprod_map e.inv f.inv
  hom_inv_id := by
    rw [HasCoproducts.coprod_comp]
    simp only [Iso.hom_inv_id]
    exact HasCoproducts.coprod_id A X
  inv_hom_id := by
    rw [HasCoproducts.coprod_comp]
    simp only [Iso.inv_hom_id]
    exact HasCoproducts.coprod_id B Y

/-! ### The product base isomorphism -/

/-- The identity numerical program, typed from `omega product omega` to
`omega`.  Pairing and unpairing make every internal element a product code. -/
def omegaProductToOmega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T (.product .omega .omega) ⟶ omegaObject T :=
  arrowOfIndex T (.product .omega .omega) .omega Kleene.identityIndex

/-- The identity numerical program, typed from `omega` to
`omega product omega`. -/
def omegaToOmegaProduct
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ object T (.product .omega .omega) :=
  arrowOfIndex T .omega (.product .omega .omega) Kleene.identityIndex

@[simp] theorem omegaProductToOmega_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (omegaProductToOmega T).1 = 1 := by
  change objectIdempotent T .omega * classOf T Kleene.identityIndex *
      objectIdempotent T (.product .omega .omega) = 1
  rw [objectIdempotent_product, objectIdempotent_omega,
    tensorClass_one_one, ← one_eq_classOf]
  simp

@[simp] theorem omegaToOmegaProduct_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (omegaToOmegaProduct T).1 = 1 := by
  change objectIdempotent T (.product .omega .omega) *
      classOf T Kleene.identityIndex * objectIdempotent T .omega = 1
  rw [objectIdempotent_product, objectIdempotent_omega,
    tensorClass_one_one, ← one_eq_classOf]
  simp

/-- The product coding already identifies `omega product omega` with
`omega`; the same numerical identity program represents both directions. -/
def omegaProductIso
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T (.product .omega .omega) ≅ omegaObject T where
  hom := omegaProductToOmega T
  inv := omegaToOmegaProduct T
  hom_inv_id := by
    apply CodedHom.ext
    rw [comp_val, omegaProductToOmega_val, omegaToOmegaProduct_val, id_val]
    change (1 : ProgramQuotient T) * 1 =
      objectIdempotent T (.product .omega .omega)
    rw [
      objectIdempotent_product, objectIdempotent_omega,
      tensorClass_one_one, mul_one]
  inv_hom_id := by
    apply CodedHom.ext
    rw [comp_val, omegaProductToOmega_val, omegaToOmegaProduct_val, id_val]
    change (1 : ProgramQuotient T) * 1 = objectIdempotent T .omega
    rw [
      objectIdempotent_omega, mul_one]

/-! ### The coproduct base isomorphism -/

/-- Even--odd encoding of the two tagged copies of `omega`. -/
def omegaCoprodEncodeGraph : Graph :=
  .mkSigma “x y.
    (∃ a, !natPairFormula.val x a 0 ∧ y = 2 * a) ∨
    (∃ a, !natPairFormula.val x a 1 ∧ y = 2 * a + 1)”

/-- Decoding a number into its quotient and remainder modulo two. -/
def omegaCoprodDecodeGraph : Graph :=
  .mkSigma “x y. ∃ a, ∃ t,
    !divDef.val a x 2 ∧ !remDef.val t x 2 ∧
      !natPairFormula.val y a t”

@[simp] theorem omegaCoprodEncodeGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    omegaCoprodEncodeGraph.val.Evalb ![x, y] ↔
      (∃ a : M, x = pair a 0 ∧ y = 2 * a) ∨
      (∃ a : M, x = pair a 1 ∧ y = 2 * a + 1) := by
  simp [omegaCoprodEncodeGraph]

@[simp] theorem omegaCoprodDecodeGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    omegaCoprodDecodeGraph.val.Evalb ![x, y] ↔
      y = pair (x / 2) (x % 2) := by
  simp [omegaCoprodDecodeGraph]

theorem omegaCoprodEncodeGraph_functional :
    Functional omegaCoprodEncodeGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rcases omegaCoprodEncodeGraph_eval x y |>.mp hy with
      ⟨a, hxa, hya⟩ | ⟨a, hxa, hya⟩ <;>
    rcases omegaCoprodEncodeGraph_eval x z |>.mp hz with
      ⟨b, hxb, hzb⟩ | ⟨b, hxb, hzb⟩
  · have hab : a = b :=
      (pair_eq_pair_iff a 0 b 0).mp (hxa.symm.trans hxb) |>.1
    exact hya.trans (congrArg (fun u : M => 2 * u) hab) |>.trans hzb.symm
  · have h01 : (0 : M) = 1 :=
      (pair_eq_pair_iff a 0 b 1).mp (hxa.symm.trans hxb) |>.2
    exact False.elim (zero_ne_one h01)
  · have h10 : (1 : M) = 0 :=
      (pair_eq_pair_iff a 1 b 0).mp (hxa.symm.trans hxb) |>.2
    exact False.elim (Arithmetic.one_ne_zero h10)
  · have hab : a = b :=
      (pair_eq_pair_iff a 1 b 1).mp (hxa.symm.trans hxb) |>.1
    exact hya.trans (congrArg (fun u : M => 2 * u + 1) hab) |>.trans hzb.symm

theorem omegaCoprodDecodeGraph_functional :
    Functional omegaCoprodDecodeGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact (omegaCoprodDecodeGraph_eval x y).mp hy |>.trans
    ((omegaCoprodDecodeGraph_eval x z).mp hz).symm

/-- A selected production index for even--odd encoding. -/
def omegaCoprodEncodeIndex : ℕ :=
  Classical.choose
    (realize_graph omegaCoprodEncodeGraph omegaCoprodEncodeGraph_functional)

/-- A selected production index for quotient--remainder decoding. -/
def omegaCoprodDecodeIndex : ℕ :=
  Classical.choose
    (realize_graph omegaCoprodDecodeGraph omegaCoprodDecodeGraph_functional)

theorem omegaCoprodEncodeIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph omegaCoprodEncodeIndex)
      omegaCoprodEncodeGraph :=
  Classical.choose_spec
    (realize_graph omegaCoprodEncodeGraph omegaCoprodEncodeGraph_functional)

theorem omegaCoprodDecodeIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph omegaCoprodDecodeIndex)
      omegaCoprodDecodeGraph :=
  Classical.choose_spec
    (realize_graph omegaCoprodDecodeGraph omegaCoprodDecodeGraph_functional)

@[simp] theorem eventualGraph_omegaCoprodEncodeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph omegaCoprodEncodeIndex).val.Evalb ![x, y] ↔
      (∃ a : M, x = pair a 0 ∧ y = 2 * a) ∨
      (∃ a : M, x = pair a 1 ∧ y = 2 * a + 1) := by
  have h := consequence_iff.mp
    (Theory.Proof.sound omegaCoprodEncodeIndex_uniform) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (omegaCoprodEncodeGraph_eval x y)

@[simp] theorem eventualGraph_omegaCoprodDecodeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph omegaCoprodDecodeIndex).val.Evalb ![x, y] ↔
      y = pair (x / 2) (x % 2) := by
  have h := consequence_iff.mp
    (Theory.Proof.sound omegaCoprodDecodeIndex_uniform) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (omegaCoprodDecodeGraph_eval x y)

@[simp] theorem eventualGraph_normalize_omegaCoprodEncodeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph (normalizeIndex (.coproduct .omega .omega) .omega
      omegaCoprodEncodeIndex)).val.Evalb ![x, y] ↔
      (memberFormula (.coproduct .omega .omega)).val.Evalb ![x] ∧
        ((∃ a : M, x = pair a 0 ∧ y = 2 * a) ∨
         (∃ a : M, x = pair a 1 ∧ y = 2 * a + 1)) := by
  rw [eventualGraph_normalizeIndex_eval]
  simp only [eventualGraph_omegaCoprodEncodeIndex_eval,
    memberFormula_omega_eval, and_true]

@[simp] theorem eventualGraph_normalize_omegaCoprodDecodeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x y : M) :
    (eventualGraph (normalizeIndex .omega (.coproduct .omega .omega)
      omegaCoprodDecodeIndex)).val.Evalb ![x, y] ↔
      y = pair (x / 2) (x % 2) ∧
        (memberFormula (.coproduct .omega .omega)).val.Evalb ![y] := by
  rw [eventualGraph_normalizeIndex_eval]
  simp only [eventualGraph_omegaCoprodDecodeIndex_eval,
    memberFormula_omega_eval, true_and]

/-- Decoding after even--odd encoding is the selected partial identity of the
tagged double copy of `omega`, uniformly over `T`. -/
theorem eqIndex_omegaCoprod_encode_decode
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex
        (normalizeIndex .omega (.coproduct .omega .omega)
          omegaCoprodDecodeIndex)
        (normalizeIndex (.coproduct .omega .omega) .omega
          omegaCoprodEncodeIndex))
      (deltaIndex (.coproduct .omega .omega)) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval, eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨z, hencode, hdecode⟩
    obtain ⟨hx, hencode⟩ :=
      (eventualGraph_normalize_omegaCoprodEncodeIndex_eval x z).mp hencode
    obtain ⟨hdecode, -⟩ :=
      (eventualGraph_normalize_omegaCoprodDecodeIndex_eval z y).mp hdecode
    refine ⟨hx, ?_⟩
    rcases hencode with ⟨a, hxa, hza⟩ | ⟨a, hxa, hza⟩
    · subst x
      subst z
      simpa using hdecode
    · subst x
      subst z
      simpa using hdecode
  · rintro ⟨hx, hyx⟩
    subst y
    rcases (memberFormula_coproduct_eval .omega .omega x).mp hx with
        ⟨a, hxa, -⟩ | ⟨a, hxa, -⟩
    · subst x
      refine ⟨2 * a, ?_, ?_⟩
      · apply (eventualGraph_normalize_omegaCoprodEncodeIndex_eval
          (pair a 0) (2 * a)).mpr
        exact ⟨hx, Or.inl ⟨a, rfl, rfl⟩⟩
      · apply (eventualGraph_normalize_omegaCoprodDecodeIndex_eval
          (2 * a) (pair a 0)).mpr
        exact ⟨by simp, hx⟩
    · subst x
      refine ⟨2 * a + 1, ?_, ?_⟩
      · apply (eventualGraph_normalize_omegaCoprodEncodeIndex_eval
          (pair a 1) (2 * a + 1)).mpr
        exact ⟨hx, Or.inr ⟨a, rfl, rfl⟩⟩
      · apply (eventualGraph_normalize_omegaCoprodDecodeIndex_eval
          (2 * a + 1) (pair a 1)).mpr
        exact ⟨by simp, hx⟩

/-- Even--odd encoding after quotient--remainder decoding is the selected
identity of `omega`, uniformly over `T`. -/
theorem eqIndex_omegaCoprod_decode_encode
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T
      (compIndex
        (normalizeIndex (.coproduct .omega .omega) .omega
          omegaCoprodEncodeIndex)
        (normalizeIndex .omega (.coproduct .omega .omega)
          omegaCoprodDecodeIndex))
      (deltaIndex .omega) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval, eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨z, hdecode, hencode⟩
    obtain ⟨hz, -⟩ :=
      (eventualGraph_normalize_omegaCoprodDecodeIndex_eval x z).mp hdecode
    obtain ⟨-, hencode⟩ :=
      (eventualGraph_normalize_omegaCoprodEncodeIndex_eval z y).mp hencode
    refine ⟨memberFormula_omega_eval x, ?_⟩
    subst z
    rcases hencode with ⟨a, hpair, hya⟩ | ⟨a, hpair, hya⟩
    · obtain ⟨ha, hmod⟩ :=
        (pair_eq_pair_iff (x / 2) (x % 2) a 0).mp hpair
      calc
        y = 2 * a := hya
        _ = 2 * (x / 2) := congrArg (fun u : M => 2 * u) ha.symm
        _ = 2 * (x / 2) + (x % 2) := by rw [hmod]; simp
        _ = x := div_add_mod x 2
    · obtain ⟨ha, hmod⟩ :=
        (pair_eq_pair_iff (x / 2) (x % 2) a 1).mp hpair
      calc
        y = 2 * a + 1 := hya
        _ = 2 * (x / 2) + 1 :=
          congrArg (fun u : M => 2 * u + 1) ha.symm
        _ = 2 * (x / 2) + (x % 2) := by rw [hmod]
        _ = x := div_add_mod x 2
  · rintro ⟨-, hyx⟩
    subst y
    rcases mod_two x with hmod | hmod
    · have hmember :
          (memberFormula (.coproduct .omega .omega)).val.Evalb
            ![pair (x / 2) (x % 2)] := by
        rw [hmod, memberFormula_coproduct_left_pair_eval]
        exact memberFormula_omega_eval _
      refine ⟨pair (x / 2) (x % 2), ?_, ?_⟩
      · exact (eventualGraph_normalize_omegaCoprodDecodeIndex_eval
          x (pair (x / 2) (x % 2))).mpr ⟨rfl, hmember⟩
      · apply (eventualGraph_normalize_omegaCoprodEncodeIndex_eval
          (pair (x / 2) (x % 2)) x).mpr
        refine ⟨hmember, Or.inl ⟨x / 2, ?_, ?_⟩⟩
        · rw [hmod]
        · simpa [hmod] using (div_add_mod x 2).symm
    · have hmember :
          (memberFormula (.coproduct .omega .omega)).val.Evalb
            ![pair (x / 2) (x % 2)] := by
        rw [hmod, memberFormula_coproduct_right_pair_eval]
        exact memberFormula_omega_eval _
      refine ⟨pair (x / 2) (x % 2), ?_, ?_⟩
      · exact (eventualGraph_normalize_omegaCoprodDecodeIndex_eval
          x (pair (x / 2) (x % 2))).mpr ⟨rfl, hmember⟩
      · apply (eventualGraph_normalize_omegaCoprodEncodeIndex_eval
          (pair (x / 2) (x % 2)) x).mpr
        refine ⟨hmember, Or.inr ⟨x / 2, ?_, ?_⟩⟩
        · rw [hmod]
        · simpa [hmod] using (div_add_mod x 2).symm

/-- The even--odd encoder as a typed arrow. -/
def omegaCoprodToOmega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T (.coproduct .omega .omega) ⟶ omegaObject T :=
  arrowOfIndex T (.coproduct .omega .omega) .omega
    omegaCoprodEncodeIndex

/-- The quotient--remainder decoder as a typed arrow. -/
def omegaToOmegaCoprod
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    omegaObject T ⟶ object T (.coproduct .omega .omega) :=
  arrowOfIndex T .omega (.coproduct .omega .omega)
    omegaCoprodDecodeIndex

@[simp] theorem omegaCoprodToOmega_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (omegaCoprodToOmega T).1 =
      classOf T (normalizeIndex (.coproduct .omega .omega) .omega
        omegaCoprodEncodeIndex) :=
  arrowOfIndex_val T _ _ _

@[simp] theorem omegaToOmegaCoprod_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (omegaToOmegaCoprod T).1 =
      classOf T (normalizeIndex .omega (.coproduct .omega .omega)
        omegaCoprodDecodeIndex) :=
  arrowOfIndex_val T _ _ _

/-- The even--odd bijection is an isomorphism from the tagged double copy of
`omega` to `omega` in the uniform provability quotient. -/
def omegaCoprodIso
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T (.coproduct .omega .omega) ≅ omegaObject T where
  hom := omegaCoprodToOmega T
  inv := omegaToOmegaCoprod T
  hom_inv_id := by
    apply CodedHom.ext
    rw [comp_val, omegaCoprodToOmega_val, omegaToOmegaCoprod_val,
      mul_classOf, id_val]
    change classOf T
        (compIndex
          (normalizeIndex .omega (.coproduct .omega .omega)
            omegaCoprodDecodeIndex)
          (normalizeIndex (.coproduct .omega .omega) .omega
            omegaCoprodEncodeIndex)) =
      classOf T (deltaIndex (.coproduct .omega .omega))
    exact (classOf_eq_classOf_iff T _ _).mpr
      (eqIndex_omegaCoprod_encode_decode T)
  inv_hom_id := by
    apply CodedHom.ext
    rw [comp_val, omegaCoprodToOmega_val, omegaToOmegaCoprod_val,
      mul_classOf, id_val]
    change classOf T
        (compIndex
          (normalizeIndex (.coproduct .omega .omega) .omega
            omegaCoprodEncodeIndex)
          (normalizeIndex .omega (.coproduct .omega .omega)
            omegaCoprodDecodeIndex)) =
      classOf T (deltaIndex .omega)
    exact (classOf_eq_classOf_iff T _ _).mpr
      (eqIndex_omegaCoprod_decode_encode T)

/-! ### External induction over coded objects -/

/-- Every externally given coded object is isomorphic to `omega`.  The
induction is over object syntax; the base inverse equations above are proved
internally in arbitrary models of PA. -/
def isoToOmega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (Q : STObjectCode) → object T Q ≅ omegaObject T
  | .omega => Iso.refl _
  | .product Q R =>
      (nearProdIso (isoToOmega T Q) (isoToOmega T R)).trans
        (omegaProductIso T)
  | .coproduct Q R =>
      (coprodIso (isoToOmega T Q) (isoToOmega T R)).trans
        (omegaCoprodIso T)

/-- Any two coded objects are isomorphic by passing through `omega`. -/
instance codedProgramCategoryIsotype
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Isotype (CodedProgramCategory T) where
  iso X Y :=
    ⟨(isoToOmega T (objectCode X)).trans
      (isoToOmega T (objectCode Y)).symm⟩

/-! ## The concrete recursion-category instance -/

/-- The typed program category is a `P`-recursion category.  Its distinguished
objects are all `omega`, and its Turing morphism is the previously accepted
fixed evaluator. -/
instance codedProgramCategoryPRecursionCategory
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PRecursionCategory (CodedProgramCategory T) where
  W := omegaObject T
  X := omegaObject T
  Y := omegaObject T
  tau := typedTau T
  is_turing := typedTau_isTuringMorphism T

/-! ## Focused applications -/

/-- A nested coproduct--product object is concretely isomorphic to `omega`. -/
def nestedObjectIsoToOmega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    object T (.product (.coproduct .omega .omega) .omega) ≅
      omegaObject T :=
  isoToOmega T (.product (.coproduct .omega .omega) .omega)

/-- The Turing arrow packaged by the recursion-category instance is exactly
the previously constructed typed Turing arrow. -/
@[simp] theorem codedProgramCategory_tau
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    PRecursionCategory.tau (C := CodedProgramCategory T) = typedTau T :=
  rfl

/-- The packaged Turing property is the accepted all-object factorization
theorem, without a repeated compiler or parameterization proof. -/
theorem codedProgramCategory_tau_isTuringMorphism
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsTuringMorphism
      (PRecursionCategory.tau (C := CodedProgramCategory T)) := by
  simpa only [codedProgramCategory_tau] using
    (typedTau_isTuringMorphism T)

end

end FailureOfComposition.TypedRecursionCategory
