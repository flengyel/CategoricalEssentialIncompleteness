/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.PartialFunctions
import FailureOfComposition.TypedChoice

/-! # Interpretation of uniformly provable program graphs in arithmetic models

Programs are identified by one universally quantified graph equality proved
in the theory. All semantic quantifiers range over the complete model carrier.
The coded numerical types are interpreted as their arithmetic membership
subsets in that carrier.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition
open FailureOfComposition.CodedObjectMembership FailureOfComposition.TypedProgramCategory
open FailureOfComposition.UniformIndexQuotient FailureOfComposition.ProofSearch
open FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

open PartialFunctions
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

private theorem modelPA (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
  models_of_subtheory (U := T) inferInstance

omit [𝗣𝗔 ⪯ T] in
theorem uniform_model {F G : Graph} (h : Uniform T F G) (x y : M) :
    F.val.Evalb ![x, y] ↔ G.val.Evalb ![x, y] := by
  have hm := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
  rw [models_iff, uniformSentence_eval] at hm
  exact hm x y

/-- Interpretation of a quotient program's graph. -/
def programRelation (q : ProgramQuotient T) : M → M → Prop :=
  Quotient.lift (fun n x y => (eventualGraph n).val.Evalb ![x, y]) (by
    intro q r h
    funext x y
    exact propext (uniform_model T M h x y)) q

@[simp] theorem programRelation_class (q : ℕ) (x y : M) :
    programRelation T M (classOf T q) x y ↔ (eventualGraph q).val.Evalb ![x, y] := Iff.rfl

theorem programRelation_functional (q : ProgramQuotient T) (x y z : M)
    (hy : programRelation T M q x y) (hz : programRelation T M q x z) : y = z := by
  let := modelPA T M
  induction q using Quotient.inductionOn with
  | _ q => exact eventualGraph_output_unique q x y z hy hz

theorem programRelation_mul (q r : ProgramQuotient T) (x z : M) :
    programRelation T M (q * r) x z ↔
      ∃ y : M, programRelation T M r x y ∧ programRelation T M q y z := by
  let := modelPA T M
  induction q, r using Quotient.inductionOn₂ with
  | _ q r => exact eventualGraph_comp_eval q r x z

/-- The coded interpretation of a numerical type. -/
def carrier (Q : STObjectCode) := {x : M // (memberFormula Q).val.Evalb ![x]}

@[simp] theorem object_relation (Q : STObjectCode) (x y : M) :
    programRelation T M (objectIdempotent T Q) x y ↔
      (memberFormula Q).val.Evalb ![x] ∧ y = x := by
  let := modelPA T M
  exact eventualGraph_deltaIndex_eval Q x y

theorem arrow_source {Q R : CodedProgramCategory T} (f : Q ⟶ R) {x y : M}
    (h : programRelation T M f.val x y) : (memberFormula (objectCode Q)).val.Evalb ![x] := by
  have he := f.property.2
  have hm : programRelation T M (f.val * objectIdempotent T (objectCode Q)) x y := by
    rw [he]; exact h
  obtain ⟨z, hz, _⟩ := (programRelation_mul T M _ _ x y).mp hm
  exact ((object_relation T M _ x z).mp hz).1

theorem arrow_target {Q R : CodedProgramCategory T} (f : Q ⟶ R) {x y : M}
    (h : programRelation T M f.val x y) : (memberFormula (objectCode R)).val.Evalb ![y] := by
  have he := f.property.1
  have hm : programRelation T M (objectIdempotent T (objectCode R) * f.val) x y := by
    rw [he]; exact h
  obtain ⟨z, _, hz⟩ := (programRelation_mul T M _ _ x y).mp hm
  obtain ⟨hz, heq⟩ := (object_relation T M _ z y).mp hz
  exact heq ▸ hz

/-- The interpreted partial function is defined precisely when the graph
has an output in the model. -/
def arrow {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    PartialFun.of (carrier M (objectCode Q)) ⟶ PartialFun.of (carrier M (objectCode R)) :=
  fun x => ⟨∃ y : carrier M (objectCode R), programRelation T M f.val x.val y.val,
    fun h => Classical.choose h⟩

@[simp] theorem mem_arrow {Q R : CodedProgramCategory T} (f : Q ⟶ R)
    (x : carrier M (objectCode Q)) (y : carrier M (objectCode R)) :
    y ∈ arrow T M f x ↔ programRelation T M f.val x.val y.val := by
  constructor
  · intro h
    obtain ⟨hd, he⟩ := Part.mem_mk_iff.mp h
    have hs := Classical.choose_spec hd
    rwa [he] at hs
  · intro h
    have hd : ∃ z : carrier M (objectCode R), programRelation T M f.val x.val z.val := ⟨y, h⟩
    apply Part.mem_mk_iff.mpr
    refine ⟨hd, ?_⟩
    apply Subtype.ext
    exact programRelation_functional T M f.val x.val _ y.val (Classical.choose_spec hd) h

/-- The covariant interpretation functor on the existing uniform program
category. -/
def functor : CodedProgramCategory T ⥤ Pfn where
  obj Q := PartialFun.of (carrier M (objectCode Q))
  map f := arrow T M f
  map_id Q := by
    apply PFun.ext
    intro x y
    rw [mem_arrow, id_val, object_relation, mem_id]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨x.property, congrArg Subtype.val h⟩⟩
  map_comp f g := by
    apply PFun.ext
    intro x z
    rw [mem_arrow, comp_val, programRelation_mul, mem_comp]
    constructor
    · rintro ⟨y, hf, hg⟩
      exact ⟨⟨y, arrow_target T M f hf⟩, (mem_arrow T M f x _).mpr hf,
        (mem_arrow T M g _ z).mpr hg⟩
    · rintro ⟨y, hf, hg⟩
      exact ⟨y.val, (mem_arrow T M f x y).mp hf, (mem_arrow T M g y z).mp hg⟩

@[simp] theorem mem_map_index (Q R : STObjectCode) (q : ℕ)
    (x : carrier M Q) (y : carrier M R) :
    y ∈ (functor T M).map (arrowOfIndex T Q R q) x ↔
      (eventualGraph q).val.Evalb ![x.val, y.val] := by
  let := modelPA T M
  change y ∈ arrow T M (arrowOfIndex T Q R q) x ↔ _
  rw [mem_arrow, arrowOfIndex_val, programRelation_class,
    eventualGraph_normalizeIndex_eval]
  exact ⟨fun h => h.2.1, fun h => ⟨x.property, h, y.property⟩⟩

theorem map_restriction {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (functor T M).map (CategoryTheory.RestrictionCategory.rst f) =
      CategoryTheory.RestrictionCategory.rst ((functor T M).map f) := by
  let := modelPA T M
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  apply PFun.ext
  intro x y
  rw [TypedNearProduct.restrictionCategory_rst_arrowOfIndex, mem_map_index,
    TypedNearProduct.eventualGraph_restrictionIndex_eval, mem_rst]
  simp only [eventualGraph_normalizeIndex_eval]
  constructor
  · rintro ⟨heq, z, _, hq, hz⟩
    exact ⟨⟨⟨z, hz⟩, (mem_map_index T M _ _ q x _).mpr hq⟩, Subtype.ext heq⟩
  · rintro ⟨⟨z, hz⟩, heq⟩
    exact ⟨congrArg Subtype.val heq, z.val, x.property,
      (mem_map_index T M _ _ q x z).mp hz, z.property⟩

theorem map_range {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (functor T M).map (Ranges.range f).hom =
      (Ranges.range ((functor T M).map f)).hom := by
  let := modelPA T M
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  change (functor T M).map (HasRanges.ran (arrowOfIndex T _ _ q)) = _
  apply PFun.ext
  intro y z
  rw [TypedRanges.ran_arrowOfIndex, mem_map_index,
    TypedRanges.eventualGraph_typedRangeIndex_normalized_eval, mem_range]
  constructor
  · rintro ⟨heq, _, x, hx, hq⟩
    exact ⟨⟨⟨x, hx⟩, (mem_map_index T M _ _ q _ y).mpr hq⟩, Subtype.ext heq.symm⟩
  · rintro ⟨⟨x, hx⟩, heq⟩
    exact ⟨(congrArg Subtype.val heq).symm, y.property, x.val, x.property,
      (mem_map_index T M _ _ q x y).mp hx⟩

theorem map_zero (Q R : CodedProgramCategory T) :
    (functor T M).map (0 : Q ⟶ R) = 0 := by
  let := modelPA T M
  change (functor T M).map (arrowOfIndex T (objectCode Q) (objectCode R)
    ConcreteEmptyGraph.concreteEmptyIndex) = _
  apply PFun.ext
  intro x y
  rw [mem_map_index, mem_zero]
  exact iff_false_intro (TypedRecursionCategory.not_eventualGraph_concreteEmptyIndex_eval _ _)

def sumCoding (Q R : STObjectCode) : carrier M Q ⊕ carrier M R → carrier M (.coproduct Q R) := by
  letI := modelPA T M
  exact Sum.elim
    (fun x => ⟨pair x.val 0, (memberFormula_coproduct_left_pair_eval Q R x.val).mpr x.property⟩)
    (fun y => ⟨pair y.val 1, (memberFormula_coproduct_right_pair_eval Q R y.val).mpr y.property⟩)

theorem sumCoding_bijective (Q R : STObjectCode) : Function.Bijective (sumCoding T M Q R) := by
  let := modelPA T M
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext ((pair_eq_pair_iff _ _ _ _).mp he).1)
      | inr y => exact False.elim (zero_ne_one ((pair_eq_pair_iff _ _ _ _).mp he).2)
    | inr x =>
      cases y with
      | inl y => exact False.elim (Arithmetic.one_ne_zero ((pair_eq_pair_iff _ _ _ _).mp he).2)
      | inr y => exact congrArg Sum.inr (Subtype.ext ((pair_eq_pair_iff _ _ _ _).mp he).1)
  · intro z
    rcases (memberFormula_coproduct_eval Q R z.val).mp z.property with
      ⟨x, hx, hQ⟩ | ⟨y, hy, hR⟩
    · exact ⟨Sum.inl ⟨x, hQ⟩, Subtype.ext hx.symm⟩
    · exact ⟨Sum.inr ⟨y, hR⟩, Subtype.ext hy.symm⟩

def sumEquiv (Q R : STObjectCode) :
    carrier M Q ⊕ carrier M R ≃ carrier M (.coproduct Q R) :=
  Equiv.ofBijective (sumCoding T M Q R) (sumCoding_bijective T M Q R)

theorem comparison_eq_sumIso (Q R : CodedProgramCategory T) :
    coproductComparison (functor T M) Q R =
      (PartialFun.Iso.mk (sumEquiv T M (objectCode Q) (objectCode R))).hom := by
  let := modelPA T M
  apply PFun.ext
  intro s z
  cases s with
  | inl x =>
    change z ∈ copair ((functor T M).map (i0 Q R))
      ((functor T M).map (i1 Q R)) (Sum.inl x) ↔ _
    rw [copair_inl]
    change z ∈ (functor T M).map (arrowOfIndex T (objectCode Q)
      (.coproduct (objectCode Q) (objectCode R)) (TypedCoproducts.leftInjectionIndex _)) x ↔ _
    rw [mem_map_index,
      TypedCoproducts.eventualGraph_leftInjectionIndex_eval]
    change (_ ∧ z.val = pair x.val 0) ↔ z ∈ Part.some (sumCoding T M _ _ (Sum.inl x))
    rw [Part.mem_some_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨x.property, congrArg Subtype.val h⟩⟩
  | inr y =>
    change z ∈ copair ((functor T M).map (i0 Q R))
      ((functor T M).map (i1 Q R)) (Sum.inr y) ↔ _
    rw [copair_inr]
    change z ∈ (functor T M).map (arrowOfIndex T (objectCode R)
      (.coproduct (objectCode Q) (objectCode R)) (TypedCoproducts.rightInjectionIndex _)) y ↔ _
    rw [mem_map_index,
      TypedCoproducts.eventualGraph_rightInjectionIndex_eval]
    change (_ ∧ z.val = pair y.val 1) ↔ z ∈ Part.some (sumCoding T M _ _ (Sum.inr y))
    rw [Part.mem_some_iff]
    exact ⟨fun h => Subtype.ext h.2, fun h => ⟨y.property, congrArg Subtype.val h⟩⟩

/-- The model interpretation preserves the exact structures required in
Theorem 6.3, including the canonical coproduct comparison. -/
def rangeFunctor : RangeFunctor (CodedProgramCategory T) Pfn where
  toFunctor := functor T M
  map_restrict := map_restriction T M
  map_range := map_range T M
  map_zero := map_zero T M
  comparison_isIso Q R := by rw [comparison_eq_sumIso]; infer_instance

def productCoding (Q R : STObjectCode) :
    carrier M Q × carrier M R → carrier M (.product Q R) := by
  letI := modelPA T M
  exact fun x => ⟨pair x.1.val x.2.val,
    (memberFormula_product_pair_eval Q R _ _).mpr ⟨x.1.property, x.2.property⟩⟩

theorem productCoding_bijective (Q R : STObjectCode) :
    Function.Bijective (productCoding T M Q R) := by
  let := modelPA T M
  constructor
  · intro x y h
    have he := (pair_eq_pair_iff _ _ _ _).mp (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext he.1) (Subtype.ext he.2)
  · intro z
    obtain ⟨x, y, he, hx, hy⟩ := (memberFormula_product_eval Q R z.val).mp z.property
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), Subtype.ext he.symm⟩

def productEquiv (Q R : STObjectCode) :
    carrier M Q × carrier M R ≃ carrier M (.product Q R) :=
  Equiv.ofBijective (productCoding T M Q R) (productCoding_bijective T M Q R)

/-- The precise product graph equation, including simultaneous
definedness, under the canonical arithmetic coding comparison. -/
theorem map_product_graph (Q R S V : STObjectCode) (q r : ℕ)
    (x : carrier M Q) (u : carrier M S) (y : carrier M R) (v : carrier M V) :
    productCoding T M R V (y, v) ∈
      (functor T M).map (PCategoryStruct.nearProd_map
        (arrowOfIndex T Q R q) (arrowOfIndex T S V r)) (productCoding T M Q S (x, u)) ↔
      y ∈ (functor T M).map (arrowOfIndex T Q R q) x ∧
      v ∈ (functor T M).map (arrowOfIndex T S V r) u := by
  let := modelPA T M
  rw [TypedNearProduct.nearProd_map_arrowOfIndex, mem_map_index, mem_map_index, mem_map_index]
  change (eventualGraph (TypedNearProduct.tensorIndex
      (normalizeIndex Q R q) (normalizeIndex S V r))).val.Evalb
      ![pair x.val u.val, pair y.val v.val] ↔ _
  rw [TypedNearProduct.eventualGraph_tensorIndex_pair_eval,
    eventualGraph_normalizeIndex_eval, eventualGraph_normalizeIndex_eval]
  exact and_congr
    ⟨fun h => h.2.1, fun h => ⟨x.property, h, y.property⟩⟩
    ⟨fun h => h.2.1, fun h => ⟨u.property, h, v.property⟩⟩

/-- The recursive interpretation of formal numerical types used in
Section 4, before applying their arithmetic coding. -/
def interpretedType : STObjectCode → Type
  | .omega => M
  | .product Q R => interpretedType Q × interpretedType R
  | .coproduct Q R => interpretedType Q ⊕ interpretedType R

/-- Explicit comparison of recursively interpreted types with their coded
membership subsets. -/
def codingEquiv : (Q : STObjectCode) → interpretedType M Q ≃ carrier M Q
  | .omega =>
    { toFun := fun x => ⟨x, memberFormula_omega_eval (M := M) x⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | .product Q R => (Equiv.prodCongr (codingEquiv Q) (codingEquiv R)).trans (productEquiv T M Q R)
  | .coproduct Q R => (Equiv.sumCongr (codingEquiv Q) (codingEquiv R)).trans (sumEquiv T M Q R)

def codingIso (Q : CodedProgramCategory T) :
    PartialFun.of (interpretedType M (objectCode Q)) ≅ (functor T M).obj Q :=
  PartialFun.Iso.mk (codingEquiv T M (objectCode Q))

/-- The model functor with the manuscript's recursively interpreted object
carriers. It is obtained by the explicit coding comparison. -/
def modelFunctor : CodedProgramCategory T ⥤ Pfn where
  obj Q := PartialFun.of (interpretedType M (objectCode Q))
  map {Q R} f := (codingIso T M Q).hom ≫ (functor T M).map f ≫ (codingIso T M R).inv
  map_id Q := by rw [(functor T M).map_id, Category.id_comp, Iso.hom_inv_id]
  map_comp f g := by
    simp only [(functor T M).map_comp, Category.assoc]
    rw [← Category.assoc (codingIso T M _).inv, Iso.inv_hom_id, Category.id_comp]

def modelComparison : modelFunctor T M ≅ functor T M :=
  NatIso.ofComponents (codingIso T M) (by
    intro Q R f
    simp only [modelFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id])

theorem map_restriction_product {Q R S V : CodedProgramCategory T}
    (f : Q ⟶ R) (g : S ⟶ V) :
    (PartialFun.Iso.mk (productEquiv T M (objectCode Q) (objectCode S))).hom ≫
      (functor T M).map (PCategoryStruct.nearProd_map f g) ≫
        (PartialFun.Iso.mk (productEquiv T M (objectCode R) (objectCode V))).inv =
      PFun.prodMap ((functor T M).map f) ((functor T M).map g) := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  obtain ⟨r, rfl⟩ := exists_arrowOfIndex T (objectCode S) (objectCode V) g
  apply PFun.ext
  intro x y
  rw [mem_conjugate, PFun.mem_prodMap]
  exact map_product_graph T M _ _ _ _ q r x.1 x.2 y.1 y.2

theorem map_first_projection (Q R : STObjectCode) (x : carrier M Q) (u : carrier M R)
    (y : carrier M Q) :
    y ∈ (functor T M).map (PCategoryStruct.p0 (object T Q) (object T R))
      (productCoding T M Q R (x, u)) ↔ y = x := by
  let := modelPA T M
  rw [TypedNearProduct.p0_object, mem_map_index]
  change (eventualGraph TypedNearProduct.firstProjectionIndex).val.Evalb
    ![pair x.val u.val, y.val] ↔ y = x
  rw [TypedNearProduct.eventualGraph_firstProjectionIndex_eval, pi₁_pair]
  exact Subtype.coe_inj

theorem map_second_projection (Q R : STObjectCode) (x : carrier M Q) (u : carrier M R)
    (y : carrier M R) :
    y ∈ (functor T M).map (PCategoryStruct.p1 (object T Q) (object T R))
      (productCoding T M Q R (x, u)) ↔ y = u := by
  let := modelPA T M
  rw [TypedNearProduct.p1_object, mem_map_index]
  change (eventualGraph TypedNearProduct.secondProjectionIndex).val.Evalb
    ![pair x.val u.val, y.val] ↔ y = u
  rw [TypedNearProduct.eventualGraph_secondProjectionIndex_eval, pi₂_pair]
  exact Subtype.coe_inj

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] in
/-- The interpretations in all arithmetic models are jointly faithful. -/
theorem joint_faithful {Q R : CodedProgramCategory T} (f g : Q ⟶ R)
    (h : ∀ (N : Type) [ORingStructure N] [N↓[ℒₒᵣ] ⊧* T],
      (functor T N).map f = (functor T N).map g) : f = g := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  obtain ⟨r, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) g
  apply (arrowOfIndex_eq_iff_eqIndex_normalize T _ _ q r).mpr
  apply Arithmetic.complete.{0} T
  intro N _ _
  let := modelPA T N
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_normalizeIndex_eval, eventualGraph_normalizeIndex_eval]
  constructor
  · rintro ⟨hx, hq, hy⟩
    have hp := (mem_map_index T N _ _ q ⟨x, hx⟩ ⟨y, hy⟩).mpr hq
    rw [h N] at hp
    exact ⟨hx, (mem_map_index T N _ _ r ⟨x, hx⟩ ⟨y, hy⟩).mp hp, hy⟩
  · rintro ⟨hx, hr, hy⟩
    have hp := (mem_map_index T N _ _ r ⟨x, hx⟩ ⟨y, hy⟩).mpr hr
    rw [← h N] at hp
    exact ⟨hx, (mem_map_index T N _ _ q ⟨x, hx⟩ ⟨y, hy⟩).mp hp, hy⟩

omit [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] in
instance syntacticJoinInverse : JoinInverse (CodedProgramCategory T) where
  pull_sup f a b := by
    apply Idem.ext
    apply joint_faithful T
    intro N _ _
    let F := rangeFunctor T N
    have he : F.mapIdem (Idem.pull f (a ⊔ b)) =
        F.mapIdem (Idem.pull f a ⊔ Idem.pull f b) := by
      rw [F.map_pull, F.map_sup, JoinInverse.pull_sup, F.map_sup,
        F.map_pull, F.map_pull]
    exact congrArg Idem.hom he

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
