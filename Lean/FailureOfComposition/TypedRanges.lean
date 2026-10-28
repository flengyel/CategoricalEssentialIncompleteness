/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.RangeAssignment
import FailureOfComposition.TypedNearProduct
import PCats.Ranges

/-!
# Categorical ranges on the typed program category

The selected range program of a typed arrow is formed only after its raw
representative has been restricted to the declared source and target.  Its
graph is therefore the partial identity on the outputs of the normalized
program.  Uniform provable equality is preserved by this construction, so it
descends to the program quotient and defines a typed endomorphism of the
target.

The resulting endomorphism satisfies the complete `CategoryTheory.IsRange`
interface.  In particular, the universal clause is proved using the
functionality of the production evaluator in arbitrary models of the ambient
theory.  The construction is compatible with the effective near product and
thus equips the category with its maintained `rP`-category structure.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedRanges

open CodedObjectMembership ConcreteEvaluator ConcreteIndices ProofSearch
open TypedProgramCategory TypedNearProduct UniformIndexQuotient
open PCategoryStruct

noncomputable section

/-! ## Normalized numerical range representatives -/

/-- The selected range index of the actual normalized representative of a
typed program.  The selection inherited from `rangeIndex` is not asserted to
be primitive recursive. -/
def typedRangeIndex (Q R : STObjectCode) (q : ℕ) : ℕ :=
  rangeIndex (normalizeIndex Q R q)

/-- The range graph of a normalized typed representative, expressed through
the already defined normalized graph. -/
def typedRangeGraph (Q R : STObjectCode) (q : ℕ) : Graph :=
  rangeOfGraph (normalizedGraph Q R q)

@[simp] theorem typedRangeGraph_eval
    {M : Type*} [ORingStructure M]
    (Q R : STObjectCode) (q : ℕ) (y z : M) :
    (typedRangeGraph Q R q).val.Evalb ![y, z] ↔
      y = z ∧ (memberFormula R).val.Evalb ![y] ∧
        ∃ x : M, (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] := by
  rw [typedRangeGraph, rangeOfGraph_eval]
  constructor
  · rintro ⟨hyz, x, hnorm⟩
    obtain ⟨hQ, hq, hR⟩ := (normalizedGraph_eval Q R q x y).mp hnorm
    exact ⟨hyz, hR, x, hQ, hq⟩
  · rintro ⟨hyz, hR, x, hQ, hq⟩
    exact ⟨hyz, x, (normalizedGraph_eval Q R q x y).mpr ⟨hQ, hq, hR⟩⟩

/-- Exact range equation for the normalized representative in every model of
PA. -/
@[simp] theorem eventualGraph_typedRangeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (y z : M) :
    (eventualGraph (typedRangeIndex Q R q)).val.Evalb ![y, z] ↔
      y = z ∧ ∃ x : M,
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] := by
  exact rangeIndex_graph_equation (normalizeIndex Q R q) y z

/-- The same equation with normalization expanded into its source and target
membership conditions. -/
@[simp] theorem eventualGraph_typedRangeIndex_normalized_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (y z : M) :
    (eventualGraph (typedRangeIndex Q R q)).val.Evalb ![y, z] ↔
      y = z ∧ (memberFormula R).val.Evalb ![y] ∧
        ∃ x : M, (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] := by
  rw [eventualGraph_typedRangeIndex_eval]
  constructor
  · rintro ⟨hyz, x, hnorm⟩
    obtain ⟨hQ, hq, hR⟩ :=
      (eventualGraph_normalizeIndex_eval Q R q x y).mp hnorm
    exact ⟨hyz, hR, x, hQ, hq⟩
  · rintro ⟨hyz, hR, x, hQ, hq⟩
    exact ⟨hyz, x,
      (eventualGraph_normalizeIndex_eval Q R q x y).mpr ⟨hQ, hq, hR⟩⟩

/-- PA-uniform equation for the selected typed range representative. -/
theorem typedRangeIndex_uniform (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (typedRangeIndex Q R q))
      (rangeGraph (normalizeIndex Q R q)) :=
  rangeIndex_realizes (normalizeIndex Q R q)

/-- PA-uniform equation with the source-target normalization graph expanded. -/
theorem typedRangeIndex_normalized_uniform
    (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (typedRangeIndex Q R q))
      (typedRangeGraph Q R q) :=
  rangeIndex_of_uniform (normalizeIndex_uniform Q R q)

/-! ## Descent through uniform equality -/

/-- Taking the range partial identity preserves uniform equality over any
theory whose provability includes PA. -/
theorem uniform_rangeOfGraph_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F G : Graph}
    (h : Uniform T F G) :
    Uniform T (rangeOfGraph F) (rangeOfGraph G) := by
  apply complete.{0} T
  intro M _ hM
  have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
  simp only [models_iff, uniformSentence_eval] at h' ⊢
  intro y z
  rw [rangeOfGraph_eval, rangeOfGraph_eval]
  exact and_congr_right fun _ => exists_congr fun x => h' x y

/-- The selected numerical range operation respects uniform `T`-provable
graph equality. -/
theorem eqIndex_range_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {q r : ℕ}
    (h : EqIndex T q r) : EqIndex T (rangeIndex q) (rangeIndex r) := by
  exact uniform_trans (WeakerThan.pbl (rangeIndex_realizes q))
    (uniform_trans (uniform_rangeOfGraph_in T h)
      (uniform_symm (WeakerThan.pbl (rangeIndex_realizes r))))

/-- Range on quotient programs, obtained by descent through uniform graph
equality. -/
def rangeClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T → ProgramQuotient T :=
  Quotient.lift
    (fun q => classOf T (rangeIndex q))
    (fun _ _ h => Quotient.sound (eqIndex_range_congr T h))

@[simp] theorem rangeClass_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    rangeClass T (classOf T q) = classOf T (rangeIndex q) :=
  rfl

/-! ## Algebra of quotient ranges -/

/-- The computation domain of a selected range partial identity is that same
partial identity. -/
theorem eqIndex_domain_range
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T (domainIndex (rangeIndex q)) (rangeIndex q) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨hyx, z, hz⟩ :=
      (eventualGraph_domainIndex_eval (rangeIndex q) x y).mp h
    obtain ⟨hxz, u, hu⟩ := (rangeIndex_graph_equation q x z).mp hz
    exact (rangeIndex_graph_equation q x y).mpr ⟨hyx.symm, u, hu⟩
  · intro h
    obtain ⟨hxy, u, hu⟩ := (rangeIndex_graph_equation q x y).mp h
    apply (eventualGraph_domainIndex_eval (rangeIndex q) x y).mpr
    exact ⟨hxy.symm, x,
      (rangeIndex_graph_equation q x x).mpr ⟨rfl, u, hu⟩⟩

/-- A selected range partial identity receives its source program. -/
theorem eqIndex_range_receives
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T (compIndex (rangeIndex q) q) q := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x z
  constructor
  · intro h
    obtain ⟨y, hq, hr⟩ := (eventualGraph_comp_eval _ _ x z).mp h
    obtain ⟨hyz, -, -⟩ := (rangeIndex_graph_equation q y z).mp hr
    simpa only [hyz] using hq
  · intro hq
    apply (eventualGraph_comp_eval _ _ x z).mpr
    exact ⟨z, hq,
      (rangeIndex_graph_equation q z z).mpr ⟨rfl, x, hq⟩⟩

/-- The universal range clause at the level of numerical representatives. -/
theorem eqIndex_range_uniq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (q β β' : ℕ)
    (h : EqIndex T (compIndex β q) (compIndex β' q)) :
    EqIndex T (compIndex β (rangeIndex q))
      (compIndex β' (rangeIndex q)) := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
  simp only [models_iff, uniformSentence_eval] at h' ⊢
  intro x z
  constructor
  · intro hxz
    obtain ⟨y, hry, hβ⟩ := (eventualGraph_comp_eval _ _ x z).mp hxz
    obtain ⟨hxy, u, hqu⟩ := (rangeIndex_graph_equation q x y).mp hry
    have hβx : (eventualGraph β).val.Evalb ![x, z] := by
      simpa only [hxy] using hβ
    have hcomp :
        (eventualGraph (compIndex β q)).val.Evalb ![u, z] :=
      (eventualGraph_comp_eval β q u z).mpr ⟨x, hqu, hβx⟩
    obtain ⟨v, hqv, hβ'v⟩ :=
      (eventualGraph_comp_eval β' q u z).mp ((h' u z).mp hcomp)
    have hxv : x = v := eventualGraph_output_unique q u x v hqu hqv
    apply (eventualGraph_comp_eval β' (rangeIndex q) x z).mpr
    exact ⟨v, (rangeIndex_graph_equation q x v).mpr ⟨hxv, u, hqu⟩,
      hβ'v⟩
  · intro hxz
    obtain ⟨y, hry, hβ'⟩ := (eventualGraph_comp_eval _ _ x z).mp hxz
    obtain ⟨hxy, u, hqu⟩ := (rangeIndex_graph_equation q x y).mp hry
    have hβ'x : (eventualGraph β').val.Evalb ![x, z] := by
      simpa only [hxy] using hβ'
    have hcomp :
        (eventualGraph (compIndex β' q)).val.Evalb ![u, z] :=
      (eventualGraph_comp_eval β' q u z).mpr ⟨x, hqu, hβ'x⟩
    obtain ⟨v, hqv, hβv⟩ :=
      (eventualGraph_comp_eval β q u z).mp ((h' u z).mpr hcomp)
    have hxv : x = v := eventualGraph_output_unique q u x v hqu hqv
    apply (eventualGraph_comp_eval β (rangeIndex q) x z).mpr
    exact ⟨v, (rangeIndex_graph_equation q x v).mpr ⟨hxv, u, hqu⟩,
      hβv⟩

/-- If a program is fixed by the target object idempotent, then its range is
fixed by that idempotent on both sides. -/
theorem eqIndex_range_target_supported
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (R : STObjectCode) (q : ℕ)
    (h : EqIndex T (compIndex (deltaIndex R) q) q) :
    EqIndex T (compIndex (deltaIndex R) (rangeIndex q)) (rangeIndex q) ∧
      EqIndex T (compIndex (rangeIndex q) (deltaIndex R)) (rangeIndex q) := by
  constructor
  · have hcomp : EqIndex T (compIndex (deltaIndex R) q)
        (compIndex Kleene.identityIndex q) :=
      eqIndex_trans h (eqIndex_symm (eqIndex_identity_comp T q))
    exact eqIndex_trans (eqIndex_range_uniq T q (deltaIndex R)
      Kleene.identityIndex hcomp)
      (eqIndex_identity_comp T (rangeIndex q))
  · apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
    simp only [models_iff, uniformSentence_eval] at h' ⊢
    intro x y
    constructor
    · intro hxy
      obtain ⟨z, hR, hr⟩ := (eventualGraph_comp_eval _ _ x y).mp hxy
      obtain ⟨hRx, hzx⟩ := (eventualGraph_deltaIndex_eval R x z).mp hR
      obtain ⟨hzy, u, hqu⟩ := (rangeIndex_graph_equation q z y).mp hr
      apply (rangeIndex_graph_equation q x y).mpr
      exact ⟨hzx.symm.trans hzy, u, by simpa only [hzx] using hqu⟩
    · intro hr
      obtain ⟨hxy, u, hqu⟩ := (rangeIndex_graph_equation q x y).mp hr
      have hcomp :
          (eventualGraph (compIndex (deltaIndex R) q)).val.Evalb ![u, x] :=
        (h' u x).mpr hqu
      obtain ⟨z, hqz, hRzx⟩ :=
        (eventualGraph_comp_eval (deltaIndex R) q u x).mp hcomp
      have hzx : z = x := eventualGraph_output_unique q u z x hqz hqu
      have hRxx : (eventualGraph (deltaIndex R)).val.Evalb ![x, x] := by
        simpa only [hzx] using hRzx
      apply (eventualGraph_comp_eval (rangeIndex q) (deltaIndex R) x y).mpr
      exact ⟨x, hRxx, (rangeIndex_graph_equation q x y).mpr
        ⟨hxy, u, hqu⟩⟩

@[simp] theorem domainClass_rangeClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) :
    domainClass T (rangeClass T a) = rangeClass T a := by
  refine Quotient.inductionOn a ?_
  intro q
  change classOf T (domainIndex (rangeIndex q)) = classOf T (rangeIndex q)
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_domain_range T q)

@[simp] theorem rangeClass_mul
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) : rangeClass T a * a = a := by
  refine Quotient.inductionOn a ?_
  intro q
  change classOf T (compIndex (rangeIndex q) q) = classOf T q
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_range_receives T q)

/-- Quotient form of the full universal range clause. -/
theorem rangeClass_uniq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a β β' : ProgramQuotient T)
    (h : β * a = β' * a) :
    β * rangeClass T a = β' * rangeClass T a := by
  revert h
  refine Quotient.inductionOn a ?_
  intro q
  refine Quotient.inductionOn β ?_
  intro b
  refine Quotient.inductionOn β' ?_
  intro c h
  change classOf T (compIndex b q) = classOf T (compIndex c q) at h
  change classOf T (compIndex b (rangeIndex q)) =
    classOf T (compIndex c (rangeIndex q))
  apply (classOf_eq_classOf_iff T _ _).mpr
  exact eqIndex_range_uniq T q b c
    ((classOf_eq_classOf_iff T _ _).mp h)

/-- Both target-support equations for the range of a supported quotient
program. -/
theorem rangeClass_target_supported
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (R : STObjectCode) (a : ProgramQuotient T)
    (h : objectIdempotent T R * a = a) :
    objectIdempotent T R * rangeClass T a = rangeClass T a ∧
      rangeClass T a * objectIdempotent T R = rangeClass T a := by
  revert h
  refine Quotient.inductionOn a ?_
  intro q h
  change classOf T (compIndex (deltaIndex R) q) = classOf T q at h
  obtain ⟨hl, hr⟩ := eqIndex_range_target_supported T R q
    ((classOf_eq_classOf_iff T _ _).mp h)
  change classOf T (compIndex (deltaIndex R) (rangeIndex q)) =
      classOf T (rangeIndex q) ∧
    classOf T (compIndex (rangeIndex q) (deltaIndex R)) =
      classOf T (rangeIndex q)
  constructor
  · exact (classOf_eq_classOf_iff T _ _).mpr hl
  · exact (classOf_eq_classOf_iff T _ _).mpr hr

/-! ## Typed range arrows and the `HasRanges` instance -/

/-- The typed range endomorphism of the target of `f`. -/
def rangeArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) : R ⟶ R :=
  ⟨rangeClass T f.1, rangeClass_target_supported T (objectCode R) f.1 f.2.1⟩

@[simp] theorem rangeArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (rangeArrow T f).1 = rangeClass T f.1 :=
  rfl

/-- Exact representative equation: normalization precedes the selected range
construction. -/
@[simp] theorem rangeArrow_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    rangeArrow T (arrowOfIndex T Q R q) =
      arrowOfIndex T R R (typedRangeIndex Q R q) := by
  symm
  apply arrowOfIndex_eq_of_class
  rw [rangeArrow_val, arrowOfIndex_val, rangeClass_classOf]
  rfl

/-- Reapplying the target normalization to a selected typed range
representative does not change its uniform `T`-class. -/
theorem typedRangeIndex_normalize_eq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T (normalizeIndex R R (typedRangeIndex Q R q))
      (typedRangeIndex Q R q) := by
  have h := congrArg Subtype.val (rangeArrow_arrowOfIndex T Q R q)
  rw [rangeArrow_val, arrowOfIndex_val, rangeClass_classOf,
    arrowOfIndex_val] at h
  exact (classOf_eq_classOf_iff T _ _).mp h.symm

/-- Any PA-uniform realizer of the same normalized range graph represents the
same typed range arrow. -/
theorem rangeArrow_eq_arrowOfIndex_of_realizes
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q r : ℕ)
    (hr : Uniform 𝗣𝗔 (eventualGraph r)
      (rangeGraph (normalizeIndex Q R q))) :
    rangeArrow T (arrowOfIndex T Q R q) = arrowOfIndex T R R r := by
  symm
  apply arrowOfIndex_eq_of_class
  rw [rangeArrow_val, arrowOfIndex_val, rangeClass_classOf]
  apply (classOf_eq_classOf_iff T _ _).mpr
  exact WeakerThan.pbl
    (rangeIndex_realization_unique hr
      (rangeIndex_realizes (normalizeIndex Q R q)))

/-- The concrete typed range arrow satisfies all three categorical range
clauses. -/
theorem rangeArrow_isRange
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    IsRange (rangeArrow T f) f where
  isDomain := by
    apply CodedHom.ext
    rw [← domainArrow_eq_rst]
    exact domainClass_rangeClass T f.1
  receives := by
    apply CodedHom.ext
    exact rangeClass_mul T f.1
  uniq β β' h := by
    apply CodedHom.ext
    apply rangeClass_uniq T f.1 β.1 β'.1
    exact congrArg Subtype.val h

/-- The typed program category has categorical ranges. -/
instance codedProgramCategoryHasRanges
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    HasRanges (CodedProgramCategory T) where
  ran := rangeArrow T
  isRange := rangeArrow_isRange T

@[simp] theorem ran_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    HasRanges.ran (arrowOfIndex T Q R q) =
      arrowOfIndex T R R (typedRangeIndex Q R q) :=
  rangeArrow_arrowOfIndex T Q R q

/-! ## Compatibility with the near product -/

/-- Taking a selected range commutes with the effective tensor constructor. -/
theorem eqIndex_range_tensor
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    EqIndex T (rangeIndex (tensorIndex q r))
      (tensorIndex (rangeIndex q) (rangeIndex r)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro s z
  constructor
  · intro h
    obtain ⟨hsz, p, hp⟩ :=
      (rangeIndex_graph_equation (tensorIndex q r) s z).mp h
    obtain ⟨y, v, hq, hr, hsp⟩ :=
      (eventualGraph_tensorIndex_eval q r p s).mp hp
    have hsy : pi₁ s = y := by rw [hsp, pi₁_pair]
    have hsv : pi₂ s = v := by rw [hsp, pi₂_pair]
    apply (eventualGraph_tensorIndex_eval (rangeIndex q) (rangeIndex r) s z).mpr
    refine ⟨y, v, ?_, ?_, ?_⟩
    · exact (rangeIndex_graph_equation q (pi₁ s) y).mpr
        ⟨hsy, pi₁ p, by simpa only [hsy] using hq⟩
    · exact (rangeIndex_graph_equation r (pi₂ s) v).mpr
        ⟨hsv, pi₂ p, by simpa only [hsv] using hr⟩
    · exact hsz.symm.trans hsp
  · intro h
    obtain ⟨y, v, hqy, hrv, hz⟩ :=
      (eventualGraph_tensorIndex_eval (rangeIndex q) (rangeIndex r) s z).mp h
    obtain ⟨hsy, x, hqx⟩ :=
      (rangeIndex_graph_equation q (pi₁ s) y).mp hqy
    obtain ⟨hsv, u, hru⟩ :=
      (rangeIndex_graph_equation r (pi₂ s) v).mp hrv
    apply (rangeIndex_graph_equation (tensorIndex q r) s z).mpr
    refine ⟨?_, pair x u, ?_⟩
    · calc
        s = pair (pi₁ s) (pi₂ s) := (pair_unpair s).symm
        _ = pair y v := by rw [hsy, hsv]
        _ = z := hz.symm
    · apply (eventualGraph_tensorIndex_eval q r (pair x u) s).mpr
      exact ⟨pi₁ s, pi₂ s, by simpa only [pi₁_pair] using hqx,
        by simpa only [pi₂_pair] using hru, (pair_unpair s).symm⟩

@[simp] theorem rangeClass_tensorClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b : ProgramQuotient T) :
    rangeClass T (tensorClass T a b) =
      tensorClass T (rangeClass T a) (rangeClass T b) := by
  refine Quotient.inductionOn a ?_
  intro q
  refine Quotient.inductionOn b ?_
  intro r
  change classOf T (rangeIndex (tensorIndex q r)) =
    classOf T (tensorIndex (rangeIndex q) (rangeIndex r))
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_range_tensor T q r)

/-- Concrete ranges commute with the near-product map. -/
theorem ran_nearProd_map
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y Z : CodedProgramCategory T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    HasRanges.ran (nearProd_map f g) =
      nearProd_map (HasRanges.ran f) (HasRanges.ran g) := by
  apply CodedHom.ext
  exact rangeClass_tensorClass T f.1 g.1

/-- The typed program category is an `rP`-category. -/
instance codedProgramCategoryIsRP
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsRP (CodedProgramCategory T) where
  ran_nearProd_map := ran_nearProd_map T

/-! ## Focused categorical applications -/

/-- The range of an identity is the identity, specialized to every coded
object. -/
@[simp] theorem ran_identity
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    HasRanges.ran (𝟙 Q) = 𝟙 Q :=
  HasRanges.ran_id Q

/-- The normalized first projection from `Q ⨯ omega` has the whole of `Q`
as its range.  The reverse implication uses the input pair `(y, 0)`. -/
theorem eqIndex_range_firstProjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    EqIndex T
      (rangeIndex
        (normalizeIndex (.product Q .omega) Q firstProjectionIndex))
      (deltaIndex Q) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro y z
  constructor
  · intro hr
    obtain ⟨hyz, x, hx⟩ :=
      (rangeIndex_graph_equation
        (normalizeIndex (.product Q .omega) Q firstProjectionIndex)
        y z).mp hr
    have hQ :=
      (eventualGraph_normalizeIndex_eval (.product Q .omega) Q
        firstProjectionIndex x y).mp hx |>.2.2
    exact (eventualGraph_deltaIndex_eval Q y z).mpr ⟨hQ, hyz.symm⟩
  · intro hdelta
    obtain ⟨hQ, hzy⟩ := (eventualGraph_deltaIndex_eval Q y z).mp hdelta
    apply (rangeIndex_graph_equation
      (normalizeIndex (.product Q .omega) Q firstProjectionIndex)
      y z).mpr
    refine ⟨hzy.symm, pair y 0, ?_⟩
    apply (eventualGraph_normalizeIndex_eval (.product Q .omega) Q
      firstProjectionIndex (pair y 0) y).mpr
    refine ⟨?_, ?_, hQ⟩
    · exact (memberFormula_product_pair_eval Q .omega y 0).mpr
        ⟨hQ, memberFormula_omega_eval 0⟩
    · exact (eventualGraph_firstProjectionIndex_eval (pair y 0) y).mpr
        (by simp only [pi₁_pair])

/-- The range of the first projection `Q ⨯ omega ⟶ Q` is the identity of
`Q`, for every coded object `Q`. -/
@[simp] theorem ran_firstProjection_product_omega
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    HasRanges.ran
      (p0 (object T Q) (object T STObjectCode.omega)) =
      𝟙 (object T Q) := by
  change HasRanges.ran
    (arrowOfIndex T (.product Q .omega) Q firstProjectionIndex) =
      𝟙 (object T Q)
  rw [ran_arrowOfIndex]
  apply arrowOfIndex_eq_of_class
  rw [id_val, objectIdempotent]
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_range_firstProjection T Q)

/-! ## Closed arithmetic instances -/

/-- The unary formula asserting that `y` is an output of the normalized typed
representative. -/
def typedRangeMembershipFormula
    (Q R : STObjectCode) (q : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma
    “y. ∃ x, !(eventualGraph (normalizeIndex Q R q)).val x y”

@[simp] theorem typedRangeMembershipFormula_eval
    {M : Type*} [ORingStructure M]
    (Q R : STObjectCode) (q : ℕ) (y : M) :
    (typedRangeMembershipFormula Q R q).val.Evalb ![y] ↔
      ∃ x : M,
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] := by
  simp [typedRangeMembershipFormula]

@[simp] theorem typedRangeMembershipFormula_instance_eval
    {M : Type*} [ORingStructure M]
    (Q R : STObjectCode) (q n : ℕ) :
    ((typedRangeMembershipFormula Q R q).val/[n]).Evalb (M := M) ![] ↔
      ∃ x : M, (eventualGraph (normalizeIndex Q R q)).val.Evalb
        ![x, (ORingStructure.numeral n : M)] := by
  simp

/-- Closed-instance derivability for the displayed range representative.  The
existential input remains inside `T`-provability. -/
theorem typedRangeIndex_provable_iff
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q n : ℕ) :
    (T ⊢ (eventualGraph (typedRangeIndex Q R q)).val/[n, n]) ↔
      (T ⊢ (typedRangeMembershipFormula Q R q).val/[n]) := by
  constructor
  · intro h
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
    rw [models_iff, graph_instance_eval] at h'
    rw [models_iff, typedRangeMembershipFormula_instance_eval]
    exact (eventualGraph_typedRangeIndex_eval Q R q _ _).mp h' |>.2
  · intro h
    apply complete.{0} T
    intro M _ hM
    have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
      models_of_subtheory (U := T) inferInstance
    have h' := consequence_iff.mp (Theory.Proof.sound h) M hM
    rw [models_iff, typedRangeMembershipFormula_instance_eval] at h'
    rw [models_iff, graph_instance_eval]
    exact (eventualGraph_typedRangeIndex_eval Q R q _ _).mpr
      ⟨rfl, h'⟩

end

end FailureOfComposition.TypedRanges
