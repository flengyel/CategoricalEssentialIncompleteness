/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.ArithmeticCodeCompiler
import FailureOfComposition.FirstSuccessGraph
import FailureOfComposition.TypedCoproducts
import PCats.Recursion

/-!
# A Turing morphism on the typed program category

The fixed program in this file treats an input as `pair (pair q v) x`.
Here `q` is an internal program code, `v` is a stored parameter, and `x` is
the current input.  The program applies the canonical first-success evaluator
to `q` and `pair v x`.  For each external index `q : ℕ`, a total parameter
arrow stores the standard numeral for `q` beside its input.  This convention
gives the factorization required by the maintained `IsTuringMorphism`
interface for every coded parameter object.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open CategoricalRiceShapiro.ArithmeticCode
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedTuringMorphism

open ArithmeticCodeCompiler CodedObjectMembership ConcreteEvaluator
open ProgramGraph ProofSearch TypedProgramCategory TypedNearProduct
open UniformIndexQuotient
open PCategoryStruct CategoryTheory.RecursionCategory

noncomputable section

/-! ## The fixed evaluator program -/

/-- The arithmetic code reads an input `z = pair (pair q v) x` and applies
the canonical evaluator to `q` and `pair v x`. -/
def tauArithmeticCode : Nat.ArithPart₁.Code 1 :=
  .comp canonicalEvalnCode ![
    codeUnpair₁ (codeUnpair₁ (.proj 0)),
    codePair (codeUnpair₂ (codeUnpair₁ (.proj 0)))
      (codeUnpair₂ (.proj 0))]

/-- The fixed unary Mathlib program compiled from `tauArithmeticCode`. -/
def tauProgram : Nat.Partrec.Code :=
  unaryCompile tauArithmeticCode

/-- The production index of the fixed Turing program. -/
def tauIndex : ℕ :=
  encode tauProgram

/-- The compiler graph of the fixed Turing program. -/
def tauGraph : Graph :=
  sourceGraph tauArithmeticCode

private theorem tauArgumentCodes_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : M) :
    Semiformula.Evalb
        (pi₁ (pi₁ z) :> ![z])
        (code (codeUnpair₁ (codeUnpair₁
          (Nat.ArithPart₁.Code.proj 0)))) ∧
      Semiformula.Evalb
        (pair (pi₂ (pi₁ z)) (pi₂ z) :> ![z])
        (code (codePair
          (codeUnpair₂ (codeUnpair₁ (Nat.ArithPart₁.Code.proj 0)))
          (codeUnpair₂ (Nat.ArithPart₁.Code.proj 0)))) := by
  have hz : Semiformula.Evalb (z :> ![z])
      (code (Nat.ArithPart₁.Code.proj 0)) :=
    (eval_proj_iff 0 z ![z]).mpr rfl
  have hz₁ : Semiformula.Evalb (pi₁ z :> ![z])
      (code (codeUnpair₁ (Nat.ArithPart₁.Code.proj 0))) :=
    eval_codeUnpair₁ _ z ![z] hz
  have hz₂ : Semiformula.Evalb (pi₂ z :> ![z])
      (code (codeUnpair₂ (Nat.ArithPart₁.Code.proj 0))) :=
    eval_codeUnpair₂ _ z ![z] hz
  have hq : Semiformula.Evalb (pi₁ (pi₁ z) :> ![z])
      (code (codeUnpair₁ (codeUnpair₁
        (Nat.ArithPart₁.Code.proj 0)))) :=
    eval_codeUnpair₁ _ (pi₁ z) ![z] hz₁
  have hv : Semiformula.Evalb (pi₂ (pi₁ z) :> ![z])
      (code (codeUnpair₂ (codeUnpair₁
        (Nat.ArithPart₁.Code.proj 0)))) :=
    eval_codeUnpair₂ _ (pi₁ z) ![z] hz₁
  exact ⟨hq, eval_codePair _ _ _ _ ![z] hv hz₂⟩

/-- Evaluation of the explicit arithmetic code exposes the internal program
code and the stored-parameter input. -/
theorem tauArithmeticCode_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z y : M) :
    Semiformula.Evalb ![y, z] (code tauArithmeticCode) ↔
      Semiformula.Evalb
        ![y, pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z)]
        (code canonicalEvalnCode) := by
  rw [tauArithmeticCode, eval_comp_iff]
  obtain ⟨hq, hu⟩ := tauArgumentCodes_eval z
  constructor
  · rintro ⟨w, hw, hargs⟩
    have hwq : w 0 = pi₁ (pi₁ z) := eval_unique (hargs 0) hq
    have hwu : w 1 = pair (pi₂ (pi₁ z)) (pi₂ z) :=
      eval_unique (hargs 1) hu
    have hwv : w = ![pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z)] := by
      funext i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
      · exact hwq
      · exact hwu
    subst w
    exact hw
  · intro h
    refine ⟨![pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z)], ?_, ?_⟩
    · exact h
    · intro i
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
      · exact hq
      · exact hu

/-- The compiler graph has the intended first-success semantics for internal
program, parameter, input, and output elements of every PA model. -/
@[simp] theorem tauGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z y : M) :
    tauGraph.val.Evalb ![z, y] ↔
      Semiformula.Evalb
        ![pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z), y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  rw [tauGraph, sourceGraph_eval, tauArithmeticCode_eval]
  exact (canonicalPartrecGraphFormula_eval_iff
    (pi₁ (pi₁ z)) (pair (pi₂ (pi₁ z)) (pi₂ z)) y).symm

/-- PA proves that the compiled fixed program realizes `tauGraph`. -/
theorem tauIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph tauIndex) tauGraph := by
  change Uniform 𝗣𝗔
    (eventualGraph (encode (unaryCompile tauArithmeticCode)))
    (sourceGraph tauArithmeticCode)
  exact unaryCompile_realizes tauArithmeticCode

/-- Arbitrary-model graph equation for the fixed Turing program. -/
@[simp] theorem eventualGraph_tauIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z y : M) :
    (eventualGraph tauIndex).val.Evalb ![z, y] ↔
      Semiformula.Evalb
        ![pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z), y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  have h := consequence_iff.mp (Theory.Proof.sound tauIndex_uniform) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h z y).trans (tauGraph_eval z y)

/-- At a fixed external index `q : ℕ`, the internal evaluator section is the
production graph of `q`; the parameter, input, and output remain arbitrary
elements of the PA model. -/
@[simp] theorem eventualGraph_tauIndex_section_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (v x y : M) :
    (eventualGraph tauIndex).val.Evalb
        ![pair (pair (q : M) v) x, y] ↔
      (eventualGraph q).val.Evalb ![pair v x, y] := by
  rw [eventualGraph_tauIndex_eval]
  simpa only [pi₁_pair, pi₂_pair, numeral_eq_natCast_app] using
    (canonicalPartrecGraphFormula_eval_iff_eventualGraph q (pair v x) y)

/-! ## Total parameter arrows and the typed Turing map -/

/-- The explicit parameter program sends `v` to `pair q v`, where `q` is an
external natural number and hence denotes a standard numeral in every model. -/
def parameterProgram (q : ℕ) : Nat.Partrec.Code :=
  .pair (.const q) .id

/-- Production index of `parameterProgram q`. -/
def parameterIndex (q : ℕ) : ℕ :=
  encode (parameterProgram q)

/-- Exact arbitrary-model graph of the raw parameter program. -/
@[simp] theorem eventualGraph_parameterIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (v w : M) :
    (eventualGraph (parameterIndex q)).val.Evalb ![v, w] ↔
      w = pair (q : M) v := by
  change Computes (.pair (.const q) .id) v w ↔ _
  rw [computes_pair]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    rw [(computes_const q v a).mp ha, (computes_id v b).mp hb]
  · intro h
    exact ⟨(q : M), v, (computes_const q v _).mpr rfl,
      (computes_id v v).mpr rfl, h⟩

/-- Normalization restricts the parameter program exactly to members of its
declared coded source. -/
@[simp] theorem eventualGraph_normalize_parameterIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (V : STObjectCode) (q : ℕ) (v w : M) :
    (eventualGraph (normalizeIndex V .omega (parameterIndex q))).val.Evalb
        ![v, w] ↔
      (memberFormula V).val.Evalb ![v] ∧ w = pair (q : M) v := by
  rw [eventualGraph_normalizeIndex_eval,
    eventualGraph_parameterIndex_eval]
  simp only [memberFormula_omega_eval, and_true]

/-- PA proves that the parameter program terminates on every member of its
declared source object. -/
theorem pa_proves_parameterIndex_totality
    (V : STObjectCode) (q : ℕ) :
    𝗣𝗔 ⊢ typedTotalitySentence V .omega (parameterIndex q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, typedTotalitySentence_eval]
  intro v hV
  exact ⟨pair (q : M) v,
    (eventualGraph_normalize_parameterIndex_eval V q v _).mpr ⟨hV, rfl⟩⟩

/-- The typed parameter arrow for a coded source `V` and external index `q`. -/
def parameterArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : CodedProgramCategory T) (q : ℕ) : V ⟶ omegaObject T :=
  arrowOfIndex T (objectCode V) .omega (parameterIndex q)

@[simp] theorem parameterArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : CodedProgramCategory T) (q : ℕ) :
    (parameterArrow T V q).1 =
      classOf T (normalizeIndex (objectCode V) .omega (parameterIndex q)) :=
  arrowOfIndex_val T (objectCode V) .omega (parameterIndex q)

/-- Every parameter arrow is restriction-total relative to its coded source. -/
theorem parameterArrow_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : CodedProgramCategory T) (q : ℕ) :
    RestrictionCategory.isTotal (parameterArrow T V q) := by
  apply (arrowOfIndex_isTotal_iff_proves_typedTotality T
    (objectCode V) .omega (parameterIndex q)).mpr
  exact WeakerThan.pbl (pa_proves_parameterIndex_totality (objectCode V) q)

/-- The raw fixed evaluator is supported from `Omega product Omega` to
`Omega`; every model element belongs to these coded objects. -/
theorem pa_proves_tauIndex_support :
    𝗣𝗔 ⊢ supportSentence (.product .omega .omega) .omega tauIndex := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro z y _
  constructor
  · apply (memberFormula_product_eval .omega .omega z).mpr
    exact ⟨pi₁ z, pi₂ z, (pair_unpair z).symm,
      memberFormula_omega_eval _, memberFormula_omega_eval _⟩
  · exact memberFormula_omega_eval y

/-- Source-target normalization does not change the fixed evaluator graph in
any theory extending PA. -/
theorem eqIndex_normalize_tauIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (normalizeIndex (.product .omega .omega) .omega tauIndex)
      tauIndex :=
  (proves_support_iff_eqIndex_normalize T
    (.product .omega .omega) .omega tauIndex).mp
      (WeakerThan.pbl pa_proves_tauIndex_support)

/-- Every element of a PA model belongs to the coded product
`Omega product Omega`. -/
@[simp] theorem memberFormula_omegaProduct_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : M) :
    (memberFormula (.product .omega .omega)).val.Evalb ![z] := by
  apply (memberFormula_product_eval .omega .omega z).mpr
  exact ⟨pi₁ z, pi₂ z, (pair_unpair z).symm,
    memberFormula_omega_eval _, memberFormula_omega_eval _⟩

/-- Source-target normalization is harmless on the displayed graph of the
fixed evaluator. -/
@[simp] theorem eventualGraph_normalize_tauIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z y : M) :
    (eventualGraph
        (normalizeIndex (.product .omega .omega) .omega tauIndex)).val.Evalb
        ![z, y] ↔
      Semiformula.Evalb
        ![pi₁ (pi₁ z), pair (pi₂ (pi₁ z)) (pi₂ z), y]
        (↑canonicalPartrecGraphFormula : ArithmeticSemisentence 3) := by
  rw [eventualGraph_normalizeIndex_eval, eventualGraph_tauIndex_eval]
  simp only [memberFormula_omegaProduct_eval, memberFormula_omega_eval,
    true_and, and_true]

/-- The typed fixed evaluator `tau : Omega product Omega ⟶ Omega`. -/
def typedTau
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T :=
  arrowOfIndex T (.product .omega .omega) .omega tauIndex

@[simp] theorem typedTau_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (typedTau T).1 = classOf T tauIndex := by
  rw [typedTau, arrowOfIndex_val, classOf_eq_classOf_iff]
  exact eqIndex_normalize_tauIndex T

/-! ## Uniform sections and representative-level factorization -/

/-- The raw program obtained by storing the external index `q`, preserving the
current input, and then applying `tauIndex`. -/
def tauSectionIndex (q : ℕ) : ℕ :=
  compIndex tauIndex
    (tensorIndex (parameterIndex q) Kleene.identityIndex)

/-- The model-level section equation gives a PA proof of uniform graph
equality for every fixed external index. -/
theorem eqIndex_tauSection (q : ℕ) :
    EqIndex 𝗣𝗔 (tauSectionIndex q) q := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro s y
  rw [tauSectionIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hz, htau⟩
    obtain ⟨a, b, ha, hb, rfl⟩ :=
      (eventualGraph_tensorIndex_eval
        (parameterIndex q) Kleene.identityIndex s z).mp hz
    have ha' : a = pair (q : M) (pi₁ s) :=
      (eventualGraph_parameterIndex_eval q (pi₁ s) a).mp ha
    have hb' : b = pi₂ s :=
      (eventualGraph_identityIndex_eval (pi₂ s) b).mp hb
    subst a
    subst b
    have hq :=
      (eventualGraph_tauIndex_section_eval q (pi₁ s) (pi₂ s) y).mp htau
    simpa only [pair_unpair] using hq
  · intro hq
    have hq' :
        (eventualGraph q).val.Evalb ![pair (pi₁ s) (pi₂ s), y] := by
      simpa only [pair_unpair] using hq
    refine ⟨pair (pair (q : M) (pi₁ s)) (pi₂ s), ?_,
      (eventualGraph_tauIndex_section_eval q (pi₁ s) (pi₂ s) y).mpr hq'⟩
    apply (eventualGraph_tensorIndex_eval
      (parameterIndex q) Kleene.identityIndex s _).mpr
    exact ⟨pair (q : M) (pi₁ s), pi₂ s,
      (eventualGraph_parameterIndex_eval q (pi₁ s) _).mpr rfl,
      (eventualGraph_identityIndex_eval (pi₂ s) _).mpr rfl, rfl⟩

/-- The actual normalized index represented by a raw arrow from
`V product Omega` to `Omega`. -/
def normalizedArrowIndex (V : STObjectCode) (r : ℕ) : ℕ :=
  normalizeIndex (.product V .omega) .omega r

/-- Representative of the typed factorization through `tauIndex`.  The
parameter program is normalized at `V`, whereas the second coordinate is the
production identity. -/
def turingFactorizationIndex (V : STObjectCode) (r : ℕ) : ℕ :=
  compIndex tauIndex
    (tensorIndex
      (normalizeIndex V .omega (parameterIndex (normalizedArrowIndex V r)))
      Kleene.identityIndex)

/-- Every raw representative factors through the fixed evaluator after its
actual source-target normalization. -/
theorem eqIndex_turingFactorization
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : STObjectCode) (r : ℕ) :
    EqIndex T (turingFactorizationIndex V r) (normalizedArrowIndex V r) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro s y
  rw [turingFactorizationIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨z, hz, htau⟩
    obtain ⟨a, b, ha, hb, rfl⟩ :=
      (eventualGraph_tensorIndex_eval
        (normalizeIndex V .omega
          (parameterIndex (normalizedArrowIndex V r)))
        Kleene.identityIndex s z).mp hz
    obtain ⟨-, ha'⟩ :=
      (eventualGraph_normalize_parameterIndex_eval V
        (normalizedArrowIndex V r) (pi₁ s) a).mp ha
    have hb' : b = pi₂ s :=
      (eventualGraph_identityIndex_eval (pi₂ s) b).mp hb
    subst a
    subst b
    have hq := (eventualGraph_tauIndex_section_eval
      (normalizedArrowIndex V r) (pi₁ s) (pi₂ s) y).mp htau
    simpa only [pair_unpair] using hq
  · intro hq
    have hqnorm :
        (eventualGraph (normalizeIndex (.product V .omega) .omega r)).val.Evalb
          ![s, y] := by
      simpa only [normalizedArrowIndex] using hq
    obtain ⟨hsource, -, -⟩ :=
      (eventualGraph_normalizeIndex_eval
        (.product V .omega) .omega r s y).mp hqnorm
    obtain ⟨a, b, hs, hV, -⟩ :=
      (memberFormula_product_eval V .omega s).mp hsource
    have hVa : (memberFormula V).val.Evalb ![pi₁ s] := by
      have hpa : pi₁ s = a := by rw [hs, pi₁_pair]
      simpa only [hpa] using hV
    have hq' :
        (eventualGraph (normalizedArrowIndex V r)).val.Evalb
          ![pair (pi₁ s) (pi₂ s), y] := by
      simpa only [pair_unpair] using hq
    refine ⟨pair (pair ((normalizedArrowIndex V r : ℕ) : M) (pi₁ s))
        (pi₂ s), ?_,
      (eventualGraph_tauIndex_section_eval
        (normalizedArrowIndex V r) (pi₁ s) (pi₂ s) y).mpr hq'⟩
    apply (eventualGraph_tensorIndex_eval
      (normalizeIndex V .omega
        (parameterIndex (normalizedArrowIndex V r)))
      Kleene.identityIndex s _).mpr
    exact ⟨pair ((normalizedArrowIndex V r : ℕ) : M) (pi₁ s), pi₂ s,
      (eventualGraph_normalize_parameterIndex_eval V
        (normalizedArrowIndex V r) (pi₁ s) _).mpr ⟨hVa, rfl⟩,
      (eventualGraph_identityIndex_eval (pi₂ s) _).mpr rfl, rfl⟩

/-! ## Typed factorization and the Turing universal property -/

/-- Representative-level typed factorization for every raw index and every
coded parameter object. -/
theorem typedTau_factorization_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : STObjectCode) (r : ℕ) :
    nearProd_map
          (parameterArrow T (object T V) (normalizedArrowIndex V r))
          (𝟙 (omegaObject T)) ≫ typedTau T =
      arrowOfIndex T (.product V .omega) .omega r := by
  apply CodedHom.ext
  change (typedTau T).1 *
      tensorClass T
        (parameterArrow T (object T V) (normalizedArrowIndex V r)).1
        ((𝟙 (omegaObject T) : omegaObject T ⟶ omegaObject T).1) =
    (arrowOfIndex T (.product V .omega) .omega r).1
  rw [typedTau_val, parameterArrow_val, id_val, arrowOfIndex_val]
  change classOf T tauIndex *
      tensorClass T
        (classOf T (normalizeIndex V .omega
          (parameterIndex (normalizedArrowIndex V r))))
        (objectIdempotent T .omega) =
    classOf T (normalizeIndex (.product V .omega) .omega r)
  rw [objectIdempotent_omega, one_eq_classOf,
    tensorClass_classOf, mul_classOf]
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_turingFactorization T V r)

/-- The explicit fixed evaluator is a Turing morphism for the typed program
category.  The parameter object ranges over all coded objects. -/
theorem typedTau_isTuringMorphism
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    IsTuringMorphism (typedTau T) := by
  intro V phi
  obtain ⟨r, hr⟩ := exists_arrowOfIndex T
    (.product (objectCode V) .omega) .omega phi
  refine ⟨parameterArrow T V (normalizedArrowIndex (objectCode V) r),
    parameterArrow_isTotal T V _, ?_⟩
  exact (typedTau_factorization_arrowOfIndex T (objectCode V) r).trans hr

/-! ## Direct applications -/

/-- The second projection factors through the fixed Turing morphism by a
total parameter arrow. -/
theorem exists_factorization_secondProjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : CodedProgramCategory T) :
    ∃ g : V ⟶ omegaObject T,
      RestrictionCategory.isTotal g ∧
        nearProd_map g (𝟙 (omegaObject T)) ≫ typedTau T =
          p1 V (omegaObject T) :=
  typedTau_isTuringMorphism T V (p1 V (omegaObject T))

/-- The nowhere-defined typed arrow factors through the fixed Turing
morphism; no zero-morphism instance is required. -/
theorem exists_factorization_emptyArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (V : STObjectCode) :
    ∃ g : object T V ⟶ omegaObject T,
      RestrictionCategory.isTotal g ∧
        nearProd_map g (𝟙 (omegaObject T)) ≫ typedTau T =
          TypedCoproducts.emptyArrow T (.product V .omega) .omega :=
  typedTau_isTuringMorphism T (object T V)
    (TypedCoproducts.emptyArrow T (.product V .omega) .omega)

/-- The universal factorization applies when the parameter object is a coded
coproduct, not only when it is `Omega`. -/
theorem exists_factorization_coproductParameter
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode)
    (phi : nearProd (object T (.coproduct Q R)) (omegaObject T) ⟶
      omegaObject T) :
    ∃ g : object T (.coproduct Q R) ⟶ omegaObject T,
      RestrictionCategory.isTotal g ∧
        nearProd_map g (𝟙 (omegaObject T)) ≫ typedTau T = phi :=
  typedTau_isTuringMorphism T (object T (.coproduct Q R)) phi

end

end FailureOfComposition.TypedTuringMorphism
