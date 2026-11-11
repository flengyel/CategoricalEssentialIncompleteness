/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.TypedRanges
public import PCats.Coproducts

/-!
# Distributive coproducts on the typed program category

The coproduct of coded objects uses the existing value-first coding: the left
and right copies of a value `a` are `pair a 0` and `pair a 1`.  A coproduct of
programs evaluates only the component selected by the input tag.  Its graph is
realized by the maintained Sigma-one realization theorem, so the construction
does not require both component programs to terminate.

The resulting operation descends through uniform provable graph equality and
equips `CodedProgramCategory T` with the maintained `CoprodStruct` and
`HasCoproducts` interfaces.  Explicit rearrangement graphs then provide
inverses to the generic distributivity morphisms.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open Metamath.Feferman Arith.Feferman.Specialization

namespace FailureOfComposition.TypedCoproducts

open CodedObjectMembership ConcreteEvaluator ConcreteIndices ProofSearch
open SigmaOneRealization TypedProgramCategory TypedNearProduct TypedRanges
open UniformIndexQuotient
open PCategoryStruct CoprodStruct

noncomputable section

/-! ## Tagged-union graphs and selected indices -/

/-- The graph that runs `q` on a left-tagged input and `r` on a right-tagged
input, preserving the selected tag on the output. -/
def coprodGraph (q r : ℕ) : Graph :=
  .mkSigma “x y.
    (∃ a, ∃ b, !natPairFormula.val x a 0 ∧
      !natPairFormula.val y b 0 ∧ !(eventualGraph q).val a b) ∨
    (∃ a, ∃ b, !natPairFormula.val x a 1 ∧
      !natPairFormula.val y b 1 ∧ !(eventualGraph r).val a b)”

/-- The graph of the left injection from `Q`. -/
def leftInjectionGraph (Q : STObjectCode) : Graph :=
  .mkSigma “x y. !(memberFormula Q).val x ∧
    !natPairFormula.val y x 0”

/-- The graph of the right injection from `R`. -/
def rightInjectionGraph (R : STObjectCode) : Graph :=
  .mkSigma “x y. !(memberFormula R).val x ∧
    !natPairFormula.val y x 1”

/-- The graph that forgets either valid tag on a doubled copy of `Q`. -/
def codiagonalGraph (Q : STObjectCode) : Graph :=
  .mkSigma “x y.
    (∃ a, !natPairFormula.val x a 0 ∧
      !(memberFormula Q).val a ∧ y = a) ∨
    (∃ a, !natPairFormula.val x a 1 ∧
      !(memberFormula Q).val a ∧ y = a)”

@[simp] theorem coprodGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x y : M) :
    (coprodGraph q r).val.Evalb ![x, y] ↔
      (∃ a b : M, x = pair a 0 ∧ y = pair b 0 ∧
        (eventualGraph q).val.Evalb ![a, b]) ∨
      (∃ a b : M, x = pair a 1 ∧ y = pair b 1 ∧
        (eventualGraph r).val.Evalb ![a, b]) := by
  simp [coprodGraph]

@[simp] theorem leftInjectionGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (x y : M) :
    (leftInjectionGraph Q).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧ y = pair x 0 := by
  simp [leftInjectionGraph]

@[simp] theorem rightInjectionGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (R : STObjectCode) (x y : M) :
    (rightInjectionGraph R).val.Evalb ![x, y] ↔
      (memberFormula R).val.Evalb ![x] ∧ y = pair x 1 := by
  simp [rightInjectionGraph]

@[simp] theorem codiagonalGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (x y : M) :
    (codiagonalGraph Q).val.Evalb ![x, y] ↔
      (∃ a : M, x = pair a 0 ∧
        (memberFormula Q).val.Evalb ![a] ∧ y = a) ∨
      (∃ a : M, x = pair a 1 ∧
        (memberFormula Q).val.Evalb ![a] ∧ y = a) := by
  simp [codiagonalGraph]

/-- Tagged union is functional because the component graphs are functional and
the two tags are disjoint. -/
theorem coprodGraph_functional (q r : ℕ) : Functional (coprodGraph q r) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rcases (coprodGraph_eval q r x y).mp hy with
      ⟨a, b, hxa, hyb, hq⟩ | ⟨a, b, hxa, hyb, hr⟩ <;>
    rcases (coprodGraph_eval q r x z).mp hz with
      ⟨a', c, hxa', hzc, hq'⟩ | ⟨a', c, hxa', hzc, hr'⟩
  · have haa : a = a' :=
      (pair_eq_pair_iff a 0 a' 0).mp (hxa.symm.trans hxa') |>.1
    subst a'
    have hbc : b = c := eventualGraph_output_unique q a b c hq hq'
    exact hyb.trans (congrArg (fun u => pair u (0 : M)) hbc) |>.trans hzc.symm
  · have h01 : (0 : M) = 1 :=
      (pair_eq_pair_iff a 0 a' 1).mp (hxa.symm.trans hxa') |>.2
    exact False.elim (zero_ne_one h01)
  · have h10 : (1 : M) = 0 :=
      (pair_eq_pair_iff a 1 a' 0).mp (hxa.symm.trans hxa') |>.2
    exact False.elim (Arithmetic.one_ne_zero h10)
  · have haa : a = a' :=
      (pair_eq_pair_iff a 1 a' 1).mp (hxa.symm.trans hxa') |>.1
    subst a'
    have hbc : b = c := eventualGraph_output_unique r a b c hr hr'
    exact hyb.trans (congrArg (fun u => pair u (1 : M)) hbc) |>.trans hzc.symm

theorem leftInjectionGraph_functional (Q : STObjectCode) :
    Functional (leftInjectionGraph Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((leftInjectionGraph_eval Q x y).mp hy).2.trans
    ((leftInjectionGraph_eval Q x z).mp hz).2.symm

theorem rightInjectionGraph_functional (R : STObjectCode) :
    Functional (rightInjectionGraph R) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  exact ((rightInjectionGraph_eval R x y).mp hy).2.trans
    ((rightInjectionGraph_eval R x z).mp hz).2.symm

theorem codiagonalGraph_functional (Q : STObjectCode) :
    Functional (codiagonalGraph Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rcases (codiagonalGraph_eval Q x y).mp hy with
      ⟨a, hxa, -, hya⟩ | ⟨a, hxa, -, hya⟩ <;>
    rcases (codiagonalGraph_eval Q x z).mp hz with
      ⟨b, hxb, -, hzb⟩ | ⟨b, hxb, -, hzb⟩
  · have hab : a = b :=
      (pair_eq_pair_iff a 0 b 0).mp (hxa.symm.trans hxb) |>.1
    exact hya.trans hab |>.trans hzb.symm
  · have h01 : (0 : M) = 1 :=
      (pair_eq_pair_iff a 0 b 1).mp (hxa.symm.trans hxb) |>.2
    exact False.elim (zero_ne_one h01)
  · have h10 : (1 : M) = 0 :=
      (pair_eq_pair_iff a 1 b 0).mp (hxa.symm.trans hxb) |>.2
    exact False.elim (Arithmetic.one_ne_zero h10)
  · have hab : a = b :=
      (pair_eq_pair_iff a 1 b 1).mp (hxa.symm.trans hxb) |>.1
    exact hya.trans hab |>.trans hzb.symm

/-- A selected realizer of the output-preserving tagged union. -/
def coprodIndex (q r : ℕ) : ℕ :=
  Classical.choose (realize_graph (coprodGraph q r)
    (coprodGraph_functional q r))

/-- A selected realizer of the left-injection graph. -/
def leftInjectionIndex (Q : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (leftInjectionGraph Q)
    (leftInjectionGraph_functional Q))

/-- A selected realizer of the right-injection graph. -/
def rightInjectionIndex (R : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (rightInjectionGraph R)
    (rightInjectionGraph_functional R))

/-- A selected realizer of the codiagonal graph. -/
def codiagonalIndex (Q : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (codiagonalGraph Q)
    (codiagonalGraph_functional Q))

theorem coprodIndex_uniform (q r : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (coprodIndex q r)) (coprodGraph q r) :=
  Classical.choose_spec (realize_graph (coprodGraph q r)
    (coprodGraph_functional q r))

theorem leftInjectionIndex_uniform (Q : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (leftInjectionIndex Q))
      (leftInjectionGraph Q) :=
  Classical.choose_spec (realize_graph (leftInjectionGraph Q)
    (leftInjectionGraph_functional Q))

theorem rightInjectionIndex_uniform (R : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (rightInjectionIndex R))
      (rightInjectionGraph R) :=
  Classical.choose_spec (realize_graph (rightInjectionGraph R)
    (rightInjectionGraph_functional R))

theorem codiagonalIndex_uniform (Q : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (codiagonalIndex Q))
      (codiagonalGraph Q) :=
  Classical.choose_spec (realize_graph (codiagonalGraph Q)
    (codiagonalGraph_functional Q))

@[simp] theorem eventualGraph_coprodIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (x y : M) :
    (eventualGraph (coprodIndex q r)).val.Evalb ![x, y] ↔
      (∃ a b : M, x = pair a 0 ∧ y = pair b 0 ∧
        (eventualGraph q).val.Evalb ![a, b]) ∨
      (∃ a b : M, x = pair a 1 ∧ y = pair b 1 ∧
        (eventualGraph r).val.Evalb ![a, b]) := by
  have h := consequence_iff.mp (Theory.Proof.sound (coprodIndex_uniform q r))
    M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (coprodGraph_eval q r x y)

@[simp] theorem eventualGraph_leftInjectionIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (x y : M) :
    (eventualGraph (leftInjectionIndex Q)).val.Evalb ![x, y] ↔
      (memberFormula Q).val.Evalb ![x] ∧ y = pair x 0 := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (leftInjectionIndex_uniform Q)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (leftInjectionGraph_eval Q x y)

@[simp] theorem eventualGraph_rightInjectionIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (R : STObjectCode) (x y : M) :
    (eventualGraph (rightInjectionIndex R)).val.Evalb ![x, y] ↔
      (memberFormula R).val.Evalb ![x] ∧ y = pair x 1 := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (rightInjectionIndex_uniform R)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (rightInjectionGraph_eval R x y)

@[simp] theorem eventualGraph_codiagonalIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q : STObjectCode) (x y : M) :
    (eventualGraph (codiagonalIndex Q)).val.Evalb ![x, y] ↔
      (∃ a : M, x = pair a 0 ∧
        (memberFormula Q).val.Evalb ![a] ∧ y = a) ∨
      (∃ a : M, x = pair a 1 ∧
        (memberFormula Q).val.Evalb ![a] ∧ y = a) := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (codiagonalIndex_uniform Q)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h x y).trans (codiagonalGraph_eval Q x y)

/-! ## Normalized representatives and quotient descent -/

/-- The selected coproduct index of the two actual normalized typed
representatives. -/
def typedCoprodIndex (Q R S U : STObjectCode) (q r : ℕ) : ℕ :=
  coprodIndex (normalizeIndex Q R q) (normalizeIndex S U r)

/-- The normalized tagged-union graph. -/
def typedCoprodGraph (Q R S U : STObjectCode) (q r : ℕ) : Graph :=
  coprodGraph (normalizeIndex Q R q) (normalizeIndex S U r)

@[simp] theorem eventualGraph_typedCoprodIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R S U : STObjectCode) (q r : ℕ) (x y : M) :
    (eventualGraph (typedCoprodIndex Q R S U q r)).val.Evalb ![x, y] ↔
      (∃ a b : M, x = pair a 0 ∧ y = pair b 0 ∧
        (memberFormula Q).val.Evalb ![a] ∧
        (eventualGraph q).val.Evalb ![a, b] ∧
        (memberFormula R).val.Evalb ![b]) ∨
      (∃ a b : M, x = pair a 1 ∧ y = pair b 1 ∧
        (memberFormula S).val.Evalb ![a] ∧
        (eventualGraph r).val.Evalb ![a, b] ∧
        (memberFormula U).val.Evalb ![b]) := by
  rw [typedCoprodIndex, eventualGraph_coprodIndex_eval]
  constructor
  · rintro (⟨a, b, hx, hy, hq⟩ | ⟨a, b, hx, hy, hr⟩)
    · obtain ⟨hQ, hq, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a b).mp hq
      exact Or.inl ⟨a, b, hx, hy, hQ, hq, hR⟩
    · obtain ⟨hS, hr, hU⟩ :=
        (eventualGraph_normalizeIndex_eval S U r a b).mp hr
      exact Or.inr ⟨a, b, hx, hy, hS, hr, hU⟩
  · rintro (⟨a, b, hx, hy, hQ, hq, hR⟩ |
      ⟨a, b, hx, hy, hS, hr, hU⟩)
    · exact Or.inl ⟨a, b, hx, hy,
        (eventualGraph_normalizeIndex_eval Q R q a b).mpr ⟨hQ, hq, hR⟩⟩
    · exact Or.inr ⟨a, b, hx, hy,
        (eventualGraph_normalizeIndex_eval S U r a b).mpr ⟨hS, hr, hU⟩⟩

/-- PA-uniform graph equation for the normalized coproduct representative. -/
theorem typedCoprodIndex_uniform
    (Q R S U : STObjectCode) (q r : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (typedCoprodIndex Q R S U q r))
      (typedCoprodGraph Q R S U q r) :=
  coprodIndex_uniform (normalizeIndex Q R q) (normalizeIndex S U r)

/-- A selected coproduct program rejects every input whose tag is neither
`0` nor `1`; the unselected branch is not evaluated. -/
theorem not_eventualGraph_coprodIndex_pair_of_tag_ne
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : ℕ) (a t y : M) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    ¬(eventualGraph (coprodIndex q r)).val.Evalb ![pair a t, y] := by
  rw [eventualGraph_coprodIndex_eval]
  rintro (⟨u, v, hx, -, -⟩ | ⟨u, v, hx, -, -⟩)
  · exact h0 ((pair_eq_pair_iff a t u 0).mp hx).2
  · exact h1 ((pair_eq_pair_iff a t u 1).mp hx).2

/-- Tagged union preserves uniform equality over every theory extending PA. -/
theorem eqIndex_coprod_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {q q' r r' : ℕ} (hq : EqIndex T q q') (hr : EqIndex T r r') :
    EqIndex T (coprodIndex q r) (coprodIndex q' r') := by
  apply complete.{0} T
  intro M _ hM
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hq' := consequence_iff.mp (Theory.Proof.sound hq) M hM
  have hr' := consequence_iff.mp (Theory.Proof.sound hr) M hM
  simp only [models_iff, uniformSentence_eval] at hq' hr' ⊢
  intro x y
  rw [eventualGraph_coprodIndex_eval, eventualGraph_coprodIndex_eval]
  constructor
  · rintro (⟨a, b, hx, hy, hab⟩ | ⟨a, b, hx, hy, hab⟩)
    · exact Or.inl ⟨a, b, hx, hy, (hq' a b).mp hab⟩
    · exact Or.inr ⟨a, b, hx, hy, (hr' a b).mp hab⟩
  · rintro (⟨a, b, hx, hy, hab⟩ | ⟨a, b, hx, hy, hab⟩)
    · exact Or.inl ⟨a, b, hx, hy, (hq' a b).mpr hab⟩
    · exact Or.inr ⟨a, b, hx, hy, (hr' a b).mpr hab⟩

/-- Coproduct on quotient programs. -/
def coprodClass (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    ProgramQuotient T → ProgramQuotient T → ProgramQuotient T :=
  Quotient.lift₂
    (fun q r => classOf T (coprodIndex q r))
    (fun _ _ _ _ hq hr => Quotient.sound (eqIndex_coprod_congr T hq hr))

@[simp] theorem coprodClass_classOf
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q r : ℕ) :
    coprodClass T (classOf T q) (classOf T r) =
      classOf T (coprodIndex q r) :=
  rfl

/-! ## Algebra of quotient coproducts -/

/-- Tagged union commutes with program composition. -/
theorem eqIndex_coprod_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b c d : ℕ) :
    EqIndex T (coprodIndex (compIndex a b) (compIndex c d))
      (compIndex (coprodIndex a c) (coprodIndex b d)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    rcases (eventualGraph_coprodIndex_eval _ _ x y).mp h with
      ⟨u, v, hx, hy, huv⟩ | ⟨u, v, hx, hy, huv⟩
    · obtain ⟨w, hbw, hav⟩ := (eventualGraph_comp_eval a b u v).mp huv
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨pair w 0, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval b d x _).mpr
          (Or.inl ⟨u, w, hx, rfl, hbw⟩)
      · exact (eventualGraph_coprodIndex_eval a c _ y).mpr
          (Or.inl ⟨w, v, rfl, hy, hav⟩)
    · obtain ⟨w, hdw, hcv⟩ := (eventualGraph_comp_eval c d u v).mp huv
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨pair w 1, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval b d x _).mpr
          (Or.inr ⟨u, w, hx, rfl, hdw⟩)
      · exact (eventualGraph_coprodIndex_eval a c _ y).mpr
          (Or.inr ⟨w, v, rfl, hy, hcv⟩)
  · intro h
    obtain ⟨p, hp, hpy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    rcases (eventualGraph_coprodIndex_eval b d x p).mp hp with
      ⟨u, w, hx, hpw, hbw⟩ | ⟨u, w, hx, hpw, hdw⟩
    · rcases (eventualGraph_coprodIndex_eval a c p y).mp hpy with
        ⟨w', v, hpw', hy, haw⟩ | ⟨w', v, hpw', hy, hcw⟩
      · have hww : w = w' :=
          (pair_eq_pair_iff w 0 w' 0).mp (hpw.symm.trans hpw') |>.1
        subst w'
        exact (eventualGraph_coprodIndex_eval _ _ x y).mpr
          (Or.inl ⟨u, v, hx, hy,
            (eventualGraph_comp_eval a b u v).mpr ⟨w, hbw, haw⟩⟩)
      · have h01 : (0 : M) = 1 :=
          (pair_eq_pair_iff w 0 w' 1).mp (hpw.symm.trans hpw') |>.2
        exact False.elim (zero_ne_one h01)
    · rcases (eventualGraph_coprodIndex_eval a c p y).mp hpy with
        ⟨w', v, hpw', hy, haw⟩ | ⟨w', v, hpw', hy, hcw⟩
      · have h10 : (1 : M) = 0 :=
          (pair_eq_pair_iff w 1 w' 0).mp (hpw.symm.trans hpw') |>.2
        exact False.elim (Arithmetic.one_ne_zero h10)
      · have hww : w = w' :=
          (pair_eq_pair_iff w 1 w' 1).mp (hpw.symm.trans hpw') |>.1
        subst w'
        exact (eventualGraph_coprodIndex_eval _ _ x y).mpr
          (Or.inr ⟨u, v, hx, hy,
            (eventualGraph_comp_eval c d u v).mpr ⟨w, hdw, hcw⟩⟩)

/-- Coproduct of quotient programs is multiplicative in both variables. -/
theorem coprodClass_mul
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a b c d : ProgramQuotient T) :
    coprodClass T (a * b) (c * d) =
      coprodClass T a c * coprodClass T b d := by
  refine Quotient.inductionOn a ?_
  intro a
  refine Quotient.inductionOn b ?_
  intro b
  refine Quotient.inductionOn c ?_
  intro c
  refine Quotient.inductionOn d ?_
  intro d
  change classOf T (coprodIndex (compIndex a b) (compIndex c d)) =
    classOf T (compIndex (coprodIndex a c) (coprodIndex b d))
  exact (classOf_eq_classOf_iff T _ _).mpr (eqIndex_coprod_comp T a b c d)

/-- The coproduct of the two selected object identities is the selected
identity of the coproduct object. -/
theorem eqIndex_coprod_delta
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    EqIndex T (coprodIndex (deltaIndex Q) (deltaIndex R))
      (deltaIndex (.coproduct Q R)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    rcases (eventualGraph_coprodIndex_eval _ _ x y).mp h with
      ⟨a, b, hx, hy, hQ⟩ | ⟨a, b, hx, hy, hR⟩
    · obtain ⟨ha, hba⟩ := (eventualGraph_deltaIndex_eval Q a b).mp hQ
      apply (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mpr
      refine ⟨(memberFormula_coproduct_eval Q R x).mpr
        (Or.inl ⟨a, hx, ha⟩), ?_⟩
      exact hy.trans (congrArg (fun u => pair u (0 : M)) hba) |>.trans hx.symm
    · obtain ⟨ha, hba⟩ := (eventualGraph_deltaIndex_eval R a b).mp hR
      apply (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mpr
      refine ⟨(memberFormula_coproduct_eval Q R x).mpr
        (Or.inr ⟨a, hx, ha⟩), ?_⟩
      exact hy.trans (congrArg (fun u => pair u (1 : M)) hba) |>.trans hx.symm
  · intro h
    obtain ⟨hQR, hyx⟩ :=
      (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mp h
    rcases (memberFormula_coproduct_eval Q R x).mp hQR with
      ⟨a, hx, hQ⟩ | ⟨a, hx, hR⟩
    · exact (eventualGraph_coprodIndex_eval _ _ x y).mpr
        (Or.inl ⟨a, a, hx, hyx.trans hx,
          (eventualGraph_deltaIndex_eval Q a a).mpr ⟨hQ, rfl⟩⟩)
    · exact (eventualGraph_coprodIndex_eval _ _ x y).mpr
        (Or.inr ⟨a, a, hx, hyx.trans hx,
          (eventualGraph_deltaIndex_eval R a a).mpr ⟨hR, rfl⟩⟩)

/-- The quotient idempotent of a coproduct object is the coproduct of the two
factor idempotents. -/
theorem objectIdempotent_coproduct
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    objectIdempotent T (.coproduct Q R) =
      coprodClass T (objectIdempotent T Q) (objectIdempotent T R) := by
  change classOf T (deltaIndex (.coproduct Q R)) =
    classOf T (coprodIndex (deltaIndex Q) (deltaIndex R))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_symm (eqIndex_coprod_delta T Q R))

/-! ## Typed coproduct maps -/

/-- Coproduct of two typed arrows. -/
def typedCoprodMap
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y Z : CodedProgramCategory T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    object T (.coproduct (objectCode W) (objectCode Y)) ⟶
      object T (.coproduct (objectCode X) (objectCode Z)) :=
  ⟨coprodClass T f.1 g.1, by
    constructor
    · change objectIdempotent T (.coproduct (objectCode X) (objectCode Z)) *
          coprodClass T f.1 g.1 = coprodClass T f.1 g.1
      rw [objectIdempotent_coproduct, ← coprodClass_mul]
      rw [f.2.1, g.2.1]
    · change coprodClass T f.1 g.1 *
          objectIdempotent T (.coproduct (objectCode W) (objectCode Y)) =
        coprodClass T f.1 g.1
      rw [objectIdempotent_coproduct, ← coprodClass_mul]
      rw [f.2.2, g.2.2]⟩

@[simp] theorem typedCoprodMap_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {W X Y Z : CodedProgramCategory T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    (typedCoprodMap T f g).1 = coprodClass T f.1 g.1 :=
  rfl

/-- Exact normalized representative equation for a coproduct map. -/
theorem typedCoprodMap_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S U : STObjectCode) (q r : ℕ) :
    typedCoprodMap T (arrowOfIndex T Q R q) (arrowOfIndex T S U r) =
      arrowOfIndex T (.coproduct Q S) (.coproduct R U)
        (typedCoprodIndex Q R S U q r) := by
  symm
  apply arrowOfIndex_eq_of_class
  rw [typedCoprodMap_val, arrowOfIndex_val, arrowOfIndex_val,
    coprodClass_classOf]
  rfl

/-! ## Injections, codiagonal, and typed coproduct data -/

/-- The selected left injection has exactly the declared source and target
support. -/
theorem pa_proves_leftInjection_support (Q R : STObjectCode) :
    𝗣𝗔 ⊢ supportSentence Q (.coproduct Q R) (leftInjectionIndex Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro x y hxy
  obtain ⟨hQ, hy⟩ := (eventualGraph_leftInjectionIndex_eval Q x y).mp hxy
  refine ⟨hQ, ?_⟩
  rw [hy]
  exact (memberFormula_coproduct_left_pair_eval Q R x).mpr hQ

/-- The selected right injection has exactly the declared source and target
support. -/
theorem pa_proves_rightInjection_support (Q R : STObjectCode) :
    𝗣𝗔 ⊢ supportSentence R (.coproduct Q R) (rightInjectionIndex R) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro x y hxy
  obtain ⟨hR, hy⟩ := (eventualGraph_rightInjectionIndex_eval R x y).mp hxy
  refine ⟨hR, ?_⟩
  rw [hy]
  exact (memberFormula_coproduct_right_pair_eval Q R x).mpr hR

/-- The selected codiagonal has exactly the declared source and target
support. -/
theorem pa_proves_codiagonal_support (Q : STObjectCode) :
    𝗣𝗔 ⊢ supportSentence (.coproduct Q Q) Q (codiagonalIndex Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro x y hxy
  rcases (eventualGraph_codiagonalIndex_eval Q x y).mp hxy with
    ⟨a, hx, hQ, hy⟩ | ⟨a, hx, hQ, hy⟩
  · exact ⟨(memberFormula_coproduct_eval Q Q x).mpr
      (Or.inl ⟨a, hx, hQ⟩), by simpa only [hy] using hQ⟩
  · exact ⟨(memberFormula_coproduct_eval Q Q x).mpr
      (Or.inr ⟨a, hx, hQ⟩), by simpa only [hy] using hQ⟩

theorem eqIndex_normalize_leftInjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    EqIndex T
      (normalizeIndex Q (.coproduct Q R) (leftInjectionIndex Q))
      (leftInjectionIndex Q) :=
  (proves_support_iff_eqIndex_normalize T Q (.coproduct Q R)
    (leftInjectionIndex Q)).mp
      (WeakerThan.pbl (pa_proves_leftInjection_support Q R))

theorem eqIndex_normalize_rightInjection
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    EqIndex T
      (normalizeIndex R (.coproduct Q R) (rightInjectionIndex R))
      (rightInjectionIndex R) :=
  (proves_support_iff_eqIndex_normalize T R (.coproduct Q R)
    (rightInjectionIndex R)).mp
      (WeakerThan.pbl (pa_proves_rightInjection_support Q R))

theorem eqIndex_normalize_codiagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    EqIndex T
      (normalizeIndex (.coproduct Q Q) Q (codiagonalIndex Q))
      (codiagonalIndex Q) :=
  (proves_support_iff_eqIndex_normalize T (.coproduct Q Q) Q
    (codiagonalIndex Q)).mp
      (WeakerThan.pbl (pa_proves_codiagonal_support Q))

/-- Quotient class of the selected left injection from `Q`. -/
def leftInjectionClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    ProgramQuotient T :=
  classOf T (leftInjectionIndex Q)

/-- Quotient class of the selected right injection from `R`. -/
def rightInjectionClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (R : STObjectCode) :
    ProgramQuotient T :=
  classOf T (rightInjectionIndex R)

/-- Quotient class of the selected codiagonal on `Q`. -/
def codiagonalClass
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    ProgramQuotient T :=
  classOf T (codiagonalIndex Q)

/-- The typed left injection. -/
def typedI0
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    Q ⟶ object T (.coproduct (objectCode Q) (objectCode R)) :=
  arrowOfIndex T (objectCode Q) (.coproduct (objectCode Q) (objectCode R))
    (leftInjectionIndex (objectCode Q))

/-- The typed right injection. -/
def typedI1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    R ⟶ object T (.coproduct (objectCode Q) (objectCode R)) :=
  arrowOfIndex T (objectCode R) (.coproduct (objectCode Q) (objectCode R))
    (rightInjectionIndex (objectCode R))

/-- The typed codiagonal. -/
def typedCodiag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    object T (.coproduct (objectCode Q) (objectCode Q)) ⟶ Q :=
  arrowOfIndex T (.coproduct (objectCode Q) (objectCode Q)) (objectCode Q)
    (codiagonalIndex (objectCode Q))

@[simp] theorem typedI0_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    (typedI0 T Q R).1 = leftInjectionClass T (objectCode Q) := by
  rw [typedI0, arrowOfIndex_val, leftInjectionClass,
    classOf_eq_classOf_iff]
  exact eqIndex_normalize_leftInjection T (objectCode Q) (objectCode R)

@[simp] theorem typedI1_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    (typedI1 T Q R).1 = rightInjectionClass T (objectCode R) := by
  rw [typedI1, arrowOfIndex_val, rightInjectionClass,
    classOf_eq_classOf_iff]
  exact eqIndex_normalize_rightInjection T (objectCode Q) (objectCode R)

@[simp] theorem typedCodiag_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : CodedProgramCategory T) :
    (typedCodiag T Q).1 = codiagonalClass T (objectCode Q) := by
  rw [typedCodiag, arrowOfIndex_val, codiagonalClass,
    classOf_eq_classOf_iff]
  exact eqIndex_normalize_codiagonal T (objectCode Q)

/-- Concrete coproduct data on the typed program category. -/
instance codedProgramCategoryCoprodStruct
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    CoprodStruct (CodedProgramCategory T) where
  coprod Q R := object T (.coproduct (objectCode Q) (objectCode R))
  coprod_map := typedCoprodMap T
  codiag := typedCodiag T
  i0 := typedI0 T
  i1 := typedI1 T

@[simp] theorem coprod_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    coprod (object T Q) (object T R) = object T (.coproduct Q R) :=
  rfl

@[simp] theorem objectCode_coprod
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : CodedProgramCategory T) :
    objectCode (coprod Q R) = .coproduct (objectCode Q) (objectCode R) :=
  rfl

@[simp] theorem coprod_map_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R S U : STObjectCode) (q r : ℕ) :
    coprod_map (arrowOfIndex T Q R q) (arrowOfIndex T S U r) =
      arrowOfIndex T (.coproduct Q S) (.coproduct R U)
        (typedCoprodIndex Q R S U q r) :=
  typedCoprodMap_arrowOfIndex T Q R S U q r

@[simp] theorem i0_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    i0 (object T Q) (object T R) =
      arrowOfIndex T Q (.coproduct Q R) (leftInjectionIndex Q) :=
  rfl

@[simp] theorem i1_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    i1 (object T Q) (object T R) =
      arrowOfIndex T R (.coproduct Q R) (rightInjectionIndex R) :=
  rfl

@[simp] theorem codiag_object
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    codiag (object T Q) =
      arrowOfIndex T (.coproduct Q Q) Q (codiagonalIndex Q) :=
  rfl

/-! ## Structural coproduct equations -/

theorem eqIndex_left_codiagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    EqIndex T (compIndex (codiagonalIndex Q) (leftInjectionIndex Q))
      (deltaIndex Q) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hp'⟩ :=
      (eventualGraph_leftInjectionIndex_eval Q x p).mp hp
    rcases (eventualGraph_codiagonalIndex_eval Q p y).mp hy with
      ⟨a, hpa, -, hya⟩ | ⟨a, hpa, -, -⟩
    · have hxa : x = a :=
        (pair_eq_pair_iff x 0 a 0).mp (hp'.symm.trans hpa) |>.1
      exact (eventualGraph_deltaIndex_eval Q x y).mpr
        ⟨hQ, hya.trans hxa.symm⟩
    · have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff x 0 a 1).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (zero_ne_one h01)
  · intro h
    obtain ⟨hQ, hyx⟩ := (eventualGraph_deltaIndex_eval Q x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 0,
      (eventualGraph_leftInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (eventualGraph_codiagonalIndex_eval Q _ y).mpr
      (Or.inl ⟨x, rfl, hQ, hyx⟩)

theorem eqIndex_right_codiagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q : STObjectCode) :
    EqIndex T (compIndex (codiagonalIndex Q) (rightInjectionIndex Q))
      (deltaIndex Q) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hp'⟩ :=
      (eventualGraph_rightInjectionIndex_eval Q x p).mp hp
    rcases (eventualGraph_codiagonalIndex_eval Q p y).mp hy with
      ⟨a, hpa, -, -⟩ | ⟨a, hpa, -, hya⟩
    · have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff x 1 a 0).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · have hxa : x = a :=
        (pair_eq_pair_iff x 1 a 1).mp (hp'.symm.trans hpa) |>.1
      exact (eventualGraph_deltaIndex_eval Q x y).mpr
        ⟨hQ, hya.trans hxa.symm⟩
  · intro h
    obtain ⟨hQ, hyx⟩ := (eventualGraph_deltaIndex_eval Q x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 1,
      (eventualGraph_rightInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (eventualGraph_codiagonalIndex_eval Q _ y).mpr
      (Or.inr ⟨x, rfl, hQ, hyx⟩)

/-- Coproduct of the two injections followed by the codiagonal is the
identity of the coproduct object. -/
theorem eqIndex_coprod_injections_codiagonal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (Q R : STObjectCode) :
    EqIndex T
      (compIndex (codiagonalIndex (.coproduct Q R))
        (coprodIndex (leftInjectionIndex Q) (rightInjectionIndex R)))
      (deltaIndex (.coproduct Q R)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hpy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    rcases (eventualGraph_coprodIndex_eval _ _ x p).mp hp with
      ⟨a, b, hxa, hpb, hinl⟩ | ⟨a, b, hxa, hpb, hinr⟩
    · obtain ⟨hQ, hb⟩ :=
        (eventualGraph_leftInjectionIndex_eval Q a b).mp hinl
      rcases (eventualGraph_codiagonalIndex_eval (.coproduct Q R) p y).mp hpy with
        ⟨c, hpc, -, hyc⟩ | ⟨c, hpc, -, -⟩
      · have hbc : b = c :=
          (pair_eq_pair_iff b 0 c 0).mp (hpb.symm.trans hpc) |>.1
        have hba : b = pair a 0 := hb
        apply (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mpr
        refine ⟨(memberFormula_coproduct_eval Q R x).mpr
          (Or.inl ⟨a, hxa, hQ⟩), ?_⟩
        exact hyc.trans hbc.symm |>.trans hba |>.trans hxa.symm
      · have h01 : (0 : M) = 1 :=
          (pair_eq_pair_iff b 0 c 1).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (zero_ne_one h01)
    · obtain ⟨hR, hb⟩ :=
        (eventualGraph_rightInjectionIndex_eval R a b).mp hinr
      rcases (eventualGraph_codiagonalIndex_eval (.coproduct Q R) p y).mp hpy with
        ⟨c, hpc, -, -⟩ | ⟨c, hpc, -, hyc⟩
      · have h10 : (1 : M) = 0 :=
          (pair_eq_pair_iff b 1 c 0).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (Arithmetic.one_ne_zero h10)
      · have hbc : b = c :=
          (pair_eq_pair_iff b 1 c 1).mp (hpb.symm.trans hpc) |>.1
        have hba : b = pair a 1 := hb
        apply (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mpr
        refine ⟨(memberFormula_coproduct_eval Q R x).mpr
          (Or.inr ⟨a, hxa, hR⟩), ?_⟩
        exact hyc.trans hbc.symm |>.trans hba |>.trans hxa.symm
  · intro h
    obtain ⟨hQR, hyx⟩ :=
      (eventualGraph_deltaIndex_eval (.coproduct Q R) x y).mp h
    rcases (memberFormula_coproduct_eval Q R x).mp hQR with
      ⟨a, hxa, hQ⟩ | ⟨a, hxa, hR⟩
    · let b : M := pair a 0
      let p : M := pair b 0
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨p, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval _ _ x p).mpr
          (Or.inl ⟨a, b, hxa, rfl,
            (eventualGraph_leftInjectionIndex_eval Q a b).mpr ⟨hQ, rfl⟩⟩)
      · exact (eventualGraph_codiagonalIndex_eval (.coproduct Q R) p y).mpr
          (Or.inl ⟨b, rfl,
            (memberFormula_coproduct_left_pair_eval Q R a).mpr hQ,
            hyx.trans hxa⟩)
    · let b : M := pair a 1
      let p : M := pair b 1
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨p, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval _ _ x p).mpr
          (Or.inr ⟨a, b, hxa, rfl,
            (eventualGraph_rightInjectionIndex_eval R a b).mpr ⟨hR, rfl⟩⟩)
      · exact (eventualGraph_codiagonalIndex_eval (.coproduct Q R) p y).mpr
          (Or.inr ⟨b, rfl,
            (memberFormula_coproduct_right_pair_eval Q R a).mpr hR,
            hyx.trans hxa⟩)

/-- Naturality of the selected codiagonal for a normalized representative. -/
theorem eqIndex_codiagonal_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (codiagonalIndex R)
        (coprodIndex (normalizeIndex Q R q) (normalizeIndex Q R q)))
      (compIndex (normalizeIndex Q R q) (codiagonalIndex Q)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hp, hpy⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    rcases (eventualGraph_coprodIndex_eval _ _ x p).mp hp with
      ⟨a, b, hxa, hpb, hq⟩ | ⟨a, b, hxa, hpb, hq⟩
    · obtain ⟨hQ, hqraw, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a b).mp hq
      rcases (eventualGraph_codiagonalIndex_eval R p y).mp hpy with
        ⟨c, hpc, -, hyc⟩ | ⟨c, hpc, -, -⟩
      · have hbc : b = c :=
          (pair_eq_pair_iff b 0 c 0).mp (hpb.symm.trans hpc) |>.1
        apply (eventualGraph_comp_eval _ _ x y).mpr
        refine ⟨a, (eventualGraph_codiagonalIndex_eval Q x a).mpr
          (Or.inl ⟨a, hxa, hQ, rfl⟩), ?_⟩
        exact (eventualGraph_normalizeIndex_eval Q R q a y).mpr
          ⟨hQ, by simpa only [hbc, hyc] using hqraw,
            by simpa only [hbc, hyc] using hR⟩
      · have h01 : (0 : M) = 1 :=
          (pair_eq_pair_iff b 0 c 1).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (zero_ne_one h01)
    · obtain ⟨hQ, hqraw, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a b).mp hq
      rcases (eventualGraph_codiagonalIndex_eval R p y).mp hpy with
        ⟨c, hpc, -, -⟩ | ⟨c, hpc, -, hyc⟩
      · have h10 : (1 : M) = 0 :=
          (pair_eq_pair_iff b 1 c 0).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (Arithmetic.one_ne_zero h10)
      · have hbc : b = c :=
          (pair_eq_pair_iff b 1 c 1).mp (hpb.symm.trans hpc) |>.1
        apply (eventualGraph_comp_eval _ _ x y).mpr
        refine ⟨a, (eventualGraph_codiagonalIndex_eval Q x a).mpr
          (Or.inr ⟨a, hxa, hQ, rfl⟩), ?_⟩
        exact (eventualGraph_normalizeIndex_eval Q R q a y).mpr
          ⟨hQ, by simpa only [hbc, hyc] using hqraw,
            by simpa only [hbc, hyc] using hR⟩
  · intro h
    obtain ⟨a, hxa, hq⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    rcases (eventualGraph_codiagonalIndex_eval Q x a).mp hxa with
      ⟨u, hxu, hQ, hau⟩ | ⟨u, hxu, hQ, hau⟩
    · obtain ⟨hQ', hqraw, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a y).mp hq
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨pair y 0, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval _ _ x _).mpr
          (Or.inl ⟨u, y, hxu, rfl,
            by simpa only [hau] using hq⟩)
      · exact (eventualGraph_codiagonalIndex_eval R _ y).mpr
          (Or.inl ⟨y, rfl, hR, rfl⟩)
    · obtain ⟨hQ', hqraw, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a y).mp hq
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨pair y 1, ?_, ?_⟩
      · exact (eventualGraph_coprodIndex_eval _ _ x _).mpr
          (Or.inr ⟨u, y, hxu, rfl,
            by simpa only [hau] using hq⟩)
      · exact (eventualGraph_codiagonalIndex_eval R _ y).mpr
          (Or.inr ⟨y, rfl, hR, rfl⟩)

/-- Naturality of the left injection in its active variable. -/
theorem eqIndex_leftInjection_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R Z : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (leftInjectionIndex R) (normalizeIndex Q R q))
      (compIndex
        (coprodIndex (normalizeIndex Q R q) (deltaIndex Z))
        (leftInjectionIndex Q)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨b, hq, hinl⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hqraw, hR⟩ :=
      (eventualGraph_normalizeIndex_eval Q R q x b).mp hq
    obtain ⟨-, hy⟩ := (eventualGraph_leftInjectionIndex_eval R b y).mp hinl
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 0,
      (eventualGraph_leftInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (eventualGraph_coprodIndex_eval _ _ _ y).mpr
      (Or.inl ⟨x, b, rfl, hy,
        (eventualGraph_normalizeIndex_eval Q R q x b).mpr
          ⟨hQ, hqraw, hR⟩⟩)
  · intro h
    obtain ⟨p, hinl, hp⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hp'⟩ :=
      (eventualGraph_leftInjectionIndex_eval Q x p).mp hinl
    rcases (eventualGraph_coprodIndex_eval _ _ p y).mp hp with
      ⟨a, b, hpa, hy, hq⟩ | ⟨a, b, hpa, -, -⟩
    · have hxa : x = a :=
        (pair_eq_pair_iff x 0 a 0).mp (hp'.symm.trans hpa) |>.1
      obtain ⟨-, -, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a b).mp hq
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨b, by simpa only [hxa] using hq, ?_⟩
      exact (eventualGraph_leftInjectionIndex_eval R b y).mpr ⟨hR, hy⟩
    · have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff x 0 a 1).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (zero_ne_one h01)

/-- Naturality of the right injection in its active variable. -/
theorem eqIndex_rightInjection_natural
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R Z : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (rightInjectionIndex R) (normalizeIndex Q R q))
      (compIndex
        (coprodIndex (deltaIndex Z) (normalizeIndex Q R q))
        (rightInjectionIndex Q)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨b, hq, hinr⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hqraw, hR⟩ :=
      (eventualGraph_normalizeIndex_eval Q R q x b).mp hq
    obtain ⟨-, hy⟩ := (eventualGraph_rightInjectionIndex_eval R b y).mp hinr
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 1,
      (eventualGraph_rightInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (eventualGraph_coprodIndex_eval _ _ _ y).mpr
      (Or.inr ⟨x, b, rfl, hy,
        (eventualGraph_normalizeIndex_eval Q R q x b).mpr
          ⟨hQ, hqraw, hR⟩⟩)
  · intro h
    obtain ⟨p, hinr, hp⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hp'⟩ :=
      (eventualGraph_rightInjectionIndex_eval Q x p).mp hinr
    rcases (eventualGraph_coprodIndex_eval _ _ p y).mp hp with
      ⟨a, b, hpa, -, -⟩ | ⟨a, b, hpa, hy, hq⟩
    · have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff x 1 a 0).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · have hxa : x = a :=
        (pair_eq_pair_iff x 1 a 1).mp (hp'.symm.trans hpa) |>.1
      obtain ⟨-, -, hR⟩ :=
        (eventualGraph_normalizeIndex_eval Q R q a b).mp hq
      apply (eventualGraph_comp_eval _ _ x y).mpr
      refine ⟨b, by simpa only [hxa] using hq, ?_⟩
      exact (eventualGraph_rightInjectionIndex_eval R b y).mpr ⟨hR, hy⟩

/-- Changing the unused right summand leaves the left injection unchanged. -/
theorem eqIndex_leftInjection_unused
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q : STObjectCode) (r : ℕ) :
    EqIndex T
      (compIndex (coprodIndex (deltaIndex Q) r) (leftInjectionIndex Q))
      (leftInjectionIndex Q) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hinl, hp⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hQ, hp'⟩ :=
      (eventualGraph_leftInjectionIndex_eval Q x p).mp hinl
    rcases (eventualGraph_coprodIndex_eval _ _ p y).mp hp with
      ⟨a, b, hpa, hy, hdelta⟩ | ⟨a, b, hpa, -, -⟩
    · have hxa : x = a :=
        (pair_eq_pair_iff x 0 a 0).mp (hp'.symm.trans hpa) |>.1
      obtain ⟨-, hba⟩ := (eventualGraph_deltaIndex_eval Q a b).mp hdelta
      exact (eventualGraph_leftInjectionIndex_eval Q x y).mpr
        ⟨hQ, hy.trans (congrArg (fun u => pair u (0 : M)) hba) |>.trans
          (congrArg (fun u => pair u (0 : M)) hxa.symm)⟩
    · have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff x 0 a 1).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (zero_ne_one h01)
  · intro h
    obtain ⟨hQ, hy⟩ := (eventualGraph_leftInjectionIndex_eval Q x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 0,
      (eventualGraph_leftInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩, ?_⟩
    exact (eventualGraph_coprodIndex_eval _ _ _ y).mpr
      (Or.inl ⟨x, x, rfl, hy,
        (eventualGraph_deltaIndex_eval Q x x).mpr ⟨hQ, rfl⟩⟩)

/-- Changing the unused left summand leaves the right injection unchanged. -/
theorem eqIndex_rightInjection_unused
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (R : STObjectCode) (q : ℕ) :
    EqIndex T
      (compIndex (coprodIndex q (deltaIndex R)) (rightInjectionIndex R))
      (rightInjectionIndex R) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  constructor
  · intro h
    obtain ⟨p, hinr, hp⟩ := (eventualGraph_comp_eval _ _ x y).mp h
    obtain ⟨hR, hp'⟩ :=
      (eventualGraph_rightInjectionIndex_eval R x p).mp hinr
    rcases (eventualGraph_coprodIndex_eval _ _ p y).mp hp with
      ⟨a, b, hpa, -, -⟩ | ⟨a, b, hpa, hy, hdelta⟩
    · have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff x 1 a 0).mp (hp'.symm.trans hpa) |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · have hxa : x = a :=
        (pair_eq_pair_iff x 1 a 1).mp (hp'.symm.trans hpa) |>.1
      obtain ⟨-, hba⟩ := (eventualGraph_deltaIndex_eval R a b).mp hdelta
      exact (eventualGraph_rightInjectionIndex_eval R x y).mpr
        ⟨hR, hy.trans (congrArg (fun u => pair u (1 : M)) hba) |>.trans
          (congrArg (fun u => pair u (1 : M)) hxa.symm)⟩
  · intro h
    obtain ⟨hR, hy⟩ := (eventualGraph_rightInjectionIndex_eval R x y).mp h
    apply (eventualGraph_comp_eval _ _ x y).mpr
    refine ⟨pair x 1,
      (eventualGraph_rightInjectionIndex_eval R x _).mpr ⟨hR, rfl⟩, ?_⟩
    exact (eventualGraph_coprodIndex_eval _ _ _ y).mpr
      (Or.inr ⟨x, x, rfl, hy,
        (eventualGraph_deltaIndex_eval R x x).mpr ⟨hR, rfl⟩⟩)

/-! ## The `HasCoproducts` laws -/

theorem typed_coprod_id
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y : CodedProgramCategory T) :
    typedCoprodMap T (𝟙 X) (𝟙 Y) = 𝟙 (coprod X Y) := by
  apply CodedHom.ext
  change coprodClass T (objectIdempotent T (objectCode X))
      (objectIdempotent T (objectCode Y)) =
    objectIdempotent T (.coproduct (objectCode X) (objectCode Y))
  exact (objectIdempotent_coproduct T _ _).symm

theorem typed_coprod_comp
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {A B C D E F : CodedProgramCategory T}
    (f : A ⟶ B) (g : B ⟶ C) (h : D ⟶ E) (k : E ⟶ F) :
    typedCoprodMap T f h ≫ typedCoprodMap T g k =
      typedCoprodMap T (f ≫ g) (h ≫ k) := by
  apply CodedHom.ext
  change coprodClass T g.1 k.1 * coprodClass T f.1 h.1 =
    coprodClass T (g.1 * f.1) (k.1 * h.1)
  exact (coprodClass_mul T g.1 f.1 k.1 h.1).symm

theorem typed_i0_codiag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X : CodedProgramCategory T) :
    typedI0 T X X ≫ typedCodiag T X = 𝟙 X := by
  apply CodedHom.ext
  rw [comp_val, typedI0_val, typedCodiag_val, id_val]
  change classOf T
      (compIndex (codiagonalIndex (objectCode X))
        (leftInjectionIndex (objectCode X))) =
    classOf T (deltaIndex (objectCode X))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_left_codiagonal T (objectCode X))

theorem typed_i1_codiag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X : CodedProgramCategory T) :
    typedI1 T X X ≫ typedCodiag T X = 𝟙 X := by
  apply CodedHom.ext
  rw [comp_val, typedI1_val, typedCodiag_val, id_val]
  change classOf T
      (compIndex (codiagonalIndex (objectCode X))
        (rightInjectionIndex (objectCode X))) =
    classOf T (deltaIndex (objectCode X))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_right_codiagonal T (objectCode X))

theorem typed_i0_i1_codiag
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (X Y : CodedProgramCategory T) :
    typedCoprodMap T (typedI0 T X Y) (typedI1 T X Y) ≫
        typedCodiag T (coprod X Y) =
      𝟙 (coprod X Y) := by
  apply CodedHom.ext
  rw [comp_val, typedCoprodMap_val, typedI0_val, typedI1_val,
    typedCodiag_val, id_val]
  change classOf T
      (compIndex (codiagonalIndex (.coproduct (objectCode X) (objectCode Y)))
        (coprodIndex (leftInjectionIndex (objectCode X))
          (rightInjectionIndex (objectCode Y)))) =
    classOf T (deltaIndex (.coproduct (objectCode X) (objectCode Y)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_coprod_injections_codiagonal T (objectCode X) (objectCode Y))

theorem typed_codiag_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y : CodedProgramCategory T} (f : X ⟶ Y) :
    typedCoprodMap T f f ≫ typedCodiag T Y = typedCodiag T X ≫ f := by
  obtain ⟨q, hq⟩ :=
    exists_arrowOfIndex T (objectCode X) (objectCode Y) f
  have hqv : classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
      f.1 := by
    rw [← arrowOfIndex_val T (objectCode X) (objectCode Y) q]
    exact congrArg Subtype.val hq
  apply CodedHom.ext
  rw [comp_val, comp_val, typedCoprodMap_val T f f,
    typedCodiag_val T Y, typedCodiag_val T X, codiagonalClass,
    ← hqv, coprodClass_classOf]
  change classOf T
      (compIndex (codiagonalIndex (objectCode Y))
        (coprodIndex
          (normalizeIndex (objectCode X) (objectCode Y) q)
          (normalizeIndex (objectCode X) (objectCode Y) q))) =
    classOf T
      (compIndex (normalizeIndex (objectCode X) (objectCode Y) q)
        (codiagonalIndex (objectCode X)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_codiagonal_natural T (objectCode X) (objectCode Y) q)

theorem typed_i0_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (f : X ⟶ Y) :
    f ≫ typedI0 T Y Z =
      typedI0 T X Z ≫ typedCoprodMap T f (𝟙 Z) := by
  obtain ⟨q, hq⟩ :=
    exists_arrowOfIndex T (objectCode X) (objectCode Y) f
  have hqv : classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
      f.1 := by
    rw [← arrowOfIndex_val T (objectCode X) (objectCode Y) q]
    exact congrArg Subtype.val hq
  apply CodedHom.ext
  rw [comp_val, comp_val, typedI0_val T Y Z, typedI0_val T X Z,
    typedCoprodMap_val T f (𝟙 Z), id_val, leftInjectionClass,
    ← hqv]
  change classOf T (leftInjectionIndex (objectCode Y)) *
      classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
    coprodClass T
        (classOf T (normalizeIndex (objectCode X) (objectCode Y) q))
        (classOf T (deltaIndex (objectCode Z))) *
      classOf T (leftInjectionIndex (objectCode X))
  rw [coprodClass_classOf]
  change classOf T
      (compIndex (leftInjectionIndex (objectCode Y))
        (normalizeIndex (objectCode X) (objectCode Y) q)) =
    classOf T
      (compIndex
        (coprodIndex (normalizeIndex (objectCode X) (objectCode Y) q)
          (deltaIndex (objectCode Z)))
        (leftInjectionIndex (objectCode X)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_leftInjection_natural T
      (objectCode X) (objectCode Y) (objectCode Z) q)

theorem typed_i0_nat_right
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (g : Y ⟶ Z) :
    typedI0 T X Y ≫ typedCoprodMap T (𝟙 X) g = typedI0 T X Z := by
  obtain ⟨r, hr⟩ :=
    exists_arrowOfIndex T (objectCode Y) (objectCode Z) g
  have hrv : classOf T (normalizeIndex (objectCode Y) (objectCode Z) r) =
      g.1 := by
    rw [← arrowOfIndex_val T (objectCode Y) (objectCode Z) r]
    exact congrArg Subtype.val hr
  apply CodedHom.ext
  rw [comp_val, typedCoprodMap_val T (𝟙 X) g,
    typedI0_val T X Y, typedI0_val T X Z, id_val,
    leftInjectionClass, objectIdempotent, ← hrv,
    coprodClass_classOf]
  change classOf T
      (compIndex
        (coprodIndex (deltaIndex (objectCode X))
          (normalizeIndex (objectCode Y) (objectCode Z) r))
        (leftInjectionIndex (objectCode X))) =
    classOf T (leftInjectionIndex (objectCode X))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_leftInjection_unused T (objectCode X)
      (normalizeIndex (objectCode Y) (objectCode Z) r))

theorem typed_i1_nat
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (f : X ⟶ Y) :
    f ≫ typedI1 T Z Y =
      typedI1 T Z X ≫ typedCoprodMap T (𝟙 Z) f := by
  obtain ⟨q, hq⟩ :=
    exists_arrowOfIndex T (objectCode X) (objectCode Y) f
  have hqv : classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
      f.1 := by
    rw [← arrowOfIndex_val T (objectCode X) (objectCode Y) q]
    exact congrArg Subtype.val hq
  apply CodedHom.ext
  rw [comp_val, comp_val, typedI1_val T Z Y, typedI1_val T Z X,
    typedCoprodMap_val T (𝟙 Z) f, id_val, rightInjectionClass,
    ← hqv]
  change classOf T (rightInjectionIndex (objectCode Y)) *
      classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
    coprodClass T (classOf T (deltaIndex (objectCode Z)))
        (classOf T (normalizeIndex (objectCode X) (objectCode Y) q)) *
      classOf T (rightInjectionIndex (objectCode X))
  rw [coprodClass_classOf]
  change classOf T
      (compIndex (rightInjectionIndex (objectCode Y))
        (normalizeIndex (objectCode X) (objectCode Y) q)) =
    classOf T
      (compIndex
        (coprodIndex (deltaIndex (objectCode Z))
          (normalizeIndex (objectCode X) (objectCode Y) q))
        (rightInjectionIndex (objectCode X)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_rightInjection_natural T
      (objectCode X) (objectCode Y) (objectCode Z) q)

theorem typed_i1_nat_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {X Y Z : CodedProgramCategory T} (f : X ⟶ Y) :
    typedI1 T X Z ≫ typedCoprodMap T f (𝟙 Z) = typedI1 T Y Z := by
  obtain ⟨q, hq⟩ :=
    exists_arrowOfIndex T (objectCode X) (objectCode Y) f
  have hqv : classOf T (normalizeIndex (objectCode X) (objectCode Y) q) =
      f.1 := by
    rw [← arrowOfIndex_val T (objectCode X) (objectCode Y) q]
    exact congrArg Subtype.val hq
  apply CodedHom.ext
  rw [comp_val, typedCoprodMap_val T f (𝟙 Z),
    typedI1_val T X Z, typedI1_val T Y Z, id_val,
    rightInjectionClass, ← hqv]
  change coprodClass T
        (classOf T (normalizeIndex (objectCode X) (objectCode Y) q))
        (classOf T (deltaIndex (objectCode Z))) *
      classOf T (rightInjectionIndex (objectCode Z)) =
    classOf T (rightInjectionIndex (objectCode Z))
  rw [coprodClass_classOf]
  change classOf T
      (compIndex
        (coprodIndex (normalizeIndex (objectCode X) (objectCode Y) q)
          (deltaIndex (objectCode Z)))
        (rightInjectionIndex (objectCode Z))) =
    classOf T (rightInjectionIndex (objectCode Z))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_rightInjection_unused T (objectCode Z)
      (normalizeIndex (objectCode X) (objectCode Y) q))

/-- The typed program category has binary coproducts. -/
instance codedProgramCategoryHasCoproducts
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    HasCoproducts (CodedProgramCategory T) where
  coprod_id := typed_coprod_id T
  coprod_comp := typed_coprod_comp T
  i0_codiag := typed_i0_codiag T
  i1_codiag := typed_i1_codiag T
  i0_i1_codiag := typed_i0_i1_codiag T
  codiag_nat := typed_codiag_nat T
  i0_nat := typed_i0_nat T
  i0_nat_right := typed_i0_nat_right T
  i1_nat := typed_i1_nat T
  i1_nat_left := typed_i1_nat_left T

/-! ## Copairing and total injections -/

/-- The left injection selects the left branch of typed copairing. -/
@[simp] theorem typed_i0_copair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R V : CodedProgramCategory T}
    (f : Q ⟶ V) (g : R ⟶ V) :
    i0 Q R ≫ copair f g = f :=
  HasCoproducts.i0_copair f g

/-- The right injection selects the right branch of typed copairing. -/
@[simp] theorem typed_i1_copair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R V : CodedProgramCategory T}
    (f : Q ⟶ V) (g : R ⟶ V) :
    i1 Q R ≫ copair f g = g :=
  HasCoproducts.i1_copair f g

/-- The binary-coproduct universal property, with no totality premise
on either branch. -/
theorem typed_existsUnique_copair
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {Q R V : CodedProgramCategory T}
    (f : Q ⟶ V) (g : R ⟶ V) :
    ∃! h : coprod Q R ⟶ V,
      i0 Q R ≫ h = f ∧ i1 Q R ≫ h = g :=
  HasCoproducts.existsUnique_copair f g

theorem pa_proves_leftInjection_totality (Q R : STObjectCode) :
    𝗣𝗔 ⊢ typedTotalitySentence Q (.coproduct Q R)
      (leftInjectionIndex Q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, typedTotalitySentence_eval]
  intro x hQ
  refine ⟨pair x 0, ?_⟩
  apply (eventualGraph_normalizeIndex_eval Q (.coproduct Q R)
    (leftInjectionIndex Q) x (pair x 0)).mpr
  exact ⟨hQ,
    (eventualGraph_leftInjectionIndex_eval Q x _).mpr ⟨hQ, rfl⟩,
    (memberFormula_coproduct_left_pair_eval Q R x).mpr hQ⟩

theorem pa_proves_rightInjection_totality (Q R : STObjectCode) :
    𝗣𝗔 ⊢ typedTotalitySentence R (.coproduct Q R)
      (rightInjectionIndex R) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, typedTotalitySentence_eval]
  intro x hR
  refine ⟨pair x 1, ?_⟩
  apply (eventualGraph_normalizeIndex_eval R (.coproduct Q R)
    (rightInjectionIndex R) x (pair x 1)).mpr
  exact ⟨hR,
    (eventualGraph_rightInjectionIndex_eval R x _).mpr ⟨hR, rfl⟩,
    (memberFormula_coproduct_right_pair_eval Q R x).mpr hR⟩

/-- Every typed left injection is restriction-total. -/
theorem typed_i0_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) :
    RestrictionCategory.isTotal (i0 (object T Q) (object T R)) := by
  rw [i0_object]
  apply (arrowOfIndex_isTotal_iff_proves_typedTotality T Q
    (.coproduct Q R) (leftInjectionIndex Q)).mpr
  exact WeakerThan.pbl (pa_proves_leftInjection_totality Q R)

/-- Every typed right injection is restriction-total. -/
theorem typed_i1_isTotal
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) :
    RestrictionCategory.isTotal (i1 (object T Q) (object T R)) := by
  rw [i1_object]
  apply (arrowOfIndex_isTotal_iff_proves_typedTotality T R
    (.coproduct Q R) (rightInjectionIndex R)).mpr
  exact WeakerThan.pbl (pa_proves_rightInjection_totality Q R)

/-! ## Distributivity rearrangement graphs -/

/-- Graph of the left comparison rearrangement
`((w,u), tag) ↦ (w,(u,tag))`. -/
def distribLeftGraph (W U V : STObjectCode) : Graph :=
  .mkSigma “x y.
    (∃ w, ∃ u, ∃ wu, ∃ ut,
      !natPairFormula.val wu w u ∧ !natPairFormula.val x wu 0 ∧
      !natPairFormula.val ut u 0 ∧ !natPairFormula.val y w ut ∧
      !(memberFormula W).val w ∧ !(memberFormula U).val u) ∨
    (∃ w, ∃ v, ∃ wv, ∃ vt,
      !natPairFormula.val wv w v ∧ !natPairFormula.val x wv 1 ∧
      !natPairFormula.val vt v 1 ∧ !natPairFormula.val y w vt ∧
      !(memberFormula W).val w ∧ !(memberFormula V).val v)”

/-- Graph of the inverse left comparison rearrangement
`(w,(u,tag)) ↦ ((w,u),tag)`. -/
def distribLeftInvGraph (W U V : STObjectCode) : Graph :=
  .mkSigma “x y.
    (∃ w, ∃ u, ∃ wu, ∃ ut,
      !natPairFormula.val ut u 0 ∧ !natPairFormula.val x w ut ∧
      !natPairFormula.val wu w u ∧ !natPairFormula.val y wu 0 ∧
      !(memberFormula W).val w ∧ !(memberFormula U).val u) ∨
    (∃ w, ∃ v, ∃ wv, ∃ vt,
      !natPairFormula.val vt v 1 ∧ !natPairFormula.val x w vt ∧
      !natPairFormula.val wv w v ∧ !natPairFormula.val y wv 1 ∧
      !(memberFormula W).val w ∧ !(memberFormula V).val v)”

/-- Graph of the right comparison rearrangement
`((u,w), tag) ↦ ((u,tag),w)`. -/
def distribRightGraph (U V W : STObjectCode) : Graph :=
  .mkSigma “x y.
    (∃ u, ∃ w, ∃ uw, ∃ ut,
      !natPairFormula.val uw u w ∧ !natPairFormula.val x uw 0 ∧
      !natPairFormula.val ut u 0 ∧ !natPairFormula.val y ut w ∧
      !(memberFormula U).val u ∧ !(memberFormula W).val w) ∨
    (∃ v, ∃ w, ∃ vw, ∃ vt,
      !natPairFormula.val vw v w ∧ !natPairFormula.val x vw 1 ∧
      !natPairFormula.val vt v 1 ∧ !natPairFormula.val y vt w ∧
      !(memberFormula V).val v ∧ !(memberFormula W).val w)”

/-- Graph of the inverse right comparison rearrangement
`((u,tag),w) ↦ ((u,w),tag)`. -/
def distribRightInvGraph (U V W : STObjectCode) : Graph :=
  .mkSigma “x y.
    (∃ u, ∃ w, ∃ uw, ∃ ut,
      !natPairFormula.val ut u 0 ∧ !natPairFormula.val x ut w ∧
      !natPairFormula.val uw u w ∧ !natPairFormula.val y uw 0 ∧
      !(memberFormula U).val u ∧ !(memberFormula W).val w) ∨
    (∃ v, ∃ w, ∃ vw, ∃ vt,
      !natPairFormula.val vt v 1 ∧ !natPairFormula.val x vt w ∧
      !natPairFormula.val vw v w ∧ !natPairFormula.val y vw 1 ∧
      !(memberFormula V).val v ∧ !(memberFormula W).val w)”

@[simp] theorem distribLeftGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (W U V : STObjectCode) (x y : M) :
    (distribLeftGraph W U V).val.Evalb ![x, y] ↔
      (∃ w u : M, x = pair (pair w u) 0 ∧
        y = pair w (pair u 0) ∧
        (memberFormula W).val.Evalb ![w] ∧
        (memberFormula U).val.Evalb ![u]) ∨
      (∃ w v : M, x = pair (pair w v) 1 ∧
        y = pair w (pair v 1) ∧
        (memberFormula W).val.Evalb ![w] ∧
        (memberFormula V).val.Evalb ![v]) := by
  simp [distribLeftGraph]

@[simp] theorem distribLeftInvGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (W U V : STObjectCode) (x y : M) :
    (distribLeftInvGraph W U V).val.Evalb ![x, y] ↔
      (∃ w u : M, x = pair w (pair u 0) ∧
        y = pair (pair w u) 0 ∧
        (memberFormula W).val.Evalb ![w] ∧
        (memberFormula U).val.Evalb ![u]) ∨
      (∃ w v : M, x = pair w (pair v 1) ∧
        y = pair (pair w v) 1 ∧
        (memberFormula W).val.Evalb ![w] ∧
        (memberFormula V).val.Evalb ![v]) := by
  simp [distribLeftInvGraph]

@[simp] theorem distribRightGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (U V W : STObjectCode) (x y : M) :
    (distribRightGraph U V W).val.Evalb ![x, y] ↔
      (∃ u w : M, x = pair (pair u w) 0 ∧
        y = pair (pair u 0) w ∧
        (memberFormula U).val.Evalb ![u] ∧
        (memberFormula W).val.Evalb ![w]) ∨
      (∃ v w : M, x = pair (pair v w) 1 ∧
        y = pair (pair v 1) w ∧
        (memberFormula V).val.Evalb ![v] ∧
        (memberFormula W).val.Evalb ![w]) := by
  simp [distribRightGraph]

@[simp] theorem distribRightInvGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (U V W : STObjectCode) (x y : M) :
    (distribRightInvGraph U V W).val.Evalb ![x, y] ↔
      (∃ u w : M, x = pair (pair u 0) w ∧
        y = pair (pair u w) 0 ∧
        (memberFormula U).val.Evalb ![u] ∧
        (memberFormula W).val.Evalb ![w]) ∨
      (∃ v w : M, x = pair (pair v 1) w ∧
        y = pair (pair v w) 1 ∧
        (memberFormula V).val.Evalb ![v] ∧
        (memberFormula W).val.Evalb ![w]) := by
  simp [distribRightInvGraph]

theorem distribLeftInvGraph_functional (W U V : STObjectCode) :
    Functional (distribLeftInvGraph W U V) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rcases (distribLeftInvGraph_eval W U V x y).mp hy with
      ⟨w, u, hx, hy, hW, hU⟩ | ⟨w, v, hx, hy, hW, hV⟩ <;>
    rcases (distribLeftInvGraph_eval W U V x z).mp hz with
      ⟨w', u', hx', hz, hW', hU'⟩ | ⟨w', v', hx', hz, hW', hV'⟩
  · obtain ⟨hww, hut⟩ :=
      (pair_eq_pair_iff w (pair u 0) w' (pair u' 0)).mp
        (hx.symm.trans hx')
    have huu : u = u' := (pair_eq_pair_iff u 0 u' 0).mp hut |>.1
    subst w'
    subst u'
    exact hy.trans hz.symm
  · obtain ⟨-, hut⟩ :=
      (pair_eq_pair_iff w (pair u 0) w' (pair v' 1)).mp
        (hx.symm.trans hx')
    have h01 : (0 : M) = 1 :=
      (pair_eq_pair_iff u 0 v' 1).mp hut |>.2
    exact False.elim (zero_ne_one h01)
  · obtain ⟨-, hvt⟩ :=
      (pair_eq_pair_iff w (pair v 1) w' (pair u' 0)).mp
        (hx.symm.trans hx')
    have h10 : (1 : M) = 0 :=
      (pair_eq_pair_iff v 1 u' 0).mp hvt |>.2
    exact False.elim (Arithmetic.one_ne_zero h10)
  · obtain ⟨hww, hvt⟩ :=
      (pair_eq_pair_iff w (pair v 1) w' (pair v' 1)).mp
        (hx.symm.trans hx')
    have hvv : v = v' := (pair_eq_pair_iff v 1 v' 1).mp hvt |>.1
    subst w'
    subst v'
    exact hy.trans hz.symm

theorem distribRightInvGraph_functional (U V W : STObjectCode) :
    Functional (distribRightInvGraph U V W) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro x y z hy hz
  rcases (distribRightInvGraph_eval U V W x y).mp hy with
      ⟨u, w, hx, hy, hU, hW⟩ | ⟨v, w, hx, hy, hV, hW⟩ <;>
    rcases (distribRightInvGraph_eval U V W x z).mp hz with
      ⟨u', w', hx', hz, hU', hW'⟩ | ⟨v', w', hx', hz, hV', hW'⟩
  · obtain ⟨hut, hww⟩ :=
      (pair_eq_pair_iff (pair u 0) w (pair u' 0) w').mp
        (hx.symm.trans hx')
    have huu : u = u' := (pair_eq_pair_iff u 0 u' 0).mp hut |>.1
    subst u'
    subst w'
    exact hy.trans hz.symm
  · obtain ⟨hut, -⟩ :=
      (pair_eq_pair_iff (pair u 0) w (pair v' 1) w').mp
        (hx.symm.trans hx')
    have h01 : (0 : M) = 1 :=
      (pair_eq_pair_iff u 0 v' 1).mp hut |>.2
    exact False.elim (zero_ne_one h01)
  · obtain ⟨hvt, -⟩ :=
      (pair_eq_pair_iff (pair v 1) w (pair u' 0) w').mp
        (hx.symm.trans hx')
    have h10 : (1 : M) = 0 :=
      (pair_eq_pair_iff v 1 u' 0).mp hvt |>.2
    exact False.elim (Arithmetic.one_ne_zero h10)
  · obtain ⟨hvt, hww⟩ :=
      (pair_eq_pair_iff (pair v 1) w (pair v' 1) w').mp
        (hx.symm.trans hx')
    have hvv : v = v' := (pair_eq_pair_iff v 1 v' 1).mp hvt |>.1
    subst v'
    subst w'
    exact hy.trans hz.symm

/-- A selected program for the inverse left distributivity comparison. -/
def distribLeftInvIndex (W U V : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (distribLeftInvGraph W U V)
    (distribLeftInvGraph_functional W U V))

/-- A selected program for the inverse right distributivity comparison. -/
def distribRightInvIndex (U V W : STObjectCode) : ℕ :=
  Classical.choose (realize_graph (distribRightInvGraph U V W)
    (distribRightInvGraph_functional U V W))

theorem distribLeftInvIndex_uniform (W U V : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (distribLeftInvIndex W U V))
      (distribLeftInvGraph W U V) :=
  Classical.choose_spec (realize_graph (distribLeftInvGraph W U V)
    (distribLeftInvGraph_functional W U V))

theorem distribRightInvIndex_uniform (U V W : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (distribRightInvIndex U V W))
      (distribRightInvGraph U V W) :=
  Classical.choose_spec (realize_graph (distribRightInvGraph U V W)
    (distribRightInvGraph_functional U V W))

@[simp] theorem eventualGraph_distribLeftInvIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (W U V : STObjectCode) (x y : M) :
    (eventualGraph (distribLeftInvIndex W U V)).val.Evalb ![x, y] ↔
      (distribLeftInvGraph W U V).val.Evalb ![x, y] := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (distribLeftInvIndex_uniform W U V)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact h x y

@[simp] theorem eventualGraph_distribRightInvIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (U V W : STObjectCode) (x y : M) :
    (eventualGraph (distribRightInvIndex U V W)).val.Evalb ![x, y] ↔
      (distribRightInvGraph U V W).val.Evalb ![x, y] := by
  have h := consequence_iff.mp
    (Theory.Proof.sound (distribRightInvIndex_uniform U V W)) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact h x y

/-! ### The actual generic comparison programs -/

/-- The raw program underlying the generic left distributivity comparison. -/
def distribLeftIndex (W U V : STObjectCode) : ℕ :=
  compIndex (codiagonalIndex (.product W (.coproduct U V)))
    (coprodIndex
      (tensorIndex (deltaIndex W) (leftInjectionIndex U))
      (tensorIndex (deltaIndex W) (rightInjectionIndex V)))

/-- The raw program underlying the generic right distributivity comparison. -/
def distribRightIndex (U V W : STObjectCode) : ℕ :=
  compIndex (codiagonalIndex (.product (.coproduct U V) W))
    (coprodIndex
      (tensorIndex (leftInjectionIndex U) (deltaIndex W))
      (tensorIndex (rightInjectionIndex V) (deltaIndex W)))

@[simp] theorem eventualGraph_distribLeftIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (W U V : STObjectCode) (x y : M) :
    (eventualGraph (distribLeftIndex W U V)).val.Evalb ![x, y] ↔
      (distribLeftGraph W U V).val.Evalb ![x, y] := by
  rw [distribLeftGraph_eval, distribLeftIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rcases (eventualGraph_coprodIndex_eval _ _ x p).mp hp with
        ⟨a, b, hxa, hpb, hab⟩ | ⟨a, b, hxa, hpb, hab⟩
    · obtain ⟨w, ut, hw, hut, hb⟩ :=
        (eventualGraph_tensorIndex_eval _ _ a b).mp hab
      obtain ⟨hW, hw⟩ :=
        (eventualGraph_deltaIndex_eval W (pi₁ a) w).mp hw
      obtain ⟨hU, hut⟩ :=
        (eventualGraph_leftInjectionIndex_eval U (pi₂ a) ut).mp hut
      rcases (eventualGraph_codiagonalIndex_eval
          (.product W (.coproduct U V)) p y).mp hpy with
        ⟨c, hpc, hc, hyc⟩ | ⟨c, hpc, hc, hyc⟩
      · have hbc : b = c :=
          (pair_eq_pair_iff b 0 c 0).mp (hpb.symm.trans hpc) |>.1
        refine Or.inl ⟨pi₁ a, pi₂ a, ?_, ?_, hW, hU⟩
        · exact hxa.trans
            (congrArg (fun z => pair z (0 : M)) (pair_unpair a).symm)
        · exact hyc.trans hbc.symm |>.trans hb |>.trans
            (congrArg₂ pair hw hut)
      · have h01 : (0 : M) = 1 :=
          (pair_eq_pair_iff b 0 c 1).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (zero_ne_one h01)
    · obtain ⟨w, vt, hw, hvt, hb⟩ :=
        (eventualGraph_tensorIndex_eval _ _ a b).mp hab
      obtain ⟨hW, hw⟩ :=
        (eventualGraph_deltaIndex_eval W (pi₁ a) w).mp hw
      obtain ⟨hV, hvt⟩ :=
        (eventualGraph_rightInjectionIndex_eval V (pi₂ a) vt).mp hvt
      rcases (eventualGraph_codiagonalIndex_eval
          (.product W (.coproduct U V)) p y).mp hpy with
        ⟨c, hpc, hc, hyc⟩ | ⟨c, hpc, hc, hyc⟩
      · have h10 : (1 : M) = 0 :=
          (pair_eq_pair_iff b 1 c 0).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (Arithmetic.one_ne_zero h10)
      · have hbc : b = c :=
          (pair_eq_pair_iff b 1 c 1).mp (hpb.symm.trans hpc) |>.1
        refine Or.inr ⟨pi₁ a, pi₂ a, ?_, ?_, hW, hV⟩
        · exact hxa.trans
            (congrArg (fun z => pair z (1 : M)) (pair_unpair a).symm)
        · exact hyc.trans hbc.symm |>.trans hb |>.trans
            (congrArg₂ pair hw hvt)
  · rintro (⟨w, u, hx, hy, hW, hU⟩ | ⟨w, v, hx, hy, hW, hV⟩)
    · let b : M := pair w (pair u 0)
      let p : M := pair b 0
      refine ⟨p, ?_, ?_⟩
      · apply (eventualGraph_coprodIndex_eval _ _ x p).mpr
        exact Or.inl ⟨pair w u, b, hx, rfl,
          (eventualGraph_tensorIndex_pair_eval _ _ w u w (pair u 0)).mpr
            ⟨(eventualGraph_deltaIndex_eval W w w).mpr ⟨hW, rfl⟩,
              (eventualGraph_leftInjectionIndex_eval U u _).mpr
                ⟨hU, rfl⟩⟩⟩
      · apply (eventualGraph_codiagonalIndex_eval
          (.product W (.coproduct U V)) p y).mpr
        exact Or.inl ⟨b, rfl,
          (memberFormula_product_pair_eval W (.coproduct U V) w
            (pair u 0)).mpr ⟨hW,
              (memberFormula_coproduct_left_pair_eval U V u).mpr hU⟩,
          hy⟩
    · let b : M := pair w (pair v 1)
      let p : M := pair b 1
      refine ⟨p, ?_, ?_⟩
      · apply (eventualGraph_coprodIndex_eval _ _ x p).mpr
        exact Or.inr ⟨pair w v, b, hx, rfl,
          (eventualGraph_tensorIndex_pair_eval _ _ w v w (pair v 1)).mpr
            ⟨(eventualGraph_deltaIndex_eval W w w).mpr ⟨hW, rfl⟩,
              (eventualGraph_rightInjectionIndex_eval V v _).mpr
                ⟨hV, rfl⟩⟩⟩
      · apply (eventualGraph_codiagonalIndex_eval
          (.product W (.coproduct U V)) p y).mpr
        exact Or.inr ⟨b, rfl,
          (memberFormula_product_pair_eval W (.coproduct U V) w
            (pair v 1)).mpr ⟨hW,
              (memberFormula_coproduct_right_pair_eval U V v).mpr hV⟩,
          hy⟩

@[simp] theorem eventualGraph_distribRightIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (U V W : STObjectCode) (x y : M) :
    (eventualGraph (distribRightIndex U V W)).val.Evalb ![x, y] ↔
      (distribRightGraph U V W).val.Evalb ![x, y] := by
  rw [distribRightGraph_eval, distribRightIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rcases (eventualGraph_coprodIndex_eval _ _ x p).mp hp with
        ⟨a, b, hxa, hpb, hab⟩ | ⟨a, b, hxa, hpb, hab⟩
    · obtain ⟨ut, w, hut, hw, hb⟩ :=
        (eventualGraph_tensorIndex_eval _ _ a b).mp hab
      obtain ⟨hU, hut⟩ :=
        (eventualGraph_leftInjectionIndex_eval U (pi₁ a) ut).mp hut
      obtain ⟨hW, hw⟩ :=
        (eventualGraph_deltaIndex_eval W (pi₂ a) w).mp hw
      rcases (eventualGraph_codiagonalIndex_eval
          (.product (.coproduct U V) W) p y).mp hpy with
        ⟨c, hpc, hc, hyc⟩ | ⟨c, hpc, hc, hyc⟩
      · have hbc : b = c :=
          (pair_eq_pair_iff b 0 c 0).mp (hpb.symm.trans hpc) |>.1
        refine Or.inl ⟨pi₁ a, pi₂ a, ?_, ?_, hU, hW⟩
        · exact hxa.trans
            (congrArg (fun z => pair z (0 : M)) (pair_unpair a).symm)
        · exact hyc.trans hbc.symm |>.trans hb |>.trans
            (congrArg₂ pair hut hw)
      · have h01 : (0 : M) = 1 :=
          (pair_eq_pair_iff b 0 c 1).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (zero_ne_one h01)
    · obtain ⟨vt, w, hvt, hw, hb⟩ :=
        (eventualGraph_tensorIndex_eval _ _ a b).mp hab
      obtain ⟨hV, hvt⟩ :=
        (eventualGraph_rightInjectionIndex_eval V (pi₁ a) vt).mp hvt
      obtain ⟨hW, hw⟩ :=
        (eventualGraph_deltaIndex_eval W (pi₂ a) w).mp hw
      rcases (eventualGraph_codiagonalIndex_eval
          (.product (.coproduct U V) W) p y).mp hpy with
        ⟨c, hpc, hc, hyc⟩ | ⟨c, hpc, hc, hyc⟩
      · have h10 : (1 : M) = 0 :=
          (pair_eq_pair_iff b 1 c 0).mp (hpb.symm.trans hpc) |>.2
        exact False.elim (Arithmetic.one_ne_zero h10)
      · have hbc : b = c :=
          (pair_eq_pair_iff b 1 c 1).mp (hpb.symm.trans hpc) |>.1
        refine Or.inr ⟨pi₁ a, pi₂ a, ?_, ?_, hV, hW⟩
        · exact hxa.trans
            (congrArg (fun z => pair z (1 : M)) (pair_unpair a).symm)
        · exact hyc.trans hbc.symm |>.trans hb |>.trans
            (congrArg₂ pair hvt hw)
  · rintro (⟨u, w, hx, hy, hU, hW⟩ | ⟨v, w, hx, hy, hV, hW⟩)
    · let b : M := pair (pair u 0) w
      let p : M := pair b 0
      refine ⟨p, ?_, ?_⟩
      · apply (eventualGraph_coprodIndex_eval _ _ x p).mpr
        exact Or.inl ⟨pair u w, b, hx, rfl,
          (eventualGraph_tensorIndex_pair_eval _ _ u w (pair u 0) w).mpr
            ⟨(eventualGraph_leftInjectionIndex_eval U u _).mpr
                ⟨hU, rfl⟩,
              (eventualGraph_deltaIndex_eval W w w).mpr ⟨hW, rfl⟩⟩⟩
      · apply (eventualGraph_codiagonalIndex_eval
          (.product (.coproduct U V) W) p y).mpr
        exact Or.inl ⟨b, rfl,
          (memberFormula_product_pair_eval (.coproduct U V) W
            (pair u 0) w).mpr
              ⟨(memberFormula_coproduct_left_pair_eval U V u).mpr hU, hW⟩,
          hy⟩
    · let b : M := pair (pair v 1) w
      let p : M := pair b 1
      refine ⟨p, ?_, ?_⟩
      · apply (eventualGraph_coprodIndex_eval _ _ x p).mpr
        exact Or.inr ⟨pair v w, b, hx, rfl,
          (eventualGraph_tensorIndex_pair_eval _ _ v w (pair v 1) w).mpr
            ⟨(eventualGraph_rightInjectionIndex_eval V v _).mpr
                ⟨hV, rfl⟩,
              (eventualGraph_deltaIndex_eval W w w).mpr ⟨hW, rfl⟩⟩⟩
      · apply (eventualGraph_codiagonalIndex_eval
          (.product (.coproduct U V) W) p y).mpr
        exact Or.inr ⟨b, rfl,
          (memberFormula_product_pair_eval (.coproduct U V) W
            (pair v 1) w).mpr
              ⟨(memberFormula_coproduct_right_pair_eval U V v).mpr hV, hW⟩,
          hy⟩

/-- PA proves the exact graph of the generic left comparison program. -/
theorem distribLeftIndex_uniform (W U V : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (distribLeftIndex W U V))
      (distribLeftGraph W U V) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  exact eventualGraph_distribLeftIndex_eval W U V

/-- PA proves the exact graph of the generic right comparison program. -/
theorem distribRightIndex_uniform (U V W : STObjectCode) :
    Uniform 𝗣𝗔 (eventualGraph (distribRightIndex U V W))
      (distribRightGraph U V W) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  exact eventualGraph_distribRightIndex_eval U V W

/-! ### Supported inverse arrows -/

theorem pa_proves_distribLeftInv_support (W U V : STObjectCode) :
    𝗣𝗔 ⊢ supportSentence (.product W (.coproduct U V))
      (.coproduct (.product W U) (.product W V))
      (distribLeftInvIndex W U V) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro x y hxy
  rw [eventualGraph_distribLeftInvIndex_eval,
    distribLeftInvGraph_eval] at hxy
  rcases hxy with ⟨w, u, hx, hy, hW, hU⟩ | ⟨w, v, hx, hy, hW, hV⟩
  · constructor
    · rw [hx]
      exact (memberFormula_product_pair_eval W (.coproduct U V) w
        (pair u 0)).mpr ⟨hW,
          (memberFormula_coproduct_left_pair_eval U V u).mpr hU⟩
    · rw [hy]
      exact (memberFormula_coproduct_left_pair_eval
        (.product W U) (.product W V) (pair w u)).mpr
          ((memberFormula_product_pair_eval W U w u).mpr ⟨hW, hU⟩)
  · constructor
    · rw [hx]
      exact (memberFormula_product_pair_eval W (.coproduct U V) w
        (pair v 1)).mpr ⟨hW,
          (memberFormula_coproduct_right_pair_eval U V v).mpr hV⟩
    · rw [hy]
      exact (memberFormula_coproduct_right_pair_eval
        (.product W U) (.product W V) (pair w v)).mpr
          ((memberFormula_product_pair_eval W V w v).mpr ⟨hW, hV⟩)

theorem pa_proves_distribRightInv_support (U V W : STObjectCode) :
    𝗣𝗔 ⊢ supportSentence (.product (.coproduct U V) W)
      (.coproduct (.product U W) (.product V W))
      (distribRightInvIndex U V W) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro x y hxy
  rw [eventualGraph_distribRightInvIndex_eval,
    distribRightInvGraph_eval] at hxy
  rcases hxy with ⟨u, w, hx, hy, hU, hW⟩ | ⟨v, w, hx, hy, hV, hW⟩
  · constructor
    · rw [hx]
      exact (memberFormula_product_pair_eval (.coproduct U V) W
        (pair u 0) w).mpr
          ⟨(memberFormula_coproduct_left_pair_eval U V u).mpr hU, hW⟩
    · rw [hy]
      exact (memberFormula_coproduct_left_pair_eval
        (.product U W) (.product V W) (pair u w)).mpr
          ((memberFormula_product_pair_eval U W u w).mpr ⟨hU, hW⟩)
  · constructor
    · rw [hx]
      exact (memberFormula_product_pair_eval (.coproduct U V) W
        (pair v 1) w).mpr
          ⟨(memberFormula_coproduct_right_pair_eval U V v).mpr hV, hW⟩
    · rw [hy]
      exact (memberFormula_coproduct_right_pair_eval
        (.product U W) (.product V W) (pair v w)).mpr
          ((memberFormula_product_pair_eval V W v w).mpr ⟨hV, hW⟩)

theorem eqIndex_normalize_distribLeftInv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : STObjectCode) :
    EqIndex T
      (normalizeIndex (.product W (.coproduct U V))
        (.coproduct (.product W U) (.product W V))
        (distribLeftInvIndex W U V))
      (distribLeftInvIndex W U V) :=
  (proves_support_iff_eqIndex_normalize T
    (.product W (.coproduct U V))
    (.coproduct (.product W U) (.product W V))
    (distribLeftInvIndex W U V)).mp
      (WeakerThan.pbl (pa_proves_distribLeftInv_support W U V))

theorem eqIndex_normalize_distribRightInv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : STObjectCode) :
    EqIndex T
      (normalizeIndex (.product (.coproduct U V) W)
        (.coproduct (.product U W) (.product V W))
        (distribRightInvIndex U V W))
      (distribRightInvIndex U V W) :=
  (proves_support_iff_eqIndex_normalize T
    (.product (.coproduct U V) W)
    (.coproduct (.product U W) (.product V W))
    (distribRightInvIndex U V W)).mp
      (WeakerThan.pbl (pa_proves_distribRightInv_support U V W))

/-- Typed inverse to the generic left distributivity comparison. -/
def typedDistribLeftInv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    nearProd W (coprod U V) ⟶
      coprod (nearProd W U) (nearProd W V) :=
  arrowOfIndex T
    (.product (objectCode W) (.coproduct (objectCode U) (objectCode V)))
    (.coproduct (.product (objectCode W) (objectCode U))
      (.product (objectCode W) (objectCode V)))
    (distribLeftInvIndex (objectCode W) (objectCode U) (objectCode V))

/-- Typed inverse to the generic right distributivity comparison. -/
def typedDistribRightInv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    nearProd (coprod U V) W ⟶
      coprod (nearProd U W) (nearProd V W) :=
  arrowOfIndex T
    (.product (.coproduct (objectCode U) (objectCode V)) (objectCode W))
    (.coproduct (.product (objectCode U) (objectCode W))
      (.product (objectCode V) (objectCode W)))
    (distribRightInvIndex (objectCode U) (objectCode V) (objectCode W))

@[simp] theorem typedDistribLeftInv_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    (typedDistribLeftInv T W U V).1 =
      classOf T (distribLeftInvIndex
        (objectCode W) (objectCode U) (objectCode V)) := by
  rw [typedDistribLeftInv, arrowOfIndex_val, classOf_eq_classOf_iff]
  exact eqIndex_normalize_distribLeftInv T
    (objectCode W) (objectCode U) (objectCode V)

@[simp] theorem typedDistribRightInv_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    (typedDistribRightInv T U V W).1 =
      classOf T (distribRightInvIndex
        (objectCode U) (objectCode V) (objectCode W)) := by
  rw [typedDistribRightInv, arrowOfIndex_val, classOf_eq_classOf_iff]
  exact eqIndex_normalize_distribRightInv T
    (objectCode U) (objectCode V) (objectCode W)

/-! ### Representatives of the generic comparison arrows -/

@[simp] theorem distribLeft_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    (distribLeft W U V).1 =
      classOf T (distribLeftIndex
        (objectCode W) (objectCode U) (objectCode V)) := by
  change (typedCoprodMap T
      (typedNearProdMap T (𝟙 W) (typedI0 T U V))
      (typedNearProdMap T (𝟙 W) (typedI1 T U V)) ≫
    typedCodiag T (nearProd W (coprod U V))).1 = _
  rw [comp_val,
    typedCodiag_val T (nearProd W (coprod U V)),
    typedCoprodMap_val T
      (typedNearProdMap T (𝟙 W) (typedI0 T U V))
      (typedNearProdMap T (𝟙 W) (typedI1 T U V)),
    typedNearProdMap_val T (𝟙 W) (typedI0 T U V),
    typedNearProdMap_val T (𝟙 W) (typedI1 T U V),
    id_val, typedI0_val T U V, typedI1_val T U V,
    codiagonalClass, leftInjectionClass, rightInjectionClass,
    objectIdempotent, tensorClass_classOf, tensorClass_classOf,
    coprodClass_classOf]
  rfl

@[simp] theorem distribRight_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    (distribRight U V W).1 =
      classOf T (distribRightIndex
        (objectCode U) (objectCode V) (objectCode W)) := by
  change (typedCoprodMap T
      (typedNearProdMap T (typedI0 T U V) (𝟙 W))
      (typedNearProdMap T (typedI1 T U V) (𝟙 W)) ≫
    typedCodiag T (nearProd (coprod U V) W)).1 = _
  rw [comp_val,
    typedCodiag_val T (nearProd (coprod U V) W),
    typedCoprodMap_val T
      (typedNearProdMap T (typedI0 T U V) (𝟙 W))
      (typedNearProdMap T (typedI1 T U V) (𝟙 W)),
    typedNearProdMap_val T (typedI0 T U V) (𝟙 W),
    typedNearProdMap_val T (typedI1 T U V) (𝟙 W),
    id_val, typedI0_val T U V, typedI1_val T U V,
    codiagonalClass, leftInjectionClass, rightInjectionClass,
    objectIdempotent, tensorClass_classOf, tensorClass_classOf,
    coprodClass_classOf]
  rfl

theorem distribLeft_eq_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    distribLeft W U V =
      arrowOfIndex T
        (.coproduct (.product (objectCode W) (objectCode U))
          (.product (objectCode W) (objectCode V)))
        (.product (objectCode W) (.coproduct (objectCode U) (objectCode V)))
        (distribLeftIndex (objectCode W) (objectCode U) (objectCode V)) := by
  symm
  apply arrowOfIndex_eq_of_class
  exact (distribLeft_val T W U V).symm

theorem distribRight_eq_arrowOfIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    distribRight U V W =
      arrowOfIndex T
        (.coproduct (.product (objectCode U) (objectCode W))
          (.product (objectCode V) (objectCode W)))
        (.product (.coproduct (objectCode U) (objectCode V)) (objectCode W))
        (distribRightIndex (objectCode U) (objectCode V) (objectCode W)) := by
  symm
  apply arrowOfIndex_eq_of_class
  exact (distribRight_val T U V W).symm

/-! ### Uniform inverse equations -/

theorem eqIndex_distribLeft_hom_inv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : STObjectCode) :
    EqIndex T
      (compIndex (distribLeftInvIndex W U V)
        (distribLeftIndex W U V))
      (deltaIndex (.coproduct (.product W U) (.product W V))) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval,
    eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rw [eventualGraph_distribLeftIndex_eval,
      distribLeftGraph_eval] at hp
    rw [eventualGraph_distribLeftInvIndex_eval,
      distribLeftInvGraph_eval] at hpy
    rcases hp with ⟨w, u, hx, hp, hW, hU⟩ | ⟨w, v, hx, hp, hW, hV⟩ <;>
      rcases hpy with ⟨w', u', hp', hy, hW', hU'⟩ |
        ⟨w', v', hp', hy, hW', hV'⟩
    · obtain ⟨hww, hut⟩ :=
        (pair_eq_pair_iff w (pair u 0) w' (pair u' 0)).mp
          (hp.symm.trans hp')
      have huu : u = u' := (pair_eq_pair_iff u 0 u' 0).mp hut |>.1
      subst w'
      subst u'
      constructor
      · rw [hx]
        exact (memberFormula_coproduct_left_pair_eval
          (.product W U) (.product W V) (pair w u)).mpr
            ((memberFormula_product_pair_eval W U w u).mpr ⟨hW, hU⟩)
      · exact hy.trans hx.symm
    · obtain ⟨-, hut⟩ :=
        (pair_eq_pair_iff w (pair u 0) w' (pair v' 1)).mp
          (hp.symm.trans hp')
      have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff u 0 v' 1).mp hut |>.2
      exact False.elim (zero_ne_one h01)
    · obtain ⟨-, hvt⟩ :=
        (pair_eq_pair_iff w (pair v 1) w' (pair u' 0)).mp
          (hp.symm.trans hp')
      have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff v 1 u' 0).mp hvt |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · obtain ⟨hww, hvt⟩ :=
        (pair_eq_pair_iff w (pair v 1) w' (pair v' 1)).mp
          (hp.symm.trans hp')
      have hvv : v = v' := (pair_eq_pair_iff v 1 v' 1).mp hvt |>.1
      subst w'
      subst v'
      constructor
      · rw [hx]
        exact (memberFormula_coproduct_right_pair_eval
          (.product W U) (.product W V) (pair w v)).mpr
            ((memberFormula_product_pair_eval W V w v).mpr ⟨hW, hV⟩)
      · exact hy.trans hx.symm
  · rintro ⟨hx, hy⟩
    rcases (memberFormula_coproduct_eval
        (.product W U) (.product W V) x).mp hx with
      ⟨a, hxa, ha⟩ | ⟨a, hxa, ha⟩
    · obtain ⟨w, u, hau, hW, hU⟩ :=
        (memberFormula_product_eval W U a).mp ha
      let p : M := pair w (pair u 0)
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribLeftIndex_eval,
          distribLeftGraph_eval]
        exact Or.inl ⟨w, u,
          hxa.trans (congrArg (fun z => pair z (0 : M)) hau),
          rfl, hW, hU⟩
      · rw [eventualGraph_distribLeftInvIndex_eval,
          distribLeftInvGraph_eval]
        exact Or.inl ⟨w, u, rfl,
          hy.trans hxa |>.trans
            (congrArg (fun z => pair z (0 : M)) hau), hW, hU⟩
    · obtain ⟨w, v, hav, hW, hV⟩ :=
        (memberFormula_product_eval W V a).mp ha
      let p : M := pair w (pair v 1)
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribLeftIndex_eval,
          distribLeftGraph_eval]
        exact Or.inr ⟨w, v,
          hxa.trans (congrArg (fun z => pair z (1 : M)) hav),
          rfl, hW, hV⟩
      · rw [eventualGraph_distribLeftInvIndex_eval,
          distribLeftInvGraph_eval]
        exact Or.inr ⟨w, v, rfl,
          hy.trans hxa |>.trans
            (congrArg (fun z => pair z (1 : M)) hav), hW, hV⟩

theorem eqIndex_distribLeft_inv_hom
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : STObjectCode) :
    EqIndex T
      (compIndex (distribLeftIndex W U V)
        (distribLeftInvIndex W U V))
      (deltaIndex (.product W (.coproduct U V))) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval,
    eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rw [eventualGraph_distribLeftInvIndex_eval,
      distribLeftInvGraph_eval] at hp
    rw [eventualGraph_distribLeftIndex_eval,
      distribLeftGraph_eval] at hpy
    rcases hp with ⟨w, u, hx, hp, hW, hU⟩ | ⟨w, v, hx, hp, hW, hV⟩ <;>
      rcases hpy with ⟨w', u', hp', hy, hW', hU'⟩ |
        ⟨w', v', hp', hy, hW', hV'⟩
    · obtain ⟨hwu, -⟩ :=
        (pair_eq_pair_iff (pair w u) 0 (pair w' u') 0).mp
          (hp.symm.trans hp')
      obtain ⟨hww, huu⟩ := (pair_eq_pair_iff w u w' u').mp hwu
      subst w'
      subst u'
      constructor
      · rw [hx]
        exact (memberFormula_product_pair_eval W (.coproduct U V) w
          (pair u 0)).mpr ⟨hW,
            (memberFormula_coproduct_left_pair_eval U V u).mpr hU⟩
      · exact hy.trans hx.symm
    · have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff (pair w u) 0 (pair w' v') 1).mp
          (hp.symm.trans hp') |>.2
      exact False.elim (zero_ne_one h01)
    · have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff (pair w v) 1 (pair w' u') 0).mp
          (hp.symm.trans hp') |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · obtain ⟨hwv, -⟩ :=
        (pair_eq_pair_iff (pair w v) 1 (pair w' v') 1).mp
          (hp.symm.trans hp')
      obtain ⟨hww, hvv⟩ := (pair_eq_pair_iff w v w' v').mp hwv
      subst w'
      subst v'
      constructor
      · rw [hx]
        exact (memberFormula_product_pair_eval W (.coproduct U V) w
          (pair v 1)).mpr ⟨hW,
            (memberFormula_coproduct_right_pair_eval U V v).mpr hV⟩
      · exact hy.trans hx.symm
  · rintro ⟨hx, hy⟩
    obtain ⟨w, t, hwt, hW, ht⟩ :=
      (memberFormula_product_eval W (.coproduct U V) x).mp hx
    rcases (memberFormula_coproduct_eval U V t).mp ht with
      ⟨u, htu, hU⟩ | ⟨v, htv, hV⟩
    · let p : M := pair (pair w u) 0
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribLeftInvIndex_eval,
          distribLeftInvGraph_eval]
        exact Or.inl ⟨w, u,
          hwt.trans (congrArg (fun z => pair w z) htu),
          rfl, hW, hU⟩
      · rw [eventualGraph_distribLeftIndex_eval,
          distribLeftGraph_eval]
        exact Or.inl ⟨w, u, rfl,
          hy.trans hwt |>.trans (congrArg (fun z => pair w z) htu),
          hW, hU⟩
    · let p : M := pair (pair w v) 1
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribLeftInvIndex_eval,
          distribLeftInvGraph_eval]
        exact Or.inr ⟨w, v,
          hwt.trans (congrArg (fun z => pair w z) htv),
          rfl, hW, hV⟩
      · rw [eventualGraph_distribLeftIndex_eval,
          distribLeftGraph_eval]
        exact Or.inr ⟨w, v, rfl,
          hy.trans hwt |>.trans (congrArg (fun z => pair w z) htv),
          hW, hV⟩

theorem eqIndex_distribRight_hom_inv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : STObjectCode) :
    EqIndex T
      (compIndex (distribRightInvIndex U V W)
        (distribRightIndex U V W))
      (deltaIndex (.coproduct (.product U W) (.product V W))) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval,
    eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rw [eventualGraph_distribRightIndex_eval,
      distribRightGraph_eval] at hp
    rw [eventualGraph_distribRightInvIndex_eval,
      distribRightInvGraph_eval] at hpy
    rcases hp with ⟨u, w, hx, hp, hU, hW⟩ | ⟨v, w, hx, hp, hV, hW⟩ <;>
      rcases hpy with ⟨u', w', hp', hy, hU', hW'⟩ |
        ⟨v', w', hp', hy, hV', hW'⟩
    · obtain ⟨hut, hww⟩ :=
        (pair_eq_pair_iff (pair u 0) w (pair u' 0) w').mp
          (hp.symm.trans hp')
      have huu : u = u' := (pair_eq_pair_iff u 0 u' 0).mp hut |>.1
      subst u'
      subst w'
      constructor
      · rw [hx]
        exact (memberFormula_coproduct_left_pair_eval
          (.product U W) (.product V W) (pair u w)).mpr
            ((memberFormula_product_pair_eval U W u w).mpr ⟨hU, hW⟩)
      · exact hy.trans hx.symm
    · obtain ⟨hut, -⟩ :=
        (pair_eq_pair_iff (pair u 0) w (pair v' 1) w').mp
          (hp.symm.trans hp')
      have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff u 0 v' 1).mp hut |>.2
      exact False.elim (zero_ne_one h01)
    · obtain ⟨hvt, -⟩ :=
        (pair_eq_pair_iff (pair v 1) w (pair u' 0) w').mp
          (hp.symm.trans hp')
      have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff v 1 u' 0).mp hvt |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · obtain ⟨hvt, hww⟩ :=
        (pair_eq_pair_iff (pair v 1) w (pair v' 1) w').mp
          (hp.symm.trans hp')
      have hvv : v = v' := (pair_eq_pair_iff v 1 v' 1).mp hvt |>.1
      subst v'
      subst w'
      constructor
      · rw [hx]
        exact (memberFormula_coproduct_right_pair_eval
          (.product U W) (.product V W) (pair v w)).mpr
            ((memberFormula_product_pair_eval V W v w).mpr ⟨hV, hW⟩)
      · exact hy.trans hx.symm
  · rintro ⟨hx, hy⟩
    rcases (memberFormula_coproduct_eval
        (.product U W) (.product V W) x).mp hx with
      ⟨a, hxa, ha⟩ | ⟨a, hxa, ha⟩
    · obtain ⟨u, w, hau, hU, hW⟩ :=
        (memberFormula_product_eval U W a).mp ha
      let p : M := pair (pair u 0) w
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribRightIndex_eval,
          distribRightGraph_eval]
        exact Or.inl ⟨u, w,
          hxa.trans (congrArg (fun z => pair z (0 : M)) hau),
          rfl, hU, hW⟩
      · rw [eventualGraph_distribRightInvIndex_eval,
          distribRightInvGraph_eval]
        exact Or.inl ⟨u, w, rfl,
          hy.trans hxa |>.trans
            (congrArg (fun z => pair z (0 : M)) hau), hU, hW⟩
    · obtain ⟨v, w, hav, hV, hW⟩ :=
        (memberFormula_product_eval V W a).mp ha
      let p : M := pair (pair v 1) w
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribRightIndex_eval,
          distribRightGraph_eval]
        exact Or.inr ⟨v, w,
          hxa.trans (congrArg (fun z => pair z (1 : M)) hav),
          rfl, hV, hW⟩
      · rw [eventualGraph_distribRightInvIndex_eval,
          distribRightInvGraph_eval]
        exact Or.inr ⟨v, w, rfl,
          hy.trans hxa |>.trans
            (congrArg (fun z => pair z (1 : M)) hav), hV, hW⟩

theorem eqIndex_distribRight_inv_hom
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : STObjectCode) :
    EqIndex T
      (compIndex (distribRightIndex U V W)
        (distribRightInvIndex U V W))
      (deltaIndex (.product (.coproduct U V) W)) := by
  apply complete.{0} T
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 :=
    models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_comp_eval,
    eventualGraph_deltaIndex_eval]
  constructor
  · rintro ⟨p, hp, hpy⟩
    rw [eventualGraph_distribRightInvIndex_eval,
      distribRightInvGraph_eval] at hp
    rw [eventualGraph_distribRightIndex_eval,
      distribRightGraph_eval] at hpy
    rcases hp with ⟨u, w, hx, hp, hU, hW⟩ | ⟨v, w, hx, hp, hV, hW⟩ <;>
      rcases hpy with ⟨u', w', hp', hy, hU', hW'⟩ |
        ⟨v', w', hp', hy, hV', hW'⟩
    · obtain ⟨huw, -⟩ :=
        (pair_eq_pair_iff (pair u w) 0 (pair u' w') 0).mp
          (hp.symm.trans hp')
      obtain ⟨huu, hww⟩ := (pair_eq_pair_iff u w u' w').mp huw
      subst u'
      subst w'
      constructor
      · rw [hx]
        exact (memberFormula_product_pair_eval (.coproduct U V) W
          (pair u 0) w).mpr
            ⟨(memberFormula_coproduct_left_pair_eval U V u).mpr hU, hW⟩
      · exact hy.trans hx.symm
    · have h01 : (0 : M) = 1 :=
        (pair_eq_pair_iff (pair u w) 0 (pair v' w') 1).mp
          (hp.symm.trans hp') |>.2
      exact False.elim (zero_ne_one h01)
    · have h10 : (1 : M) = 0 :=
        (pair_eq_pair_iff (pair v w) 1 (pair u' w') 0).mp
          (hp.symm.trans hp') |>.2
      exact False.elim (Arithmetic.one_ne_zero h10)
    · obtain ⟨hvw, -⟩ :=
        (pair_eq_pair_iff (pair v w) 1 (pair v' w') 1).mp
          (hp.symm.trans hp')
      obtain ⟨hvv, hww⟩ := (pair_eq_pair_iff v w v' w').mp hvw
      subst v'
      subst w'
      constructor
      · rw [hx]
        exact (memberFormula_product_pair_eval (.coproduct U V) W
          (pair v 1) w).mpr
            ⟨(memberFormula_coproduct_right_pair_eval U V v).mpr hV, hW⟩
      · exact hy.trans hx.symm
  · rintro ⟨hx, hy⟩
    obtain ⟨t, w, htw, ht, hW⟩ :=
      (memberFormula_product_eval (.coproduct U V) W x).mp hx
    rcases (memberFormula_coproduct_eval U V t).mp ht with
      ⟨u, htu, hU⟩ | ⟨v, htv, hV⟩
    · let p : M := pair (pair u w) 0
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribRightInvIndex_eval,
          distribRightInvGraph_eval]
        exact Or.inl ⟨u, w,
          htw.trans (congrArg (fun z => pair z w) htu),
          rfl, hU, hW⟩
      · rw [eventualGraph_distribRightIndex_eval,
          distribRightGraph_eval]
        exact Or.inl ⟨u, w, rfl,
          hy.trans htw |>.trans (congrArg (fun z => pair z w) htu),
          hU, hW⟩
    · let p : M := pair (pair v w) 1
      refine ⟨p, ?_, ?_⟩
      · rw [eventualGraph_distribRightInvIndex_eval,
          distribRightInvGraph_eval]
        exact Or.inr ⟨v, w,
          htw.trans (congrArg (fun z => pair z w) htv),
          rfl, hV, hW⟩
      · rw [eventualGraph_distribRightIndex_eval,
          distribRightGraph_eval]
        exact Or.inr ⟨v, w, rfl,
          hy.trans htw |>.trans (congrArg (fun z => pair z w) htv),
          hV, hW⟩

/-! ### The distributive instance -/

theorem typed_distribLeft_hom_inv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    distribLeft W U V ≫ typedDistribLeftInv T W U V =
      𝟙 (coprod (nearProd W U) (nearProd W V)) := by
  apply CodedHom.ext
  rw [comp_val, distribLeft_val T W U V,
    typedDistribLeftInv_val T W U V, id_val]
  change classOf T
      (compIndex
        (distribLeftInvIndex (objectCode W) (objectCode U) (objectCode V))
        (distribLeftIndex (objectCode W) (objectCode U) (objectCode V))) =
    classOf T
      (deltaIndex (.coproduct
        (.product (objectCode W) (objectCode U))
        (.product (objectCode W) (objectCode V))))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_distribLeft_hom_inv T
      (objectCode W) (objectCode U) (objectCode V))

theorem typed_distribLeft_inv_hom
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (W U V : CodedProgramCategory T) :
    typedDistribLeftInv T W U V ≫ distribLeft W U V =
      𝟙 (nearProd W (coprod U V)) := by
  apply CodedHom.ext
  rw [comp_val, typedDistribLeftInv_val T W U V,
    distribLeft_val T W U V, id_val]
  change classOf T
      (compIndex
        (distribLeftIndex (objectCode W) (objectCode U) (objectCode V))
        (distribLeftInvIndex (objectCode W) (objectCode U) (objectCode V))) =
    classOf T
      (deltaIndex (.product (objectCode W)
        (.coproduct (objectCode U) (objectCode V))))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_distribLeft_inv_hom T
      (objectCode W) (objectCode U) (objectCode V))

theorem typed_distribRight_hom_inv
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    distribRight U V W ≫ typedDistribRightInv T U V W =
      𝟙 (coprod (nearProd U W) (nearProd V W)) := by
  apply CodedHom.ext
  rw [comp_val, distribRight_val T U V W,
    typedDistribRightInv_val T U V W, id_val]
  change classOf T
      (compIndex
        (distribRightInvIndex (objectCode U) (objectCode V) (objectCode W))
        (distribRightIndex (objectCode U) (objectCode V) (objectCode W))) =
    classOf T
      (deltaIndex (.coproduct
        (.product (objectCode U) (objectCode W))
        (.product (objectCode V) (objectCode W))))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_distribRight_hom_inv T
      (objectCode U) (objectCode V) (objectCode W))

theorem typed_distribRight_inv_hom
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (U V W : CodedProgramCategory T) :
    typedDistribRightInv T U V W ≫ distribRight U V W =
      𝟙 (nearProd (coprod U V) W) := by
  apply CodedHom.ext
  rw [comp_val, typedDistribRightInv_val T U V W,
    distribRight_val T U V W, id_val]
  change classOf T
      (compIndex
        (distribRightIndex (objectCode U) (objectCode V) (objectCode W))
        (distribRightInvIndex (objectCode U) (objectCode V) (objectCode W))) =
    classOf T
      (deltaIndex (.product
        (.coproduct (objectCode U) (objectCode V)) (objectCode W)))
  exact (classOf_eq_classOf_iff T _ _).mpr
    (eqIndex_distribRight_inv_hom T
      (objectCode U) (objectCode V) (objectCode W))

/-- The typed program category is distributive on both sides. -/
instance codedProgramCategoryDistributive
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    Distributive (CodedProgramCategory T) where
  isIso_distribLeft W U V :=
    ⟨⟨typedDistribLeftInv T W U V,
      typed_distribLeft_hom_inv T W U V,
      typed_distribLeft_inv_hom T W U V⟩⟩
  isIso_distribRight U V W :=
    ⟨⟨typedDistribRightInv T U V W,
      typed_distribRight_hom_inv T U V W,
      typed_distribRight_inv_hom T U V W⟩⟩

/-! ## Focused coproduct applications -/

/-- The nowhere-defined typed arrow, used here only as a branch of a genuine
copairing. -/
def emptyArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) : object T Q ⟶ object T R :=
  arrowOfIndex T Q R ConcreteEmptyGraph.concreteEmptyIndex

/-- Copairing the identity with an empty right branch still restricts along
the left injection to the identity.  No zero-morphism structure is used. -/
theorem copair_identity_empty_left
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) :
    i0 (object T Q) (object T R) ≫
        copair (𝟙 (object T Q)) (emptyArrow T R Q) =
      𝟙 (object T Q) :=
  typed_i0_copair T (𝟙 (object T Q)) (emptyArrow T R Q)

/-- Copairing an empty left branch with the identity restricts along the
right injection to the identity. -/
theorem copair_empty_identity_right
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) :
    i1 (object T Q) (object T R) ≫
        copair (emptyArrow T Q R) (𝟙 (object T R)) =
      𝟙 (object T R) :=
  typed_i1_copair T (emptyArrow T Q R) (𝟙 (object T R))

/-- PA refutes every closed application of a tagged-union program whose input
has the explicit invalid tag `2`. -/
theorem pa_proves_not_coprodIndex_invalidTag
    (q r u y : ℕ) :
    𝗣𝗔 ⊢ ∼(eventualGraph (coprodIndex q r)).val/[
      Nat.pair u 2, y] := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simp only [LogicalConnective.HomClass.map_neg, graph_instance_eval]
  intro h
  apply not_eventualGraph_coprodIndex_pair_of_tag_ne
    q r (u : M) ((2 : ℕ) : M) (y : M) (by norm_num) (by norm_num)
  simpa only [numeral_eq_natCast, coe_pair_eq_pair_coe] using h

end

end FailureOfComposition.TypedCoproducts
