/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.GeneratedQuotient
import FailureOfComposition.NumericalProofBridge.RETheory

/-!
# The uniform-provability quotient of production program indices

For an arithmetic theory `T`, two external natural-number indices are related
when `T` proves uniform equality of their production evaluator graphs.  This
module constructs the resulting quotient.  If `T` extends PA in provability
strength, canonical program composition and the production identity index make
the quotient a monoid.  Multiplication is ordered so that `f * g` applies `g`
first and then `f`.

For a recursively enumerable presentation of the axioms of `T`, quotient
equality and provable graph instances are connected to the existing numerical
proof presentation.  The quotient concerns only the production number object.
No typed source objects, product or coproduct structure, or identification with
the manuscript's full category `S_T` is asserted here.
-/

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Metamath.Feferman Arith.Feferman.Specialization
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.UniformIndexQuotient

open ProofSearch ConcreteEvaluator NumericalProofBridge

/-! ## Uniform graph equality -/

/-- Uniform `T`-provable equality of the production graphs at two external
program indices. -/
def EqIndex (T : ArithmeticTheory) (q r : ℕ) : Prop :=
  Uniform T (eventualGraph q) (eventualGraph r)

/-- Uniform graph equality is reflexive in every extension of PA. -/
theorem uniform_refl (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (F : Graph) : Uniform T F F := by
  apply complete.{0} T
  intro M _ _
  simp [models_iff]

/-- Uniform graph equality is symmetric in every extension of PA. -/
theorem uniform_symm {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F G : Graph}
    (hFG : Uniform T F G) : Uniform T G F := by
  apply complete.{0} T
  intro M _ hM
  have hFG' : M↓[ℒₒᵣ] ⊧ uniformSentence F G :=
    consequence_iff.mp (Theory.Proof.sound hFG) M hM
  simp only [models_iff, uniformSentence_eval] at hFG' ⊢
  exact fun x y => (hFG' x y).symm

/-- Uniform graph equality is transitive in every extension of PA. -/
theorem uniform_trans {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {F G H : Graph}
    (hFG : Uniform T F G) (hGH : Uniform T G H) : Uniform T F H := by
  apply complete.{0} T
  intro M _ hM
  have hFG' : M↓[ℒₒᵣ] ⊧ uniformSentence F G :=
    consequence_iff.mp (Theory.Proof.sound hFG) M hM
  have hGH' : M↓[ℒₒᵣ] ⊧ uniformSentence G H :=
    consequence_iff.mp (Theory.Proof.sound hGH) M hM
  simp only [models_iff, uniformSentence_eval] at hFG' hGH' ⊢
  exact fun x y => (hFG' x y).trans (hGH' x y)

/-- Relational composition preserves uniform graph equality in both
arguments, within the same theory. -/
theorem uniform_comp_congr {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {F F' G G' : Graph}
    (hF : Uniform T F F') (hG : Uniform T G G') :
    Uniform T (comp F G) (comp F' G') := by
  apply complete.{0} T
  intro M _ hM
  have hF' : M↓[ℒₒᵣ] ⊧ uniformSentence F F' :=
    consequence_iff.mp (Theory.Proof.sound hF) M hM
  have hG' : M↓[ℒₒᵣ] ⊧ uniformSentence G G' :=
    consequence_iff.mp (Theory.Proof.sound hG) M hM
  simp only [models_iff, uniformSentence_eval] at hF' hG' ⊢
  intro x z
  simp only [comp_eval, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact exists_congr fun y => and_congr (hG' x y) (hF' y z)

@[simp] theorem graph_instance_eval
    {M : Type*} [ORingStructure M] (F : Graph) (n m : ℕ) :
    (F.val/[n, m]).Evalb (M := M) ![] ↔
      F.val.Evalb ![(ORingStructure.numeral n : M),
        (ORingStructure.numeral m : M)] := by
  simp

/-- A uniform proof can be specialized at fixed standard input and output
numerals, in either direction. -/
theorem uniform_instance_provable_iff {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {F G : Graph}
    (hFG : Uniform T F G) (n m : ℕ) :
    (T ⊢ F.val/[n, m]) ↔ (T ⊢ G.val/[n, m]) := by
  constructor
  · intro hF
    apply complete.{0} T
    intro M _ hM
    have hFG' : M↓[ℒₒᵣ] ⊧ uniformSentence F G :=
      consequence_iff.mp (Theory.Proof.sound hFG) M hM
    have hF' : M↓[ℒₒᵣ] ⊧ F.val/[n, m] :=
      consequence_iff.mp (Theory.Proof.sound hF) M hM
    rw [models_iff, uniformSentence_eval] at hFG'
    rw [models_iff, graph_instance_eval] at hF' ⊢
    exact (hFG' (ORingStructure.numeral n : M)
      (ORingStructure.numeral m : M)).mp hF'
  · intro hG
    apply complete.{0} T
    intro M _ hM
    have hFG' : M↓[ℒₒᵣ] ⊧ uniformSentence F G :=
      consequence_iff.mp (Theory.Proof.sound hFG) M hM
    have hG' : M↓[ℒₒᵣ] ⊧ G.val/[n, m] :=
      consequence_iff.mp (Theory.Proof.sound hG) M hM
    rw [models_iff, uniformSentence_eval] at hFG'
    rw [models_iff, graph_instance_eval] at hG' ⊢
    exact (hFG' (ORingStructure.numeral n : M)
      (ORingStructure.numeral m : M)).mpr hG'

theorem eqIndex_refl (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (q : ℕ) : EqIndex T q q :=
  uniform_refl T (eventualGraph q)

theorem eqIndex_symm {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {q r : ℕ}
    (h : EqIndex T q r) : EqIndex T r q :=
  uniform_symm h

theorem eqIndex_trans {T : ArithmeticTheory} [𝗣𝗔 ⪯ T] {q r s : ℕ}
    (hqr : EqIndex T q r) (hrs : EqIndex T r s) : EqIndex T q s :=
  uniform_trans hqr hrs

/-- The setoid of external production indices under uniform `T`-provable
graph equality. -/
def eqIndexSetoid (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : Setoid ℕ where
  r := EqIndex T
  iseqv := ⟨eqIndex_refl T, eqIndex_symm, eqIndex_trans⟩

/-! ## Canonical composition -/

/-- Canonical composition applies its second argument first and then its first
argument. -/
abbrev compIndex : ℕ → ℕ → ℕ := canonicalPartrecCompIndex

/-- Canonical composition preserves uniform `T`-provable graph equality in
both arguments. -/
theorem eqIndex_comp_congr (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    {f f' g g' : ℕ} (hf : EqIndex T f f') (hg : EqIndex T g g') :
    EqIndex T (compIndex f g) (compIndex f' g') := by
  exact uniform_trans (WeakerThan.pbl (eventualGraph_composition f g))
    (uniform_trans (uniform_comp_congr hf hg)
      (uniform_symm (WeakerThan.pbl (eventualGraph_composition f' g'))))

/-- Canonical composition is associative modulo uniform `T`-provable graph
equality. -/
theorem eqIndex_comp_assoc (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (f g h : ℕ) :
    EqIndex T (compIndex (compIndex f g) h)
      (compIndex f (compIndex g h)) := by
  refine uniform_trans
    (WeakerThan.pbl (eventualGraph_composition (compIndex f g) h)) ?_
  refine uniform_trans
    (uniform_comp_congr
      (WeakerThan.pbl (eventualGraph_composition f g))
      (uniform_refl T (eventualGraph h))) ?_
  refine uniform_trans
    (WeakerThan.pbl
      (GeneratedCongruence.comp_associative_uniform
        (eventualGraph f) (eventualGraph g) (eventualGraph h))) ?_
  refine uniform_trans
    (uniform_comp_congr (uniform_refl T (eventualGraph f))
      (uniform_symm (WeakerThan.pbl (eventualGraph_composition g h)))) ?_
  exact uniform_symm
    (WeakerThan.pbl (eventualGraph_composition f (compIndex g h)))

/-- The production identity index is a left identity modulo uniform
`T`-provable graph equality. -/
theorem eqIndex_identity_comp (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (f : ℕ) :
    EqIndex T (compIndex Kleene.identityIndex f) f := by
  refine uniform_trans
    (WeakerThan.pbl (eventualGraph_composition Kleene.identityIndex f)) ?_
  refine uniform_trans
    (uniform_comp_congr (WeakerThan.pbl eventualGraph_identity)
      (uniform_refl T (eventualGraph f))) ?_
  exact WeakerThan.pbl (identity_comp (eventualGraph f))

/-- The production identity index is a right identity modulo uniform
`T`-provable graph equality. -/
theorem eqIndex_comp_identity (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (f : ℕ) :
    EqIndex T (compIndex f Kleene.identityIndex) f := by
  refine uniform_trans
    (WeakerThan.pbl (eventualGraph_composition f Kleene.identityIndex)) ?_
  refine uniform_trans
    (uniform_comp_congr (uniform_refl T (eventualGraph f))
      (WeakerThan.pbl eventualGraph_identity)) ?_
  exact WeakerThan.pbl
    (GeneratedCongruence.comp_right_identity (eventualGraph f))

/-! ## The quotient monoid -/

/-- Production program indices modulo uniform `T`-provable graph equality. -/
def ProgramQuotient (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :=
  Quotient (eqIndexSetoid T)

/-- The quotient class of an external production program index. -/
def classOf (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (q : ℕ) : ProgramQuotient T :=
  Quotient.mk (eqIndexSetoid T) q

/-- Equality of represented classes is exactly uniform `T`-provable graph
equality. -/
theorem classOf_eq_classOf_iff (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (q r : ℕ) :
    classOf T q = classOf T r ↔ EqIndex T q r := by
  change Quotient.mk (eqIndexSetoid T) q =
      Quotient.mk (eqIndexSetoid T) r ↔ EqIndex T q r
  constructor
  · exact Quotient.exact
  · intro h
    apply Quotient.sound
    exact h

instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : Mul (ProgramQuotient T) where
  mul := Quotient.lift₂
    (fun f g => classOf T (compIndex f g))
    (fun _ _ _ _ hf hg => Quotient.sound (eqIndex_comp_congr T hf hg))

instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : One (ProgramQuotient T) where
  one := classOf T Kleene.identityIndex

@[simp] theorem mul_classOf (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (f g : ℕ) :
    classOf T f * classOf T g = classOf T (compIndex f g) := rfl

theorem one_eq_classOf (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (1 : ProgramQuotient T) = classOf T Kleene.identityIndex := rfl

instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : Monoid (ProgramQuotient T) where
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c ?_
    intro f g h
    exact Quotient.sound (eqIndex_comp_assoc T f g h)
  one_mul a := by
    refine Quotient.inductionOn a ?_
    intro f
    exact Quotient.sound (eqIndex_identity_comp T f)
  mul_one a := by
    refine Quotient.inductionOn a ?_
    intro f
    exact Quotient.sound (eqIndex_comp_identity T f)

/-- The quotient unit acts on every represented program class on the left. -/
theorem one_mul_classOf (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    (1 : ProgramQuotient T) * classOf T q = classOf T q :=
  one_mul (classOf T q)

/-- The quotient unit acts on every represented program class on the right. -/
theorem classOf_mul_one (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    classOf T q * (1 : ProgramQuotient T) = classOf T q :=
  mul_one (classOf T q)

/-! ## Numerical equality proofs -/

/-- The numerical proof predicate for equality of two production program
indices in the selected r.e.-theory presentation. -/
def PrfEq (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : ℕ) : Prop :=
  Proof_T (reTheoryExtendedTheoryPresentation T hRE) p (equalityCode q r)

/-- For fixed `T` and its selected stage presentation, `PrfEq` is primitive
recursive in the proof code and the two program indices. -/
theorem primrecPred_prfEq (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    PrimrecPred (fun z : (ℕ × ℕ) × ℕ =>
      PrfEq T hRE z.1.1 z.1.2 z.2) := by
  have hProof : PrimrecPred (fun z : ℕ × ℕ =>
      Proof_T (reTheoryExtendedPRTheoryPresentation T hRE).toTheory z.1 z.2) :=
    primrecRel_proof_T (reTheoryExtendedPRTheoryPresentation T hRE)
  have hArgs : Primrec (fun z : (ℕ × ℕ) × ℕ =>
      (z.1.1, equalityCode z.1.2 z.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      (primrec₂_equalityCode.comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  simpa [PrfEq, reTheoryExtendedPRTheoryPresentation,
    reTheoryExtendedTheoryPresentation, extendedPRTheoryPresentation] using
      hProof.comp hArgs

/-- Quotient equality is exactly the existential projection of the numerical
equality-proof predicate. -/
theorem classOf_eq_classOf_iff_exists_prfEq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (q r : ℕ) :
    classOf T q = classOf T r ↔ ∃ p : ℕ, PrfEq T hRE p q r := by
  rw [classOf_eq_classOf_iff]
  have hfirst : Uniform T (firstSuccessGraph q) (eventualGraph q) :=
    WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph q)
  constructor
  · intro hqr
    apply (reTheory_provable_uniform_iff_exists_equalityCode_proof_T
      T hRE q r).mp
    exact uniform_trans hfirst hqr
  · intro hp
    apply uniform_trans (uniform_symm hfirst)
    apply (reTheory_provable_uniform_iff_exists_equalityCode_proof_T
      T hRE q r).mpr
    simpa [PrfEq] using hp

/-! ## Representative-independent provable computation -/

/-- Uniform equality of indices preserves provability of every fixed standard
graph instance. -/
theorem eqIndex_provable_instance_iff {T : ArithmeticTheory} [𝗣𝗔 ⪯ T]
    {q r : ℕ}
    (hqr : EqIndex T q r) (n m : ℕ) :
    (T ⊢ (eventualGraph q).val/[n, m]) ↔
      (T ⊢ (eventualGraph r).val/[n, m]) :=
  uniform_instance_provable_iff hqr n m

/-- Provability of a fixed production computation, defined on quotient
classes. -/
def ProvableAt (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (a : ProgramQuotient T) (n m : ℕ) : Prop :=
  Quotient.lift
    (fun q => T ⊢ (eventualGraph q).val/[n, m])
    (fun _ _ h => propext (eqIndex_provable_instance_iff h n m)) a

@[simp] theorem provableAt_classOf (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (q n m : ℕ) :
    ProvableAt T (classOf T q) n m ↔
      T ⊢ (eventualGraph q).val/[n, m] :=
  Iff.rfl

/-- The accepted first-success/eventual comparison also identifies the
provability of their fixed standard instances. -/
theorem firstSuccess_provable_iff_eventual
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q n m : ℕ) :
    (T ⊢ (firstSuccessGraph q).val/[n, m]) ↔
      (T ⊢ (eventualGraph q).val/[n, m]) :=
  uniform_instance_provable_iff
    (WeakerThan.pbl (firstSuccessGraph_uniform_eventualGraph q)) n m

/-- The right graph tag gives the exact numerical characterization of
`ProvableAt` on a representative. -/
theorem provableAt_classOf_iff_exists_rightProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (q n m : ℕ) :
    ProvableAt T (classOf T q) n m ↔
      ∃ h : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
        (rightInstanceCode q n m) := by
  rw [provableAt_classOf]
  exact reTheory_provable_right_iff_exists_rightInstanceCode_proof_T
    T hRE q n m

/-- Through the PA comparison with the first-success graph, the distinct left
graph tag gives a second exact numerical characterization. -/
theorem provableAt_classOf_iff_exists_leftProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (q n m : ℕ) :
    ProvableAt T (classOf T q) n m ↔
      ∃ h : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
        (leftInstanceCode q n m) := by
  rw [provableAt_classOf]
  exact (firstSuccess_provable_iff_eventual T q n m).symm.trans
    (reTheory_provable_left_iff_exists_leftInstanceCode_proof_T
      T hRE q n m)

/-! ## Identity regression -/

/-- Every standard numeral is provably fixed by the relational identity
graph in every theory extending PA in provability strength. -/
theorem identity_instance_provable
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (n : ℕ) :
    T ⊢ identity.val/[n, n] := by
  apply WeakerThan.pbl (𝓢 := 𝗣𝗔)
  apply complete.{0} 𝗣𝗔
  intro M _ _
  simp [models_iff, identity, numeral_eq_natCast]

/-- The quotient unit has a provable production computation from every
standard numeral to itself. -/
theorem provableAt_one (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (n : ℕ) :
    ProvableAt T (1 : ProgramQuotient T) n n := by
  rw [one_eq_classOf, provableAt_classOf]
  apply (uniform_instance_provable_iff
    (WeakerThan.pbl (𝓢 := 𝗣𝗔) eventualGraph_identity) n n).mpr
  exact identity_instance_provable T n

/-- The identity regression also has a numerical proof at the right-instance
tag, without selecting or computing a theorem-enumeration stage. -/
theorem exists_identity_rightProof
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) (n : ℕ) :
    ∃ h : ℕ, Proof_T (reTheoryExtendedTheoryPresentation T hRE) h
      (rightInstanceCode Kleene.identityIndex n n) := by
  apply (provableAt_classOf_iff_exists_rightProof
    T hRE Kleene.identityIndex n n).mp
  simpa only [← one_eq_classOf T] using provableAt_one T n

end FailureOfComposition.UniformIndexQuotient
