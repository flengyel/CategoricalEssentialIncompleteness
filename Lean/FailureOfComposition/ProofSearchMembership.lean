/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.TypedProgramCategory

/-!
# The exact proof-search membership boundary

This module internalizes the existing `UniformIndexQuotient.PrfEq` predicate
without changing its theory presentation.  It then records the source and
target formulas required by Appendix B, clause B1(2), for a normalized typed
representative from an arbitrary coded object to `omega`.

The variables of `prfEqFormula` are, in order, the proof code, the left program
index, and the right program index.  In `typedProofSearchMembershipFormula`,
the input is free, while the output program index and its `PrfEq` witness are
quantified internally.  The object code, the raw representative, and the
comparison index are fixed external parameters.

The final section states the exact primitive-recursive transport specification
needed at this boundary.  The existing quotient proves that a target witness
exists over the standard natural numbers, but it does not select that witness
primitive recursively and does not prove the corresponding arbitrary-model
preservation statement.  Accordingly, no B1(2) completion theorem is asserted
here.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open Metamath.Feferman Arith.Feferman.Specialization
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.ProofSearchMembership

open CodedObjectMembership ConcreteEvaluator NumericalProofBridge
open TypedProgramCategory UniformIndexQuotient

noncomputable section

/-! ## The existing `PrfEq` predicate as an arithmetic formula -/

/-- The exact internal graph of the existing `PrfEq` checker.

The variable order is `(p, q, r)`: `p` is checked as a proof of the existing
tagged formula `equalityCode q r` in
`reTheoryExtendedTheoryPresentation T hRE`. -/
def prfEqFormula
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) :
    𝚺₁.Semisentence 3 := .mkSigma
  “p q r. ∃ a, !equalityCodeGraph a q r ∧
    !(reTheoryExtendedProofGraph T hRE) p a”

@[simp] theorem prfEqFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : M) :
    Semiformula.Evalb (M := M) ![p, q, r]
        (prfEqFormula T hRE).val ↔
      Semiformula.Evalb (M := M)
        ![p, equalityCodeValue q r]
        (reTheoryExtendedProofGraph T hRE).val := by
  simp [prfEqFormula, equalityCodeGraph_iff]

/-- Over the standard natural numbers, `prfEqFormula` is definitionally tied
to the exact checker used by `UniformIndexQuotient.PrfEq`. -/
@[simp] theorem prfEqFormula_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (p q r : ℕ) :
    Semiformula.Evalb (M := ℕ) ![p, q, r]
        (prfEqFormula T hRE).val ↔
      PrfEq T hRE p q r := by
  rw [prfEqFormula_eval, equalityCodeValue_nat,
    reTheoryExtendedProofGraph_nat_iff]
  rfl

/-! ## Normalized typed proof-search membership -/

/-- The representative actually used at the typed boundary.  The raw external
index `q` is restricted to the coded source `Z` and to target `omega`. -/
def typedRepresentative (Z : STObjectCode) (q : ℕ) : ℕ :=
  normalizeIndex Z .omega q

/-- The B1(2) proof-search membership body for a fixed external representative
`q` and comparison index `d`.

The only free variable is the input `u`.  Both the output program index `y`
and the exact-checker proof code `p` are quantified inside the formula. -/
def typedProofSearchMembershipFormula
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (q d : ℕ) : 𝚺₁.Semisentence 1 := .mkSigma
  “u. ∃ y,
    !(eventualGraph (typedRepresentative Z q)).val u y ∧
    ∃ p, !(prfEqFormula T hRE).val p y !!(d)”

@[simp] theorem typedProofSearchMembershipFormula_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (q d : ℕ) (u : M) :
    Semiformula.Evalb (M := M) ![u]
        (typedProofSearchMembershipFormula T hRE Z q d).val ↔
      ∃ y : M,
        (eventualGraph (typedRepresentative Z q)).val.Evalb ![u, y] ∧
        ∃ p : M,
          (reTheoryExtendedProofGraph T hRE).val.Evalb
            ![p, equalityCodeValue y (ORingStructure.numeral d)] := by
  simp [typedProofSearchMembershipFormula]

/-- Standard-natural-number adequacy of the displayed membership body.  In
particular, the endpoint is the original `PrfEq`, not an extended checker. -/
@[simp] theorem typedProofSearchMembershipFormula_nat_iff
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (q d u : ℕ) :
    Semiformula.Evalb (M := ℕ) ![u]
        (typedProofSearchMembershipFormula T hRE Z q d).val ↔
      ∃ y : ℕ,
        (eventualGraph (typedRepresentative Z q)).val.Evalb ![u, y] ∧
        ∃ p : ℕ, PrfEq T hRE p y d := by
  rw [typedProofSearchMembershipFormula_eval]
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  apply exists_congr
  intro p
  rw [equalityCodeValue_nat, reTheoryExtendedProofGraph_nat_iff]
  simp [PrfEq]

/-- The discharged open-assumption endpoint for source representative `h` and
target representative `k`.  The variable order consists solely of the free
input `u`; the formula reads
`u ∈ Z → membership(h,u,d) → membership(k,u,d)`. -/
def typedProofSearchTransferFormula
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d : ℕ) : ArithmeticSemisentence 1 :=
  “u. !(memberFormula Z).val u →
    (!(typedProofSearchMembershipFormula T hRE Z h d).val u →
      !(typedProofSearchMembershipFormula T hRE Z k d).val u)”

/-- The universal closure required by B1(2). -/
def typedProofSearchTransferClosure
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d : ℕ) : ArithmeticSentence :=
  ∀¹ typedProofSearchTransferFormula T hRE Z h k d

/-- The closed numeral-substitution endpoint required by B1(2). -/
def typedProofSearchTransferNumeral
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d u : ℕ) : ArithmeticSentence :=
  (typedProofSearchTransferFormula T hRE Z h k d)/[u]

@[simp] theorem typedProofSearchTransferFormula_eval
    {M : Type*} [ORingStructure M]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d : ℕ) (u : M) :
    Semiformula.Evalb (M := M) ![u]
        (typedProofSearchTransferFormula T hRE Z h k d) ↔
      (memberFormula Z).val.Evalb ![u] →
        (typedProofSearchMembershipFormula T hRE Z h d).val.Evalb ![u] →
          (typedProofSearchMembershipFormula T hRE Z k d).val.Evalb ![u] := by
  simp [typedProofSearchTransferFormula]

@[simp] theorem typedProofSearchTransferClosure_eval
    {M : Type*} [ORingStructure M]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d : ℕ) :
    (typedProofSearchTransferClosure T hRE Z h k d).Evalb
        (M := M) ![] ↔
      ∀ u : M,
        (memberFormula Z).val.Evalb ![u] →
          (typedProofSearchMembershipFormula T hRE Z h d).val.Evalb ![u] →
            (typedProofSearchMembershipFormula T hRE Z k d).val.Evalb ![u] := by
  simp [typedProofSearchTransferClosure]

@[simp] theorem typedProofSearchTransferNumeral_eval
    {M : Type*} [ORingStructure M]
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d u : ℕ) :
    (typedProofSearchTransferNumeral T hRE Z h k d u).Evalb
        (M := M) ![] ↔
      (memberFormula Z).val.Evalb ![(ORingStructure.numeral u : M)] →
        (typedProofSearchMembershipFormula T hRE Z h d).val.Evalb
            ![(ORingStructure.numeral u : M)] →
          (typedProofSearchMembershipFormula T hRE Z k d).val.Evalb
            ![(ORingStructure.numeral u : M)] := by
  simp [typedProofSearchTransferNumeral,
    typedProofSearchTransferFormula]

/-! ## The exact missing proof-code operation -/

/-- Packed input convention `((((e,p),y),y'),d)` for a proposed exact-checker
transport.  Here `e` proves equality of `y` and `y'`, while `p` proves equality
of `y` and `d`. -/
abbrev PrfEqTransportArgs := (((ℕ × ℕ) × ℕ) × ℕ) × ℕ

/-- Correctness required of a numerical `PrfEq` transport.  The conclusion is
checked by the same presentation as both premises. -/
def PrfEqTransportCorrect
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (transport : PrfEqTransportArgs → ℕ) : Prop :=
  ∀ e p y y' d : ℕ,
    PrfEq T hRE e y y' →
      PrfEq T hRE p y d →
        PrfEq T hRE (transport ((((e, p), y), y'), d)) y' d

/-- The precise effective closure datum missing from the current checker
interface: a total primitive-recursive function satisfying
`PrfEqTransportCorrect`. -/
def HasPrimitiveRecursivePrfEqTransport
    (T : ArithmeticTheory)
    (hRE : REPred (FailureOfComposition.AxiomCodes T)) : Prop :=
  ∃ transport : PrfEqTransportArgs → ℕ,
    Primrec transport ∧ PrfEqTransportCorrect T hRE transport

/-- Exact-checker transport witnesses exist extensionally over `ℕ`.  This
uses quotient transitivity and deliberately makes no claim that the witness is
selected primitive recursively. -/
theorem exists_prfEq_transport
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    {e p y y' d : ℕ}
    (he : PrfEq T hRE e y y')
    (hp : PrfEq T hRE p y d) :
    ∃ q : ℕ, PrfEq T hRE q y' d := by
  have hyy' : classOf T y = classOf T y' :=
    (classOf_eq_classOf_iff_exists_prfEq T hRE y y').mpr ⟨e, he⟩
  have hyd : classOf T y = classOf T d :=
    (classOf_eq_classOf_iff_exists_prfEq T hRE y d).mpr ⟨p, hp⟩
  apply (classOf_eq_classOf_iff_exists_prfEq T hRE y' d).mp
  exact hyy'.symm.trans hyd

/-- At a fixed standard input, supplied source and target computations and a
supplied exact-checker equality proof reduce the membership endpoint to the
single missing witness selection. -/
theorem exists_typedProofSearchMembership_of_outputs
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (Z : STObjectCode) (h k d u y y' e p : ℕ)
    (_hh : (eventualGraph (typedRepresentative Z h)).val.Evalb ![u, y])
    (hk : (eventualGraph (typedRepresentative Z k)).val.Evalb ![u, y'])
    (he : PrfEq T hRE e y y')
    (hp : PrfEq T hRE p y d) :
    (typedProofSearchMembershipFormula T hRE Z k d).val.Evalb ![u] := by
  obtain ⟨q, hq⟩ := exists_prfEq_transport T hRE he hp
  exact (typedProofSearchMembershipFormula_nat_iff T hRE Z k d u).mpr
    ⟨y', hk, q, hq⟩

end

end FailureOfComposition.ProofSearchMembership
