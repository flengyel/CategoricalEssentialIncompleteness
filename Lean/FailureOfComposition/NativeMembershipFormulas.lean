/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeFamilyApplications

/-!
# Native membership and totality assembly formulas

Acceptance of a family-proof code `e` is an arithmetic assertion. A proof
`a` of that assertion is a different input to the numerical constructor.
Membership existentially quantifies an output index and a native equality
proof. The fixed schemas assemble totality and these existential witnesses
inside derivations; their later applications consume proofs, not model truth.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeMembershipAssembly

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeFamilyExtraction
open FailureOfComposition.NativeInternalGraphs
open FailureOfComposition.NativeInternalAxiomGraph
open FailureOfComposition.NativeInternalEquality

def acceptanceFormulaFor (P : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 2 := .mkSigma
  “p c. !P 1 p c”

/-- Coordinates `(proof,formula)`; the result bit is literally one. -/
noncomputable def acceptanceFormula (S : ArithmeticTheory) [S.Δ₁] : 𝚺₁.Semisentence 2 :=
  acceptanceFormulaFor (nativeProofCheckGraph (canonicalAxiomGraph S))

noncomputable def familyAcceptanceFor (A : 𝚺₁.Semisentence 2)
    (F : ArithmeticSentence) : 𝚺₁.Semisentence 1 := .mkSigma
  “e. !A e ↑(Encodable.encode F)”

/-- A unary assertion about `e`, not the family sentence proved by `e`. -/
noncomputable def familyAcceptance (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : 𝚺₁.Semisentence 1 :=
  familyAcceptanceFor (acceptanceFormula S) (familyEq M h k)

/-- Coordinates `(input,comparison)`; both existential witnesses are internal. -/
noncomputable def membershipFormula (S : ArithmeticTheory) [S.Δ₁] (h : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “u d. ∃ y, !(outputGraph h) u y ∧
    ∃ p, !(nativeEqCheckFormula (canonicalAxiomGraph S)) p y d”

noncomputable def totality (M : 𝚺₁.Semisentence 1) (k : ℕ) : ArithmeticSentence :=
  “∀ u, !M u → ∃ r, !(outputGraph k) u r”

noncomputable def transferBody (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 2 :=
  “u d. !M u → !(membershipFormula S h) u d → !(membershipFormula S k) u d”

/-- Universal closure in `u`, with `d` the remaining free coordinate. -/
noncomputable def transferClosure (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 1 :=
  ∀¹ transferBody S M h k

/-- Coordinates `(d,u,e)`; specializations run in the order `e,u,d`. -/
def pointwiseMatrixFor (A : ArithmeticSemisentence 1) (T : ArithmeticSentence)
    (M : ArithmeticSemisentence 1) (B D : ArithmeticSemisentence 2) :
    ArithmeticSemisentence 3 :=
  “d u e. !A e → !T → !M u → !B u d → !D u d”

noncomputable def pointwiseMatrix (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 3 :=
  pointwiseMatrixFor (familyAcceptance S M h k).val (totality M k) M.val
    (membershipFormula S h).val (membershipFormula S k).val

noncomputable def pointwiseBodyU (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 2 :=
  ∀¹ pointwiseMatrix S M h k

noncomputable def pointwiseBodyE (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 1 :=
  ∀¹ pointwiseBodyU S M h k

noncomputable def pointwiseSchema (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSentence :=
  ∀¹ pointwiseBodyE S M h k

/-- Coordinates `(d,e)`; specializations run in the order `e,d`. -/
def closureMatrixFor (A : ArithmeticSemisentence 1) (T : ArithmeticSentence)
    (C : ArithmeticSemisentence 1) : ArithmeticSemisentence 2 :=
  “d e. !A e → !T → !C d”

noncomputable def closureMatrix (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 2 :=
  closureMatrixFor (familyAcceptance S M h k).val (totality M k) (transferClosure S M h k)

noncomputable def closureBodyE (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSemisentence 1 :=
  ∀¹ closureMatrix S M h k

noncomputable def closureSchema (S : ArithmeticTheory) [S.Δ₁]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : ArithmeticSentence :=
  ∀¹ closureBodyE S M h k

theorem acceptanceFormulaFor_eval {V : Type*} [ORingStructure V]
    (P : 𝚺₁.Semisentence 3) (p c : V) :
    (acceptanceFormulaFor P).val.Evalb ![p, c] ↔ P.val.Evalb ![1, p, c] := by
  simp [acceptanceFormulaFor]

theorem acceptanceFormula_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (p c : V) :
    (acceptanceFormula S).val.Evalb ![p, c] ↔
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb ![1, p, c] :=
  acceptanceFormulaFor_eval _ p c

theorem familyAcceptanceFor_eval {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (A : 𝚺₁.Semisentence 2) (F : ArithmeticSentence) (e : V) :
    (familyAcceptanceFor A F).val.Evalb ![e] ↔ A.val.Evalb ![e, (⌜F⌝ : V)] := by
  simp [familyAcceptanceFor, Sentence.quote_eq_encode, numeral_eq_natCast_app]

theorem familyAcceptance_eval {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e : V) :
    (familyAcceptance S M h k).val.Evalb ![e] ↔
      (nativeProofCheckGraph (canonicalAxiomGraph S)).val.Evalb
        ![1, e, (⌜familyEq M h k⌝ : V)] := by
  exact (familyAcceptanceFor_eval (acceptanceFormula S) (familyEq M h k) e).trans
    (acceptanceFormula_eval S e _)

theorem membershipFormula_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (h : ℕ) (u d : V) :
    (membershipFormula S h).val.Evalb ![u, d] ↔
      ∃ y : V, (outputGraph h).val.Evalb ![u, y] ∧
        ∃ p : V, (nativeEqCheckFormula (canonicalAxiomGraph S)).val.Evalb ![p, y, d] := by
  simp [membershipFormula]

theorem totality_eval {V : Type*} [ORingStructure V]
    (M : 𝚺₁.Semisentence 1) (k : ℕ) :
    V↓[ℒₒᵣ] ⊧ totality M k ↔
      ∀ u : V, M.val.Evalb ![u] → ∃ r : V, (outputGraph k).val.Evalb ![u, r] := by
  simp [totality, models_iff]

theorem transferBody_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (M : 𝚺₁.Semisentence 1) (h k : ℕ) (u d : V) :
    (transferBody S M h k).Evalb ![u, d] ↔
      M.val.Evalb ![u] → (membershipFormula S h).val.Evalb ![u, d] →
        (membershipFormula S k).val.Evalb ![u, d] := by
  simp [transferBody]

theorem transferClosure_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (M : 𝚺₁.Semisentence 1) (h k : ℕ) (d : V) :
    (transferClosure S M h k).Evalb ![d] ↔
      ∀ u : V, (transferBody S M h k).Evalb ![u, d] := by
  simp [transferClosure]

theorem pointwiseMatrix_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u d : V) :
    (pointwiseMatrix S M h k).Evalb ![d, u, e] ↔
      (familyAcceptance S M h k).val.Evalb ![e] → (V↓[ℒₒᵣ] ⊧ totality M k) →
        M.val.Evalb ![u] → (membershipFormula S h).val.Evalb ![u, d] →
          (membershipFormula S k).val.Evalb ![u, d] := by
  simp [pointwiseMatrix, pointwiseMatrixFor, models_iff]

theorem closureMatrix_eval {V : Type*} [ORingStructure V]
    (S : ArithmeticTheory) [S.Δ₁] (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e d : V) :
    (closureMatrix S M h k).Evalb ![d, e] ↔
      (familyAcceptance S M h k).val.Evalb ![e] → (V↓[ℒₒᵣ] ⊧ totality M k) →
        (transferClosure S M h k).Evalb ![d] := by
  simp [closureMatrix, closureMatrixFor, models_iff]

theorem pointwiseMatrix_valid {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e u d : V) :
    (pointwiseMatrix S M h k).Evalb ![d, u, e] := by
  rw [pointwiseMatrix_eval, familyAcceptance_eval, totality_eval]
  intro he ht hm hp
  obtain ⟨y, hh, p, hp⟩ := (membershipFormula_eval S h u d).mp hp
  obtain ⟨r, hk⟩ := ht u hm
  obtain ⟨q, hq⟩ := exists_family_transport S M h k e u y r p d he hm hh hk hp
  exact (membershipFormula_eval S k u d).mpr ⟨r, hk, q, hq⟩

theorem closureMatrix_valid {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) (e d : V) :
    (closureMatrix S M h k).Evalb ![d, e] := by
  rw [closureMatrix_eval]
  intro he ht
  rw [transferClosure_eval]
  intro u
  rw [transferBody_eval]
  exact (pointwiseMatrix_eval S M h k e u d).mp
    (pointwiseMatrix_valid S M h k e u d) he ht

theorem pointwiseSchema_provable (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : 𝗣𝗔 ⊢ pointwiseSchema S M h k := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp only [models_iff, pointwiseSchema, pointwiseBodyE, pointwiseBodyU,
    Semiformula.eval_all]
  intro e u d
  exact pointwiseMatrix_valid S M h k e u d

theorem closureSchema_provable (S : ArithmeticTheory) [S.Δ₁] [𝗣𝗔 ⪯ S]
    (M : 𝚺₁.Semisentence 1) (h k : ℕ) : 𝗣𝗔 ⊢ closureSchema S M h k := by
  apply complete.{0} 𝗣𝗔
  intro V _ _
  simp only [models_iff, closureSchema, closureBodyE, Semiformula.eval_all]
  intro e d
  exact closureMatrix_valid S M h k e d

end FailureOfComposition.NativeMembershipAssembly
