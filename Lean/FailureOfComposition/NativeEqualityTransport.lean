/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeContextSpecialization
import FailureOfComposition.ConcreteEvaluatorGraph
import FailureOfComposition.UniformIndexQuotient
import Foundation.FirstOrder.Arithmetic.Bootstrapping.FixedPoint
import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Coding
import Foundation.Meta.ClProver
import Mathlib.Tactic.FinCases

/-!
# Native proof-code transport for equality of eventual graphs

This module separates four interfaces.  First, it fixes the literal arithmetic
syntax for equality of two evaluator graphs.  Second, it gives a total
primitive-recursive proof-tree constructor with an explicit proof seed.
Third, it proves preservation of Foundation's internal derivation predicate in
every model of PA.  Finally, it relates the native sentence code to the
standard uniform-index quotient.  The executable constructor never searches
for a proof and never uses the production proof checker.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open Arith.FixedFormulaNumeralSubstitution
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NativeEqualityTransport

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.ProofSearch

/-! ## Fixed formulas and their external syntax -/

/-- For a four-place certificate relation with coordinates
`(stage, program, input, output)`, `equalityFormulaFor C` says that two
programs have the same eventual input-output graph. -/
def equalityFormulaFor (C : ArithmeticSemisentence 4) :
    ArithmeticSemisentence 2 :=
  ∀¹ ∀¹ LogicalConnective.iff
    (∃¹ (C/[
      (#0 : ArithmeticSemiterm Empty 5),
      (#3 : ArithmeticSemiterm Empty 5),
      (#2 : ArithmeticSemiterm Empty 5),
      (#1 : ArithmeticSemiterm Empty 5)]))
    (∃¹ (C/[
      (#0 : ArithmeticSemiterm Empty 5),
      (#4 : ArithmeticSemiterm Empty 5),
      (#2 : ArithmeticSemiterm Empty 5),
      (#1 : ArithmeticSemiterm Empty 5)]))

/-- The fixed two-place equality formula for the actual evaluator
certificate. -/
def equalityFormula : ArithmeticSemisentence 2 :=
  equalityFormulaFor evalnCertificateFormula

/-- The open transitivity matrix.  Its de Bruijn coordinate vector is
`(c,r,q)`, so the three enclosing universal binders specialize in the
displayed order `q,r,c`. -/
def thetaMatrixFor (C : ArithmeticSemisentence 4) :
    ArithmeticSemisentence 3 :=
  “c r q. (!(equalityFormulaFor C) q r →
    !(equalityFormulaFor C) q c → !(equalityFormulaFor C) r c)”

def thetaBodyRFor (C : ArithmeticSemisentence 4) :
    ArithmeticSemisentence 2 :=
  ∀¹ thetaMatrixFor C

def thetaBodyQFor (C : ArithmeticSemisentence 4) :
    ArithmeticSemisentence 1 :=
  ∀¹ thetaBodyRFor C

/-- The closed logical transitivity sentence. -/
def thetaFor (C : ArithmeticSemisentence 4) : ArithmeticSentence :=
  ∀¹ thetaBodyQFor C

def thetaMatrix : ArithmeticSemisentence 3 :=
  thetaMatrixFor evalnCertificateFormula

def thetaBodyR : ArithmeticSemisentence 2 :=
  thetaBodyRFor evalnCertificateFormula

def thetaBodyQ : ArithmeticSemisentence 1 :=
  thetaBodyQFor evalnCertificateFormula

def theta : ArithmeticSentence :=
  thetaFor evalnCertificateFormula

theorem theta_eq_all : theta = ∀¹ thetaBodyQ := by
  rfl

theorem thetaBodyQ_eq_all : thetaBodyQ = ∀¹ thetaBodyR := by
  rfl

theorem thetaBodyR_eq_all : thetaBodyR = ∀¹ thetaMatrix := by
  rfl

private def binderRew : Rew ℒₒᵣ Empty 2 Empty 2 :=
  Rew.subst ![
    (#1 : ArithmeticSemiterm Empty 2),
    (#0 : ArithmeticSemiterm Empty 2)]

private def eventualOpen (q : ℕ) : ArithmeticSemisentence 3 :=
  (Rew.subst ![
    (#0 : ArithmeticSemiterm Empty 3),
    (↑q : ArithmeticSemiterm Empty 3),
    (#2 : ArithmeticSemiterm Empty 3),
    (#1 : ArithmeticSemiterm Empty 3)]) ▹
      (evalnCertificateFormula : ArithmeticSemisentence 4)

private def directEquality (q r : ℕ) : ArithmeticSentence :=
  ∀¹ ∀¹ LogicalConnective.iff (∃¹ eventualOpen q) (∃¹ eventualOpen r)

private theorem equalityFormula_subst_eq_direct (q r : ℕ) :
    (equalityFormula/[
      (↑q : ArithmeticSemiterm Empty 0),
      (↑r : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) =
      directEquality q r := by
  have hleft :
      ((Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 0),
        (↑r : ArithmeticSemiterm Empty 0)]).q.q.q).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 5),
            (#3 : ArithmeticSemiterm Empty 5),
            (#2 : ArithmeticSemiterm Empty 5),
            (#1 : ArithmeticSemiterm Empty 5)]) =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 3),
          (↑q : ArithmeticSemiterm Empty 3),
          (#2 : ArithmeticSemiterm Empty 3),
          (#1 : ArithmeticSemiterm Empty 3)] := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  have hright :
      ((Rew.subst ![
        (↑q : ArithmeticSemiterm Empty 0),
        (↑r : ArithmeticSemiterm Empty 0)]).q.q.q).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 5),
            (#4 : ArithmeticSemiterm Empty 5),
            (#2 : ArithmeticSemiterm Empty 5),
            (#1 : ArithmeticSemiterm Empty 5)]) =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 3),
          (↑r : ArithmeticSemiterm Empty 3),
          (#2 : ArithmeticSemiterm Empty 3),
          (#1 : ArithmeticSemiterm Empty 3)] := by
    ext i <;> fin_cases i <;> simp [Rew.comp_app, Rew.q]
  simp only [equalityFormula, equalityFormulaFor, directEquality,
    Rewriting.app_all, LogicalConnective.HomClass.map_iff,
    Rewriting.app_exs]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app]
  rw [hleft, hright]
  rfl

private theorem eventualOpen_eq (q : ℕ) :
    (∃¹ eventualOpen q : ArithmeticSemisentence 2) =
      binderRew ▹ (eventualGraph q).val := by
  have hopen : eventualOpen q = binderRew.q ▹
      ((evalnCertificateFormula : ArithmeticSemisentence 4)/[
        (#0 : ArithmeticSemiterm Empty 3),
        (↑q : ArithmeticSemiterm Empty 3),
        (#1 : ArithmeticSemiterm Empty 3),
        (#2 : ArithmeticSemiterm Empty 3)]) := by
    have hrew :
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 3),
          (↑q : ArithmeticSemiterm Empty 3),
          (#2 : ArithmeticSemiterm Empty 3),
          (#1 : ArithmeticSemiterm Empty 3)] =
        binderRew.q.comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 3),
            (↑q : ArithmeticSemiterm Empty 3),
            (#1 : ArithmeticSemiterm Empty 3),
            (#2 : ArithmeticSemiterm Empty 3)]) := by
      ext i <;> fin_cases i <;> simp [binderRew, Rew.comp_app, Rew.q]
    rw [eventualOpen, hrew, TransitiveRewriting.comp_app]
  calc
    (∃¹ eventualOpen q : ArithmeticSemisentence 2) =
        ∃¹ (binderRew.q ▹
          ((evalnCertificateFormula : ArithmeticSemisentence 4)/[
            (#0 : ArithmeticSemiterm Empty 3),
            (↑q : ArithmeticSemiterm Empty 3),
            (#1 : ArithmeticSemiterm Empty 3),
            (#2 : ArithmeticSemiterm Empty 3)])) := by rw [hopen]
    _ = binderRew ▹ (eventualGraph q).val := by
      rw [eventualGraph_val]
      rfl

private theorem quantifiedIff_congr
    {left₁ left₂ right₁ right₂ : ArithmeticSemisentence 2}
    (hleft : left₁ = left₂) (hright : right₁ = right₂) :
    (∀¹ ∀¹ LogicalConnective.iff left₁ right₁ : ArithmeticSentence) =
      ∀¹ ∀¹ LogicalConnective.iff left₂ right₂ := by
  exact congrArg
    (fun phi : ArithmeticSemisentence 2 =>
      (∀¹ ∀¹ phi : ArithmeticSentence))
    (congrArg₂
      (fun phi psi : ArithmeticSemisentence 2 =>
        LogicalConnective.iff phi psi) hleft hright)

private theorem directEquality_eq (q r : ℕ) :
    directEquality q r =
      uniformSentence (eventualGraph q) (eventualGraph r) := by
  calc
    directEquality q r =
        ∀¹ ∀¹ LogicalConnective.iff
          (∃¹ eventualOpen q) (∃¹ eventualOpen r) := rfl
    _ = ∀¹ ∀¹ LogicalConnective.iff
          (binderRew ▹ (eventualGraph q).val)
          (binderRew ▹ (eventualGraph r).val) :=
      quantifiedIff_congr (eventualOpen_eq q) (eventualOpen_eq r)
    _ = uniformSentence (eventualGraph q) (eventualGraph r) := rfl

/-- Literal equality of the instantiated fixed syntax with the sentence used
by `UniformIndexQuotient.EqIndex`. -/
theorem equalityFormula_instance (q r : ℕ) :
    equalityFormula/[(↑q : ArithmeticSemiterm Empty 0),
      (↑r : ArithmeticSemiterm Empty 0)] =
      uniformSentence (eventualGraph q) (eventualGraph r) :=
  (equalityFormula_subst_eq_direct q r).trans (directEquality_eq q r)

/-! ## Executable syntax codes -/

/-- Actual `Encodable` code of the closed numeral term. -/
def numeralTermCode (q : ℕ) : ℕ :=
  Encodable.encode (↑q : ArithmeticSemiterm Empty 0)

theorem primrec_numeralTermCode : Primrec numeralTermCode := by
  exact Primrec.encode.comp (primrec_arithmeticNumeral 0)

/-- Actual `Encodable` code of `E(q,r)`. -/
def nativeEqCode (q r : ℕ) : ℕ :=
  Encodable.encode
    (equalityFormula/[(↑q : ArithmeticSemiterm Empty 0),
      (↑r : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)

theorem primrec₂_nativeEqCode : Primrec₂ nativeEqCode := by
  exact Primrec.encode.comp
    (primrec₂_arithmeticSemisentenceNumeralSubst equalityFormula)

def thetaBodyQCode : ℕ :=
  Encodable.encode thetaBodyQ

/-- Actual `Encodable` code of the fixed closed transitivity sentence. -/
def thetaCode : ℕ :=
  Encodable.encode theta

def afterQMatrix (q : ℕ) : ArithmeticSemisentence 2 :=
  (Rew.subst ![
    (#0 : ArithmeticSemiterm Empty 2),
    (#1 : ArithmeticSemiterm Empty 2),
    (↑q : ArithmeticSemiterm Empty 2)]) ▹ thetaMatrix

def secondBody (q : ℕ) : ArithmeticSemisentence 1 :=
  ∀¹ afterQMatrix q

def secondBodyCode (q : ℕ) : ℕ :=
  Encodable.encode (secondBody q)

def thirdBody (q r : ℕ) : ArithmeticSemisentence 1 :=
  (Rew.subst ![
    (#0 : ArithmeticSemiterm Empty 1),
    (↑r : ArithmeticSemiterm Empty 1),
    (↑q : ArithmeticSemiterm Empty 1)]) ▹ thetaMatrix

def thirdBodyCode (q r : ℕ) : ℕ :=
  Encodable.encode (thirdBody q r)

theorem primrec_secondBodyCode : Primrec secondBodyCode := by
  exact Primrec.encode.comp <|
    primrec_formulaAll (primrec_lastNumeralPreservingTwo thetaMatrix)

theorem primrec₂_thirdBodyCode : Primrec₂ thirdBodyCode := by
  exact Primrec.encode.comp
    (primrec₂_lastTwoNumeralsPreservingOne thetaMatrix)

/-- The numerical implication constructor used between the two calls to
`mpCtx`.  Its guard is inherited from `formulaNegTotalCode`; on the generated
formula codes it is the ordinary arithmetic implication code. -/
def implicationCode (a b : ℕ) : ℕ :=
  formulaOrCode (formulaNegTotalCode a) b

theorem primrec₂_implicationCode : Primrec₂ implicationCode := by
  exact primrec₂_formulaOrCode.comp
    (primrec_formulaNegTotalCode.comp Primrec.fst) Primrec.snd

/-! ## The executable seven-input transport -/

/-- Starting with a fixed derivation of `Theta`, weaken it into `Gamma`,
specialize the three universal binders at `q,r,c`, and apply context-preserving
modus ponens first to the proof of `E(q,r)` and then to the proof of `E(q,c)`.
The definition is total on all natural-number inputs. -/
def transportCtxWithSeed
    (k Γ e p q r c : ℕ) : ℕ :=
  let nq := numeralTermCode q
  let nr := numeralTermCode r
  let nc := numeralTermCode c
  let st := sequentInsertCode thetaCode Γ
  let kw := wkRuleCode st k
  let d₁ := specializeCtx Γ thetaBodyQCode nq kw
  let d₂ := specializeCtx Γ (secondBodyCode q) nr d₁
  let d₃ := specializeCtx Γ (thirdBodyCode q r) nc d₂
  let aqr := nativeEqCode q r
  let aqc := nativeEqCode q c
  let arc := nativeEqCode r c
  let inner := implicationCode aqc arc
  let m₁ := mpCtx Γ aqr inner d₃ e
  mpCtx Γ aqc arc m₁ p

/-- Left-associated packing `((((((k,Gamma),e),p),q),r),c)`. -/
abbrev TransportCtxWithSeedArgs :=
  ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)

def transportCtxWithSeedPacked (z : TransportCtxWithSeedArgs) : ℕ :=
  transportCtxWithSeed z.1.1.1.1.1.1 z.1.1.1.1.1.2
    z.1.1.1.1.2 z.1.1.1.2 z.1.1.2 z.1.2 z.2

/-- Joint primitive recursiveness in all seven varying inputs, in the stated
left-associated packing. -/
theorem primrec_transportCtxWithSeedPacked :
    Primrec transportCtxWithSeedPacked := by
  let k : TransportCtxWithSeedArgs → ℕ := fun z => z.1.1.1.1.1.1
  let Γ : TransportCtxWithSeedArgs → ℕ := fun z => z.1.1.1.1.1.2
  let e : TransportCtxWithSeedArgs → ℕ := fun z => z.1.1.1.1.2
  let p : TransportCtxWithSeedArgs → ℕ := fun z => z.1.1.1.2
  let q : TransportCtxWithSeedArgs → ℕ := fun z => z.1.1.2
  let r : TransportCtxWithSeedArgs → ℕ := fun z => z.1.2
  let c : TransportCtxWithSeedArgs → ℕ := fun z => z.2
  have hk : Primrec k :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have hΓ : Primrec Γ :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  have he : Primrec e :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))
  have hp : Primrec p :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hq : Primrec q :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec r := Primrec.snd.comp Primrec.fst
  have hc : Primrec c := Primrec.snd
  have hnq := primrec_numeralTermCode.comp hq
  have hnr := primrec_numeralTermCode.comp hr
  have hnc := primrec_numeralTermCode.comp hc
  have hst := primrec₂_sequentInsertCode.comp
    (Primrec.const thetaCode) hΓ
  have hkw := primrec_wkRule hst hk
  have hd₁ := primrec_specializeCtxPacked.comp
    (((hΓ.pair (Primrec.const thetaBodyQCode)).pair hnq).pair hkw)
  have hb₂ := primrec_secondBodyCode.comp hq
  have hd₂ := primrec_specializeCtxPacked.comp
    (((hΓ.pair hb₂).pair hnr).pair hd₁)
  have hb₃ := primrec₂_thirdBodyCode.comp hq hr
  have hd₃ := primrec_specializeCtxPacked.comp
    (((hΓ.pair hb₃).pair hnc).pair hd₂)
  have haqr := primrec₂_nativeEqCode.comp hq hr
  have haqc := primrec₂_nativeEqCode.comp hq hc
  have harc := primrec₂_nativeEqCode.comp hr hc
  have hinner := primrec₂_implicationCode.comp haqc harc
  have hm₁ := primrec_mpCtxPacked.comp
    ((((hΓ.pair haqr).pair hinner).pair hd₃).pair he)
  have hm₂ := primrec_mpCtxPacked.comp
    ((((hΓ.pair haqc).pair harc).pair hm₁).pair hp)
  apply hm₂.of_eq
  intro z
  simp only [transportCtxWithSeedPacked, transportCtxWithSeed,
    mpCtxPacked, specializeCtxPacked, k, Γ, e, p, q, r, c,
    wkRuleCode, Bootstrapping.wkRule, nat_pair_eq]
  rfl

/-- The first specialization removes the outer `q`-binder and leaves the
two remaining universal binders. -/
theorem thetaBodyQ_subst (q : ℕ) :
    (thetaBodyQ/[(↑q : ArithmeticSemiterm Empty 0)] :
      ArithmeticSentence) = ∀¹ secondBody q := by
  have hrew :
      (Rew.subst ![(↑q : ArithmeticSemiterm Empty 0)]).q.q =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 2), #1, ↑q] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.q]
    case hf => exact i.elim
  simp only [thetaBodyQ, thetaBodyQFor, thetaBodyRFor,
    Rewriting.app_all, secondBody, afterQMatrix, thetaMatrix]
  rw [hrew]

/-- The second specialization removes the `r`-binder and leaves the final
universal `c`-binder. -/
theorem secondBody_subst (q r : ℕ) :
    ((secondBody q)/[(↑r : ArithmeticSemiterm Empty 0)] :
      ArithmeticSentence) = ∀¹ thirdBody q r := by
  have hrew :
      (Rew.subst ![(↑r : ArithmeticSemiterm Empty 0)]).q.comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 2), #1, ↑q]) =
        Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 1),
          (↑r : ArithmeticSemiterm Empty 1), ↑q] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.comp_app, Rew.q]
    case hf => exact i.elim
  simp only [secondBody, Rewriting.app_all, afterQMatrix, thirdBody]
  rw [← TransitiveRewriting.comp_app, hrew]

/-- The third specialization is literally the implication consumed by the
two native MP calls. -/
theorem thirdBody_subst (q r c : ℕ) :
    ((thirdBody q r)/[(↑c : ArithmeticSemiterm Empty 0)] :
      ArithmeticSentence) =
      Arrow.arrow
        (equalityFormula/[(↑q : ArithmeticSemiterm Empty 0),
          (↑r : ArithmeticSemiterm Empty 0)])
        (Arrow.arrow
          (equalityFormula/[(↑q : ArithmeticSemiterm Empty 0),
            (↑c : ArithmeticSemiterm Empty 0)])
          (equalityFormula/[(↑r : ArithmeticSemiterm Empty 0),
            (↑c : ArithmeticSemiterm Empty 0)])) := by
  have hrew :
      (Rew.subst ![(↑c : ArithmeticSemiterm Empty 0)]).comp
          (Rew.subst ![
            (#0 : ArithmeticSemiterm Empty 1), ↑r, ↑q]) =
        Rew.subst ![
          (↑c : ArithmeticSemiterm Empty 0), ↑r, ↑q] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.comp_app]
    case hf => exact i.elim
  simp only [thirdBody]
  change (Rew.subst ![(↑c : ArithmeticSemiterm Empty 0)]) ▹
      ((Rew.subst ![
        (#0 : ArithmeticSemiterm Empty 1), ↑r, ↑q]) ▹ thetaMatrix) = _
  rw [← TransitiveRewriting.comp_app, hrew]
  have hqr :
      (Rew.subst ![
        (↑c : ArithmeticSemiterm Empty 0), ↑r, ↑q]).comp
          (Rew.subst ![
            (#2 : ArithmeticSemiterm Empty 3), #1]) =
        Rew.subst ![(↑q : ArithmeticSemiterm Empty 0), ↑r] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.comp_app]
    case hf => exact i.elim
  have hqc :
      (Rew.subst ![
        (↑c : ArithmeticSemiterm Empty 0), ↑r, ↑q]).comp
          (Rew.subst ![
            (#2 : ArithmeticSemiterm Empty 3), #0]) =
        Rew.subst ![(↑q : ArithmeticSemiterm Empty 0), ↑c] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.comp_app]
    case hf => exact i.elim
  have hrc :
      (Rew.subst ![
        (↑c : ArithmeticSemiterm Empty 0), ↑r, ↑q]).comp
          (Rew.subst ![
            (#1 : ArithmeticSemiterm Empty 3), #0]) =
        Rew.subst ![(↑r : ArithmeticSemiterm Empty 0), ↑c] := by
    ext i
    case hb => fin_cases i <;> simp [Rew.comp_app]
    case hf => exact i.elim
  simp only [thetaMatrix, thetaMatrixFor,
    LogicalConnective.HomClass.map_imply]
  rw [← TransitiveRewriting.comp_app, hqr,
    ← TransitiveRewriting.comp_app, hqc,
    ← TransitiveRewriting.comp_app, hrc]
  rfl

/-! ## Logical validity of the fixed seed -/

private theorem eval_equalityFormulaFor
    {M : Type*} [s : Tarski.Structure ℒₒᵣ M]
    (C : ArithmeticSemisentence 4) (q r : M) :
    Semiformula.Eval ![q, r] Empty.elim (equalityFormulaFor C) ↔
      ∀ x y : M,
        ((∃ stage : M,
            Semiformula.Eval ![stage, q, x, y] Empty.elim C) ↔
          ∃ stage : M,
            Semiformula.Eval ![stage, r, x, y] Empty.elim C) := by
  have hleft (stage x y : M) :
      (fun i : Fin 4 => Semiterm.val ![stage, y, x, q, r]
        (Empty.elim : Empty → M)
        (![(#0 : ArithmeticSemiterm Empty 5), #3, #2, #1] i)) =
        ![stage, q, x, y] := by
    funext i
    fin_cases i <;> simp
  have hright (stage x y : M) :
      (fun i : Fin 4 => Semiterm.val ![stage, y, x, q, r]
        (Empty.elim : Empty → M)
        (![(#0 : ArithmeticSemiterm Empty 5), #4, #2, #1] i)) =
        ![stage, r, x, y] := by
    funext i
    fin_cases i <;> simp
  simp [equalityFormulaFor, Semiformula.eval_rew, Function.comp_def,
    hleft, hright]

private theorem thetaMatrixFor_valid
    {M : Type*} [s : Tarski.Structure ℒₒᵣ M]
    (C : ArithmeticSemisentence 4) (q r c : M) :
    Semiformula.Eval ![c, r, q] Empty.elim (thetaMatrixFor C) := by
  simpa [thetaMatrixFor, Semiformula.eval_substs,
    eval_equalityFormulaFor] using
    (fun
      (hqr : ∀ x y : M,
        ((∃ stage : M,
            Semiformula.Eval ![stage, q, x, y] Empty.elim C) ↔
          ∃ stage : M,
            Semiformula.Eval ![stage, r, x, y] Empty.elim C))
      (hqc : ∀ x y : M,
        ((∃ stage : M,
            Semiformula.Eval ![stage, q, x, y] Empty.elim C) ↔
          ∃ stage : M,
            Semiformula.Eval ![stage, c, x, y] Empty.elim C))
      (x y : M) => (hqr x y).symm.trans (hqc x y))

private theorem thetaFor_valid
    {M : Type*} [s : Tarski.Structure ℒₒᵣ M]
    (C : ArithmeticSemisentence 4) :
    Semiformula.Eval (![] : Fin 0 → M) (Empty.elim : Empty → M)
      (thetaFor C : ArithmeticSentence) := by
  simp only [thetaFor, thetaBodyQFor, thetaBodyRFor,
    Semiformula.eval_all]
  intro q r c
  exact thetaMatrixFor_valid C q r c

theorem thetaFor_provable (C : ArithmeticSemisentence 4) :
    𝐋𝐊¹ ⊢ (thetaFor C : FFL.FirstOrder.ArithmeticProposition) := by
  rw [← Theory.Proof.empty_provable_iff_eprovable]
  apply Theory.Proof.small_complete
  intro M _
  exact thetaFor_valid (M := M.Dom) C

theorem theta_provable :
    𝐋𝐊¹ ⊢ (theta : FFL.FirstOrder.ArithmeticProposition) :=
  thetaFor_provable evalnCertificateFormula

/-! ## Model-internal syntax operations and exact graphs -/

def equalityFormulaCode : ℕ :=
  Encodable.encode equalityFormula

private noncomputable def substTwoCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (code : ℕ) (q r : V) : V :=
  substNumerals (k := 2) (ORingStructure.numeral code : V) ![q, r]

private noncomputable def substTwoCodeGraph (code : ℕ) :
    𝚺₁.Semisentence 3 :=
  (ssnums (k := 2)).rew
    (Rew.subst ![(#0 : ArithmeticSemiterm Empty 3),
      (↑code : ArithmeticSemiterm Empty 3), #1, #2])

private theorem substTwoCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (code : ℕ) (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r]
        (substTwoCodeGraph code).val ↔
      y = substTwoCodeValue code q r := by
  simp [substTwoCodeGraph, substTwoCodeValue, Function.comp_def,
    Matrix.empty_eq, Matrix.fun_eq_vec_two,
    Tarski.Structure.numeral_eq_numeral]

/-- Internal substitution of the model's numeral-term codes for `q,r` into
the model quotation of `equalityFormula`. -/
noncomputable def eqValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  substNumerals (k := 2) (⌜equalityFormula⌝ : V) ![q, r]

private theorem eqValue_eq_substTwoCodeValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : V) :
    eqValue q r = substTwoCodeValue equalityFormulaCode q r := by
  simp [eqValue, substTwoCodeValue, equalityFormulaCode,
    Sentence.quote_eq_encode, numeral_eq_natCast_app]

/-- Exact output-first graph of `eqValue`, with coordinates `(y,q,r)`. -/
noncomputable def eqValueGraph : 𝚺₁.Semisentence 3 :=
  substTwoCodeGraph equalityFormulaCode

theorem eqValueGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] eqValueGraph.val ↔
      y = eqValue q r := by
  rw [eqValueGraph, substTwoCodeGraph_iff,
    eqValue_eq_substTwoCodeValue]

theorem eqValueGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q, r]
      eqValueGraph.val :=
  ⟨eqValue q r, (eqValueGraph_iff _ _ _).mpr rfl⟩

theorem eqValueGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q r : V}
    (hy : Semiformula.Evalb (M := V) ![y, q, r] eqValueGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q, r] eqValueGraph.val) :
    y = z :=
  (eqValueGraph_iff y q r).mp hy |>.trans
    ((eqValueGraph_iff z q r).mp hz).symm

private theorem substTwoCodeValue_encode
    (phi : ArithmeticSemisentence 2) (q r : ℕ) :
    substTwoCodeValue (Encodable.encode phi) q r =
      Encodable.encode (phi/[
        (q : ArithmeticSemiterm Empty 0),
        (r : ArithmeticSemiterm Empty 0)]) := by
  rw [substTwoCodeValue, numeral_eq_natCast_app]
  rw [← Sentence.quote_eq_encode_nat phi,
    ← Sentence.quote_eq_encode_nat (phi/[
      (q : ArithmeticSemiterm Empty 0),
      (r : ArithmeticSemiterm Empty 0)])]
  convert (substNumerals_app_quote (V := ℕ) phi ![q, r]) using 1 <;>
    simp [Matrix.fun_eq_vec_two]

/-- Full-domain agreement between the internal operation and executable
native code in the standard model. -/
theorem eqValue_nat (q r : ℕ) :
    eqValue q r = nativeEqCode q r := by
  rw [eqValue_eq_substTwoCodeValue]
  exact substTwoCodeValue_encode equalityFormula q r

theorem eqValueGraph_nat_iff (y q r : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, q, r] eqValueGraph.val ↔
      y = nativeEqCode q r := by
  rw [eqValueGraph_iff, eqValue_nat]

/-- Every pair of model elements produces a well-formed proposition code. -/
theorem eqValue_isFormula
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : V) : IsFormula ℒₒᵣ (eqValue q r) := by
  unfold eqValue substNumerals
  exact (Sentence.quote_isSemiformula equalityFormula).subst
    (by simp [Matrix.vecHead, Matrix.vecTail])

/-! The next fixed templates are the bodies expected by successive calls to
`specializeCtx`.  They retain respectively two and one bound parameters. -/

def thetaMatrixCode : ℕ :=
  Encodable.encode thetaMatrix

private noncomputable def lastNumeralValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (code : ℕ) (q : V) : V :=
  subst ℒₒᵣ
    (^#0 ∷ ^#1 ∷ Arithmetic.numeral q ∷ 0)
    (ORingStructure.numeral code : V)

private noncomputable def lastNumeralGraph (code : ℕ) :
    𝚺₁.Semisentence 2 := .mkSigma
  “y q.
    ∃ b0, !qqBvarDef b0 0 ∧
    ∃ b1, !qqBvarDef b1 1 ∧
    ∃ nq, !numeralGraph nq q ∧
    ∃ vq, !adjoinDef vq nq 0 ∧
    ∃ v1, !adjoinDef v1 b1 vq ∧
    ∃ v, !adjoinDef v b0 v1 ∧
      !(substsGraph ℒₒᵣ) y v ↑code”

private theorem lastNumeralGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (code : ℕ) (y q : V) :
    Semiformula.Evalb (M := V) ![y, q]
        (lastNumeralGraph code).val ↔
      y = lastNumeralValue code q := by
  simp [lastNumeralGraph, lastNumeralValue,
    Tarski.Structure.numeral_eq_numeral]

private noncomputable def lastTwoNumeralsValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (code : ℕ) (q r : V) : V :=
  subst ℒₒᵣ
    (^#0 ∷ Arithmetic.numeral r ∷ Arithmetic.numeral q ∷ 0)
    (ORingStructure.numeral code : V)

private noncomputable def lastTwoNumeralsGraph (code : ℕ) :
    𝚺₁.Semisentence 3 := .mkSigma
  “y q r.
    ∃ b0, !qqBvarDef b0 0 ∧
    ∃ nq, !numeralGraph nq q ∧
    ∃ nr, !numeralGraph nr r ∧
    ∃ vq, !adjoinDef vq nq 0 ∧
    ∃ vr, !adjoinDef vr nr vq ∧
    ∃ v, !adjoinDef v b0 vr ∧
      !(substsGraph ℒₒᵣ) y v ↑code”

private theorem lastTwoNumeralsGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (code : ℕ) (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r]
        (lastTwoNumeralsGraph code).val ↔
      y = lastTwoNumeralsValue code q r := by
  simp [lastTwoNumeralsGraph, lastTwoNumeralsValue,
    Tarski.Structure.numeral_eq_numeral]

noncomputable def afterQMatrixValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q : V) : V :=
  subst ℒₒᵣ
    (^#0 ∷ ^#1 ∷ Arithmetic.numeral q ∷ 0)
    (⌜thetaMatrix⌝ : V)

noncomputable def afterQMatrixGraph : 𝚺₁.Semisentence 2 :=
  lastNumeralGraph thetaMatrixCode

theorem afterQMatrixGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q : V) :
    Semiformula.Evalb (M := V) ![y, q] afterQMatrixGraph.val ↔
      y = afterQMatrixValue q := by
  rw [afterQMatrixGraph, lastNumeralGraph_iff]
  change y = subst ℒₒᵣ
      (^#0 ∷ ^#1 ∷ Arithmetic.numeral q ∷ 0)
      (ORingStructure.numeral thetaMatrixCode : V) ↔
    y = afterQMatrixValue q
  rw [afterQMatrixValue, thetaMatrixCode,
    numeral_eq_natCast_app, Sentence.quote_eq_encode]

noncomputable def numeralTermCodeGraph : 𝚺₁.Semisentence 2 :=
  Arithmetic.numeralGraph

theorem numeralTermCodeGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q : V) :
    Semiformula.Evalb (M := V) ![y, q] numeralTermCodeGraph.val ↔
      y = Arithmetic.numeral q := by
  simp [numeralTermCodeGraph, Arithmetic.numeral_defined.df]

theorem numeralTermCodeGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, q]
      numeralTermCodeGraph.val :=
  ⟨Arithmetic.numeral q, (numeralTermCodeGraph_iff _ _).mpr rfl⟩

theorem numeralTermCodeGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z q : V}
    (hy : Semiformula.Evalb (M := V) ![y, q]
      numeralTermCodeGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, q]
      numeralTermCodeGraph.val) : y = z :=
  (numeralTermCodeGraph_iff y q).mp hy |>.trans
    ((numeralTermCodeGraph_iff z q).mp hz).symm

theorem numeralTermCodeValue_nat (q : ℕ) :
    Arithmetic.numeral q = numeralTermCode q := by
  have htyped :=
    Semiterm.empty_typed_quote_numeral_eq_numeral
      (V := ℕ) (n := 0) q
  calc
    Arithmetic.numeral q =
        (Bootstrapping.Arithmetic.typedNumeral q :
          Bootstrapping.Semiterm ℕ ℒₒᵣ 0).val := rfl
    _ = (⌜(↑q : ArithmeticSemiterm Empty 0)⌝ :
        Bootstrapping.Semiterm ℕ ℒₒᵣ 0).val := by
      simp at htyped ⊢
    _ = (⌜(↑q : ArithmeticSemiterm Empty 0)⌝ : ℕ) := rfl
    _ = numeralTermCode q := by
      simpa [numeralTermCode] using
        (Semiterm.empty_quote_eq_encode (V := ℕ)
          (↑q : ArithmeticSemiterm Empty 0))

theorem numeralTermCodeGraph_nat_iff (y q : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, q] numeralTermCodeGraph.val ↔
      y = numeralTermCode q := by
  rw [numeralTermCodeGraph_iff, numeralTermCodeValue_nat]

noncomputable def secondBodyValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q : V) : V :=
  ^∀ (afterQMatrixValue q)

noncomputable def secondBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y q. ∃ m, !afterQMatrixGraph m q ∧ !qqAllDef y m”

theorem secondBodyGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q : V) :
    Semiformula.Evalb (M := V) ![y, q] secondBodyGraph.val ↔
      y = secondBodyValue q := by
  simp [secondBodyGraph, secondBodyValue, afterQMatrixGraph_iff]

noncomputable def thirdBodyValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (q r : V) : V :=
  subst ℒₒᵣ
    (^#0 ∷ Arithmetic.numeral r ∷ Arithmetic.numeral q ∷ 0)
    (⌜thetaMatrix⌝ : V)

noncomputable def thirdBodyGraph : 𝚺₁.Semisentence 3 :=
  lastTwoNumeralsGraph thetaMatrixCode

theorem thirdBodyGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y q r : V) :
    Semiformula.Evalb (M := V) ![y, q, r] thirdBodyGraph.val ↔
      y = thirdBodyValue q r := by
  rw [thirdBodyGraph, lastTwoNumeralsGraph_iff]
  change y = subst ℒₒᵣ
      (^#0 ∷ Arithmetic.numeral r ∷ Arithmetic.numeral q ∷ 0)
      (ORingStructure.numeral thetaMatrixCode : V) ↔
    y = thirdBodyValue q r
  rw [thirdBodyValue, thetaMatrixCode,
    numeral_eq_natCast_app, Sentence.quote_eq_encode]

private theorem qqAll_encode (phi : ArithmeticSemisentence 2) :
    (^∀ (Encodable.encode phi : ℕ)) =
      Encodable.encode (∀¹ phi : ArithmeticSemisentence 1) := by
  simp [Bootstrapping.qqAll, Semiformula.encode_eq_toNat,
    Semiformula.toNat, nat_pair_eq]

private theorem lastNumeralValue_encode
    (phi : ArithmeticSemisentence 3) (q : ℕ) :
    lastNumeralValue (Encodable.encode phi) q =
      Encodable.encode
        ((Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 2), #1, ↑q]) ▹ phi) := by
  rw [lastNumeralValue, numeral_eq_natCast_app]
  rw [← Sentence.quote_eq_encode_nat phi,
    ← Sentence.quote_eq_encode_nat]
  simp [Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb, Matrix.vecHead, Matrix.vecTail]

private theorem lastTwoNumeralsValue_encode
    (phi : ArithmeticSemisentence 3) (q r : ℕ) :
    lastTwoNumeralsValue (Encodable.encode phi) q r =
      Encodable.encode
        ((Rew.subst ![
          (#0 : ArithmeticSemiterm Empty 1), ↑r, ↑q]) ▹ phi) := by
  rw [lastTwoNumeralsValue, numeral_eq_natCast_app]
  rw [← Sentence.quote_eq_encode_nat phi,
    ← Sentence.quote_eq_encode_nat]
  simp [Sentence.quote_def, Semiformula.quote_def,
    Rewriting.emb_subst_eq_subst_emb, Matrix.vecHead, Matrix.vecTail]

theorem afterQMatrixValue_nat (q : ℕ) :
    afterQMatrixValue q = Encodable.encode (afterQMatrix q) := by
  calc
    afterQMatrixValue q =
        lastNumeralValue (Encodable.encode thetaMatrix) q := by
      simp [afterQMatrixValue, lastNumeralValue,
        Sentence.quote_eq_encode, numeral_eq_natCast_app]
    _ = Encodable.encode (afterQMatrix q) := by
      simpa only [afterQMatrix] using
        lastNumeralValue_encode thetaMatrix q

theorem secondBodyValue_nat (q : ℕ) :
    secondBodyValue q = secondBodyCode q := by
  rw [secondBodyValue, afterQMatrixValue_nat]
  exact qqAll_encode (afterQMatrix q)

theorem thirdBodyValue_nat (q r : ℕ) :
    thirdBodyValue q r = thirdBodyCode q r := by
  calc
    thirdBodyValue q r =
        lastTwoNumeralsValue (Encodable.encode thetaMatrix) q r := by
      simp [thirdBodyValue, lastTwoNumeralsValue,
        Sentence.quote_eq_encode, numeral_eq_natCast_app]
    _ = thirdBodyCode q r := by
      simpa only [thirdBodyCode, thirdBody] using
        lastTwoNumeralsValue_encode thetaMatrix q r

/-! ## Exact internal specialization identities -/

/-- Internal specialization of the outer `q`-binder, for an arbitrary
element of a PA model. -/
theorem thetaBodyQ_substs_internal
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : V) :
    substs1 ℒₒᵣ (Arithmetic.numeral q) (⌜thetaBodyQ⌝ : V) =
      ^∀ (secondBodyValue q) := by
  simp only [substs1, thetaBodyQ, thetaBodyQFor, thetaBodyRFor,
    Sentence.quote_def, Rewriting.app_all, Nat.reduceAdd, Rew.q_emb,
    Semiformula.quote_def, LCWQIsoGödelQuote.all, Semiformula.val_all,
    IsUFormula.all, Semiformula.isUFormula, substs_all, qVec, len_adjoin,
    len_nil, zero_add, numeral_uterm, termBShiftVec_cons₁, numeral_bShift,
    secondBodyValue, afterQMatrixValue, qqAll_inj]
  have hb0 : IsUTerm (V := V) ℒₒᵣ ^#0 := by simp
  have hnq : IsUTerm (V := V) ℒₒᵣ (Arithmetic.numeral q) := by simp
  rw [one_add_one_eq_two, termBShiftVec_cons₂ hb0 hnq]
  simp
  congr 2

/-- Internal specialization of the middle `r`-binder, retaining the final
universal binder. -/
theorem secondBody_substs_internal
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r : V) :
    substs1 ℒₒᵣ (Arithmetic.numeral r) (secondBodyValue q) =
      ^∀ (thirdBodyValue q r) := by
  let v : Bootstrapping.SemitermVec V ℒₒᵣ 3 2 := ![
    Bootstrapping.Semiterm.bvar 0,
    Bootstrapping.Semiterm.bvar 1,
    Arithmetic.typedNumeral q]
  let w : Bootstrapping.SemitermVec V ℒₒᵣ 2 1 := ![
    Bootstrapping.Semiterm.bvar 0,
    Arithmetic.typedNumeral r]
  let u : Bootstrapping.SemitermVec V ℒₒᵣ 3 1 := ![
    Bootstrapping.Semiterm.bvar 0,
    Arithmetic.typedNumeral r,
    Arithmetic.typedNumeral q]
  have hv : IsSemitermVec (V := V) ℒₒᵣ 3 2
      (^#0 ∷ ^#1 ∷ Arithmetic.numeral q ∷ 0) := by
    simpa [v] using v.isSemitermVec
  have hw : IsSemitermVec (V := V) ℒₒᵣ 2 1
      (^#0 ∷ Arithmetic.numeral r ∷ 0) := by
    simp
  have hafter : IsSemiformula ℒₒᵣ 2 (afterQMatrixValue q) := by
    exact (Sentence.quote_isSemiformula thetaMatrix).subst hv
  rw [substs1, secondBodyValue, substs_all hafter.isUFormula]
  congr 1
  have hnr : IsUTerm (V := V) ℒₒᵣ (Arithmetic.numeral r) := by simp
  have hqvec : qVec ℒₒᵣ (Arithmetic.numeral r ∷ 0) =
      ((^#0 : V) ∷ Arithmetic.numeral r ∷ (0 : V)) := by
    simp only [qVec]
    rw [show len (Arithmetic.numeral r ∷ (0 : V)) = (1 : V) by simp,
      termBShiftVec_cons₁ hnr]
    simp
  rw [hqvec, afterQMatrixValue, thirdBodyValue,
    substs_substs (Sentence.quote_isSemiformula thetaMatrix) hw hv]
  have htyped : (Semiterm.subst w)⨟ v = u := by
    funext i
    fin_cases i <;> simp [v, w, u]
  have hcomp : termSubstVec ℒₒᵣ (↑(3 : ℕ) : V)
      ((^#0 : V) ∷ Arithmetic.numeral r ∷ (0 : V))
      ((^#0 : V) ∷ ^#1 ∷ Arithmetic.numeral q ∷ (0 : V)) =
      ((^#0 : V) ∷ Arithmetic.numeral r ∷
        Arithmetic.numeral q ∷ (0 : V)) := by
    have hval := congrArg Bootstrapping.SemitermVec.val htyped
    rw [Bootstrapping.SemitermVec.val_substs] at hval
    dsimp [v, w, u] at hval
    convert hval using 1 <;>
      simp [Bootstrapping.SemitermVec.val_succ,
        Bootstrapping.SemitermVec.val_nil, Matrix.vecHead,
        Matrix.vecTail]
  rw [hcomp]

private theorem subst_equalityFormula_coordinates
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (w : Bootstrapping.SemitermVec V ℒₒᵣ 3 0)
    (i j : Fin 3) (a b : V)
    (hi : (w i).val = Arithmetic.numeral a)
    (hj : (w j).val = Arithmetic.numeral b) :
    subst ℒₒᵣ w.val
        (⌜(equalityFormula/[
          (#i : ArithmeticSemiterm Empty 3), #j] :
          ArithmeticSemisentence 3)⌝ : V) =
      eqValue a b := by
  have hquote :
      (⌜(equalityFormula/[
        (#i : ArithmeticSemiterm Empty 3), #j] :
        ArithmeticSemisentence 3)⌝ : V) =
        subst ℒₒᵣ (qqBvar ((i : ℕ) : V) ∷
          qqBvar ((j : ℕ) : V) ∷ (0 : V))
          (⌜equalityFormula⌝ : V) := by
    simp [Sentence.quote_def, Semiformula.quote_def,
      Rewriting.emb_subst_eq_subst_emb, Matrix.vecHead,
      Matrix.vecTail]
  have heq : eqValue a b =
      subst ℒₒᵣ
        (Arithmetic.numeral a ∷ Arithmetic.numeral b ∷ (0 : V))
        (⌜equalityFormula⌝ : V) := by
    simp [eqValue, substNumerals, Matrix.fun_eq_vec_two,
      Matrix.vecHead, Matrix.vecTail]
  let inner : Bootstrapping.SemitermVec V ℒₒᵣ 2 3 := ![
    Bootstrapping.Semiterm.bvar i,
    Bootstrapping.Semiterm.bvar j]
  let result : Bootstrapping.SemitermVec V ℒₒᵣ 2 0 := ![
    Arithmetic.typedNumeral a,
    Arithmetic.typedNumeral b]
  have hinner : IsSemitermVec (V := V) ℒₒᵣ 2 3
      (qqBvar ((i : ℕ) : V) ∷ qqBvar ((j : ℕ) : V) ∷
        (0 : V)) := by
    simp
  rw [hquote, heq,
    substs_substs (Sentence.quote_isSemiformula equalityFormula)
      w.isSemitermVec hinner]
  have htyped : (Semiterm.subst w)⨟ inner = result := by
    funext k
    fin_cases k
    · apply Bootstrapping.Semiterm.ext
      simpa [inner, result] using hi
    · apply Bootstrapping.Semiterm.ext
      simpa [inner, result] using hj
  have hcoords : termSubstVec ℒₒᵣ (↑(2 : ℕ) : V) w.val
      (qqBvar ((i : ℕ) : V) ∷ qqBvar ((j : ℕ) : V) ∷
        (0 : V)) =
      (Arithmetic.numeral a ∷ Arithmetic.numeral b ∷ (0 : V)) := by
    have hval := congrArg Bootstrapping.SemitermVec.val htyped
    rw [Bootstrapping.SemitermVec.val_substs] at hval
    dsimp [inner, result] at hval
    convert hval using 1 <;>
      simp [Bootstrapping.SemitermVec.val_succ,
        Bootstrapping.SemitermVec.val_nil, Matrix.vecHead,
        Matrix.vecTail]
  rw [hcoords]

/-- The final internal specialization is literally the nested implication
used by the two internal MP constructors. -/
theorem thirdBody_substs_internal
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q r c : V) :
    substs1 ℒₒᵣ (Arithmetic.numeral c) (thirdBodyValue q r) =
      imp ℒₒᵣ (eqValue q r)
        (imp ℒₒᵣ (eqValue q c) (eqValue r c)) := by
  let v : Bootstrapping.SemitermVec V ℒₒᵣ 3 1 := ![
    Bootstrapping.Semiterm.bvar 0,
    Arithmetic.typedNumeral r,
    Arithmetic.typedNumeral q]
  let w : Bootstrapping.SemitermVec V ℒₒᵣ 1 0 := ![
    Arithmetic.typedNumeral c]
  let u : Bootstrapping.SemitermVec V ℒₒᵣ 3 0 := ![
    Arithmetic.typedNumeral c,
    Arithmetic.typedNumeral r,
    Arithmetic.typedNumeral q]
  have hv : IsSemitermVec (V := V) ℒₒᵣ 3 1
      ((^#0 : V) ∷ Arithmetic.numeral r ∷
        Arithmetic.numeral q ∷ (0 : V)) := by
    simpa [v] using v.isSemitermVec
  have hw : IsSemitermVec (V := V) ℒₒᵣ 1 0
      (Arithmetic.numeral c ∷ (0 : V)) := by
    simp
  have htyped : (Semiterm.subst w)⨟ v = u := by
    funext i
    fin_cases i <;> simp [v, w, u]
  have hcomp : termSubstVec ℒₒᵣ (↑(3 : ℕ) : V)
      (Arithmetic.numeral c ∷ (0 : V))
      ((^#0 : V) ∷ Arithmetic.numeral r ∷
        Arithmetic.numeral q ∷ (0 : V)) =
      (Arithmetic.numeral c ∷ Arithmetic.numeral r ∷
        Arithmetic.numeral q ∷ (0 : V)) := by
    have hval := congrArg Bootstrapping.SemitermVec.val htyped
    rw [Bootstrapping.SemitermVec.val_substs] at hval
    dsimp [v, w, u] at hval
    convert hval using 1 <;>
      simp [Bootstrapping.SemitermVec.val_succ,
        Bootstrapping.SemitermVec.val_nil, Matrix.vecHead,
        Matrix.vecTail]
  let A : V :=
    (⌜(equalityFormula/[
      (#2 : ArithmeticSemiterm Empty 3), #1] :
      ArithmeticSemisentence 3)⌝ : V)
  let B : V :=
    (⌜(equalityFormula/[
      (#2 : ArithmeticSemiterm Empty 3), #0] :
      ArithmeticSemisentence 3)⌝ : V)
  let C : V :=
    (⌜(equalityFormula/[
      (#1 : ArithmeticSemiterm Empty 3), #0] :
      ArithmeticSemisentence 3)⌝ : V)
  have hA : IsSemiformula ℒₒᵣ 3 A := by
    simpa [A] using Sentence.quote_isSemiformula
      (equalityFormula/[
        (#2 : ArithmeticSemiterm Empty 3), #1] :
        ArithmeticSemisentence 3)
  have hB : IsSemiformula ℒₒᵣ 3 B := by
    simpa [B] using Sentence.quote_isSemiformula
      (equalityFormula/[
        (#2 : ArithmeticSemiterm Empty 3), #0] :
        ArithmeticSemisentence 3)
  have hC : IsSemiformula ℒₒᵣ 3 C := by
    simpa [C] using Sentence.quote_isSemiformula
      (equalityFormula/[
        (#1 : ArithmeticSemiterm Empty 3), #0] :
        ArithmeticSemisentence 3)
  have htheta : (⌜thetaMatrix⌝ : V) =
      imp ℒₒᵣ A (imp ℒₒᵣ B C) := by
    simp [A, B, C, thetaMatrix, thetaMatrixFor,
      equalityFormula, Sentence.quote_def, Semiformula.quote_def]
  rw [substs1, thirdBodyValue,
    substs_substs (Sentence.quote_isSemiformula thetaMatrix) hw hv,
    hcomp, htheta]
  have hsubstImp (p s : V)
      (hp : IsSemiformula ℒₒᵣ 3 p)
      (hs : IsSemiformula ℒₒᵣ 3 s) :
      subst ℒₒᵣ u.val (imp ℒₒᵣ p s) =
        imp ℒₒᵣ (subst ℒₒᵣ u.val p) (subst ℒₒᵣ u.val s) := by
    simp only [imp]
    rw [substs_or hp.neg.isUFormula hs.isUFormula,
      substs_neg hp u.isSemitermVec]
  change subst ℒₒᵣ u.val (imp ℒₒᵣ A (imp ℒₒᵣ B C)) = _
  rw [hsubstImp A (imp ℒₒᵣ B C) hA
      (IsSemiformula.imp.mpr ⟨hB, hC⟩),
    hsubstImp B C hB hC]
  have hqr : subst ℒₒᵣ u.val A = eqValue q r := by
    simpa [A] using subst_equalityFormula_coordinates u 2 1 q r
      (by simp [u]) (by simp [u])
  have hqc : subst ℒₒᵣ u.val B = eqValue q c := by
    simpa [B] using subst_equalityFormula_coordinates u 2 0 q c
      (by simp [u]) (by simp [u])
  have hrc : subst ℒₒᵣ u.val C = eqValue r c := by
    simpa [C] using subst_equalityFormula_coordinates u 1 0 r c
      (by simp [u]) (by simp [u])
  rw [hqr, hqc, hrc]

/-! ## Internal transport and its exact eight-coordinate graph -/

theorem thetaCode_numeral_eq_quote
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1] :
    (ORingStructure.numeral thetaCode : V) = (⌜theta⌝ : V) := by
  rw [thetaCode, numeral_eq_natCast_app, Sentence.quote_eq_encode]

theorem thetaBodyQCode_numeral_eq_quote
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* ISigma 1] :
    (ORingStructure.numeral thetaBodyQCode : V) =
      (⌜thetaBodyQ⌝ : V) := by
  rw [thetaBodyQCode, numeral_eq_natCast_app,
    Sentence.quote_eq_encode]

/-- Model-internal counterpart of `transportCtxWithSeed`.  Its arguments,
all intermediate syntax codes, and its output are elements of one arbitrary
model of PA. -/
noncomputable def transportValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (k Γ e p q r c : V) : V :=
  let nq := Arithmetic.numeral q
  let nr := Arithmetic.numeral r
  let nc := Arithmetic.numeral c
  let st := insert (⌜theta⌝ : V) Γ
  let kw := wkRule st k
  let d₁ := specializeCtxValue Γ (⌜thetaBodyQ⌝ : V) nq kw
  let d₂ := specializeCtxValue Γ (secondBodyValue q) nr d₁
  let d₃ := specializeCtxValue Γ (thirdBodyValue q r) nc d₂
  let aqr := eqValue q r
  let aqc := eqValue q c
  let arc := eqValue r c
  let inner := imp ℒₒᵣ aqc arc
  let m₁ := mpCtxValue Γ aqr inner d₃ e
  mpCtxValue Γ aqc arc m₁ p

/-- A controlled one-step unfolding of the internal transport. -/
theorem transportValue_eq
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (k Γ e p q r c : V) :
    transportValue k Γ e p q r c =
      mpCtxValue Γ (eqValue q c) (eqValue r c)
        (mpCtxValue Γ (eqValue q r)
          (imp ℒₒᵣ (eqValue q c) (eqValue r c))
          (specializeCtxValue Γ (thirdBodyValue q r)
            (Arithmetic.numeral c)
            (specializeCtxValue Γ (secondBodyValue q)
              (Arithmetic.numeral r)
              (specializeCtxValue Γ (⌜thetaBodyQ⌝ : V)
                (Arithmetic.numeral q)
                (wkRule (insert (⌜theta⌝ : V) Γ) k))))
          e)
        p := by
  rfl

private theorem specializeCtxGraph_eval_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (v : Fin 5 → V) :
    Semiformula.Evalb (M := V) v specializeCtxGraph.val ↔
      v 0 = specializeCtxValue (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact specializeCtxGraph_iff _ _ _ _ _

private theorem mpCtxGraph_eval_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (v : Fin 6 → V) :
    Semiformula.Evalb (M := V) v mpCtxGraph.val ↔
      v 0 = mpCtxValue (v 1) (v 2) (v 3) (v 4) (v 5) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4, v 5] = v := by
    funext i
    fin_cases i <;> simp
  rw [← hv]
  exact mpCtxGraph_iff _ _ _ _ _ _

private noncomputable def transportValueFor
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (thetaNumber bodyNumber : ℕ)
    (k Γ e p q r c : V) : V :=
  let nq := Arithmetic.numeral q
  let nr := Arithmetic.numeral r
  let nc := Arithmetic.numeral c
  let st := insert (ORingStructure.numeral thetaNumber : V) Γ
  let kw := wkRule st k
  let d₁ := specializeCtxValue Γ
    (ORingStructure.numeral bodyNumber : V) nq kw
  let d₂ := specializeCtxValue Γ (secondBodyValue q) nr d₁
  let d₃ := specializeCtxValue Γ (thirdBodyValue q r) nc d₂
  let aqr := eqValue q r
  let aqc := eqValue q c
  let arc := eqValue r c
  let inner := imp ℒₒᵣ aqc arc
  let m₁ := mpCtxValue Γ aqr inner d₃ e
  mpCtxValue Γ aqc arc m₁ p

private theorem transportValueFor_fixed
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (k Γ e p q r c : V) :
    transportValueFor thetaCode thetaBodyQCode k Γ e p q r c =
      transportValue k Γ e p q r c := by
  rw [transportValueFor, transportValue,
    thetaCode_numeral_eq_quote,
    thetaBodyQCode_numeral_eq_quote]

/-- Exact output-first graph of `transportValue`, in coordinate order
`(output,k,Gamma,e,p,q,r,c)`. -/
private noncomputable def transportGraphFor
    (thetaNumber bodyNumber : ℕ) :
    HierarchySymbol.sigmaOne.Semisentence 8 := .mkSigma
  “y k Γ e p q r c.
    ∃ nq, !numeralTermCodeGraph nq q ∧
    ∃ nr, !numeralTermCodeGraph nr r ∧
    ∃ nc, !numeralTermCodeGraph nc c ∧
    ∃ bq, !secondBodyGraph bq q ∧
    ∃ br, !thirdBodyGraph br q r ∧
    ∃ aqr, !eqValueGraph aqr q r ∧
    ∃ aqc, !eqValueGraph aqc q c ∧
    ∃ arc, !eqValueGraph arc r c ∧
    ∃ inner, !(impGraph ℒₒᵣ) inner aqc arc ∧
    ∃ st, !insertDef st ↑thetaNumber Γ ∧
    ∃ kw, !wkRuleGraph kw st k ∧
    ∃ d1, !specializeCtxGraph d1 Γ ↑bodyNumber nq kw ∧
    ∃ d2, !specializeCtxGraph d2 Γ bq nr d1 ∧
    ∃ d3, !specializeCtxGraph d3 Γ br nc d2 ∧
    ∃ m1, !mpCtxGraph m1 Γ aqr inner d3 e ∧
      !mpCtxGraph y Γ aqc arc m1 p”

private theorem transportGraphFor_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (thetaNumber bodyNumber : ℕ) (y k Γ e p q r c : V) :
    Semiformula.Evalb (M := V) ![y, k, Γ, e, p, q, r, c]
        (transportGraphFor thetaNumber bodyNumber).val ↔
      y = transportValueFor thetaNumber bodyNumber
        k Γ e p q r c := by
  simp [transportGraphFor, transportValueFor,
    numeralTermCodeGraph_iff, secondBodyGraph_iff,
    thirdBodyGraph_iff, eqValueGraph_iff,
    specializeCtxGraph_eval_iff,
    mpCtxGraph_eval_iff,
    Tarski.Structure.numeral_eq_numeral]

noncomputable def transportGraph :
    HierarchySymbol.sigmaOne.Semisentence 8 :=
  transportGraphFor thetaCode thetaBodyQCode

theorem transportGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (y k Γ e p q r c : V) :
    Semiformula.Evalb (M := V) ![y, k, Γ, e, p, q, r, c]
        transportGraph.val ↔
      y = transportValue k Γ e p q r c := by
  rw [transportGraph, transportGraphFor_iff,
    transportValueFor_fixed]

theorem transportGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (k Γ e p q r c : V) :
    ∃ y : V, Semiformula.Evalb (M := V)
      ![y, k, Γ, e, p, q, r, c] transportGraph.val :=
  ⟨transportValue k Γ e p q r c,
    (transportGraph_iff _ _ _ _ _ _ _ _).mpr rfl⟩

theorem transportGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    {y z k Γ e p q r c : V}
    (hy : Semiformula.Evalb (M := V)
      ![y, k, Γ, e, p, q, r, c] transportGraph.val)
    (hz : Semiformula.Evalb (M := V)
      ![z, k, Γ, e, p, q, r, c] transportGraph.val) :
    y = z :=
  (transportGraph_iff y k Γ e p q r c).mp hy |>.trans
    ((transportGraph_iff z k Γ e p q r c).mp hz).symm

/-! ## Entire-domain agreement with the numerical transport -/

private theorem syntaxImp_nat_eq_implicationCode
    {a b : ℕ} (ha : IsFormula ℒₒᵣ a) :
    imp ℒₒᵣ a b = implicationCode a b := by
  rw [implicationCode, formulaNegTotalCode_eq_neg ha]
  simp [imp, formulaOrCode, Bootstrapping.qqOr, nat_pair_eq]

private theorem insert_nat_eq_sequentInsertCode (x s : ℕ) :
    insert x s = sequentInsertCode x s := by
  simp [sequentInsertCode, nat_insert_eq]

private theorem wkRule_nat_eq_wkRuleCode (s d : ℕ) :
    wkRule s d = wkRuleCode s d := by
  simp [wkRuleCode, Bootstrapping.wkRule, nat_pair_eq]

/-- In the standard model, the internal structural operation agrees on every
seven-tuple with the total executable constructor. -/
theorem transportValue_nat (k Γ e p q r c : ℕ) :
    transportValue k Γ e p q r c =
      transportCtxWithSeed k Γ e p q r c := by
  rw [← transportValueFor_fixed]
  have hqc : IsFormula ℒₒᵣ (nativeEqCode q c) := by
    rw [← eqValue_nat]
    exact eqValue_isFormula q c
  simp only [transportValueFor, transportCtxWithSeed,
    numeralTermCodeValue_nat, secondBodyValue_nat,
    thirdBodyValue_nat, eqValue_nat,
    syntaxImp_nat_eq_implicationCode hqc,
    specializeCtxValue_nat, mpCtxValue_nat,
    numeral_eq_natCast_app,
    insert_nat_eq_sequentInsertCode,
    wkRule_nat_eq_wkRuleCode]
  simp

/-- Standard-model characterization of the exact graph on every tuple,
without syntax or proof-validity premises. -/
theorem transportGraph_nat_iff (y k Γ e p q r c : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, k, Γ, e, p, q, r, c]
        transportGraph.val ↔
      y = transportCtxWithSeed k Γ e p q r c := by
  rw [transportGraph_iff, transportValue_nat]

/-! ## Preservation of the internal derivation predicate -/

/-- The internal transport preserves the exact Foundation derivation
predicate.  The seed derives the fixed logical sentence in the empty
context; the constructor first weakens it into `Gamma`. -/
theorem derivationOf_transportValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (S : ArithmeticTheory) [S.Δ₁]
    {k Γ e p q r c : V}
    (hk : DerivationOf S k (insert (⌜theta⌝ : V) 0))
    (he : DerivationOf S e (insert (eqValue q r) Γ))
    (hp : DerivationOf S p (insert (eqValue q c) Γ)) :
    DerivationOf S (transportValue k Γ e p q r c)
      (insert (eqValue r c) Γ) := by
  have hΓ : IsFormulaSet ℒₒᵣ Γ :=
    (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  have htheta : IsFormula ℒₒᵣ (⌜theta⌝ : V) := by
    simp
  have hthetaQuote : (⌜theta⌝ : V) = ^∀ (⌜thetaBodyQ⌝ : V) := by
    simp [theta_eq_all, Sentence.quote_def, Semiformula.quote_def]
  let nq := Arithmetic.numeral q
  let nr := Arithmetic.numeral r
  let nc := Arithmetic.numeral c
  let st := insert (⌜theta⌝ : V) Γ
  let kw := wkRule st k
  let d₁ := specializeCtxValue Γ (⌜thetaBodyQ⌝ : V) nq kw
  let d₂ := specializeCtxValue Γ (secondBodyValue q) nr d₁
  let d₃ := specializeCtxValue Γ (thirdBodyValue q r) nc d₂
  let aqr := eqValue q r
  let aqc := eqValue q c
  let arc := eqValue r c
  let inner := imp ℒₒᵣ aqc arc
  let m₁ := mpCtxValue Γ aqr inner d₃ e
  have hst : IsFormulaSet ℒₒᵣ st := by
    simp [st, htheta, hΓ]
  have hkw : DerivationOf S kw st := by
    refine ⟨by simp [kw], Derivation.wkRule hst ?_ hk⟩
    intro a ha
    rcases (by simpa using ha : a = (⌜theta⌝ : V) ∨ a ∈ (0 : V)) with
      (rfl | ha)
    · simp [st]
    · simp at ha
  have hkw' : DerivationOf S kw
      (insert (^∀ (⌜thetaBodyQ⌝ : V)) Γ) := by
    simpa [st, hthetaQuote] using hkw
  have hd₁ : DerivationOf S d₁
      (insert (^∀ (secondBodyValue q)) Γ) := by
    have h := derivationOf_specializeCtxValue S
      (t := nq) (by simp [nq]) hkw'
    simpa [d₁, nq, thetaBodyQ_substs_internal] using h
  have hd₂ : DerivationOf S d₂
      (insert (^∀ (thirdBodyValue q r)) Γ) := by
    have h := derivationOf_specializeCtxValue S
      (t := nr) (by simp [nr]) hd₁
    simpa [d₂, nr, secondBody_substs_internal] using h
  have hd₃ : DerivationOf S d₃
      (insert (imp ℒₒᵣ aqr (imp ℒₒᵣ aqc arc)) Γ) := by
    have h := derivationOf_specializeCtxValue S
      (t := nc) (by simp [nc]) hd₂
    simpa [d₃, nc, aqr, aqc, arc,
      thirdBody_substs_internal] using h
  have hm₁ : DerivationOf S m₁ (insert inner Γ) := by
    exact derivationOf_mpCtxValue S hd₃ he
  have hm₂ : DerivationOf S
      (mpCtxValue Γ aqc arc m₁ p) (insert arc Γ) := by
    exact derivationOf_mpCtxValue S hm₁ hp
  rw [transportValue_eq]
  simpa only [nq, nr, nc, st, kw, d₁, d₂, d₃,
    aqr, aqc, arc, inner, m₁] using hm₂

/-- Graph-level preservation, stated solely with evaluation of the exact
arithmetic derivation predicate at the three endpoints. -/
theorem transportGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (S : ArithmeticTheory) [S.Δ₁]
    {y k Γ e p q r c : V}
    (hy : Semiformula.Evalb (M := V)
      ![y, k, Γ, e, p, q, r, c] transportGraph.val)
    (hk : Semiformula.Evalb (M := V)
      ![k, insert (⌜theta⌝ : V) 0] (derivationOf S).sigma.val)
    (he : Semiformula.Evalb (M := V)
      ![e, insert (eqValue q r) Γ] (derivationOf S).sigma.val)
    (hp : Semiformula.Evalb (M := V)
      ![p, insert (eqValue q c) Γ] (derivationOf S).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert (eqValue r c) Γ] (derivationOf S).sigma.val := by
  have hy' : y = transportValue k Γ e p q r c :=
    (transportGraph_iff y k Γ e p q r c).mp hy
  have hk' : DerivationOf S k (insert (⌜theta⌝ : V) 0) := by
    simpa using hk
  have he' : DerivationOf S e (insert (eqValue q r) Γ) := by
    simpa using he
  have hp' : DerivationOf S p (insert (eqValue q c) Γ) := by
    simpa using hp
  rw [hy']
  simpa using derivationOf_transportValue S hk' he' hp'

/-! ## One seed, fixed before the theory and the model -/

/-- A single standard proof code works as the `Theta` seed in every
Delta-one-presented arithmetic theory and every PA model.  The witness is
chosen before both the theory and model quantifiers. -/
theorem exists_uniform_theta_seed :
    ∃ seed : ℕ,
      ∀ (S : ArithmeticTheory) [S.Δ₁]
        (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano],
        DerivationOf S (ORingStructure.numeral seed : V)
          (insert (⌜theta⌝ : V) 0) := by
  let b : ⊢ᴸᴷ¹ ⦃(theta : FFL.FirstOrder.ArithmeticProposition)⦄ :=
    theta_provable.get
  refine ⟨(⌜b⌝ : ℕ), ?_⟩
  intro S _ V _ _
  have h := derivation_of_quote_derivation (T := S) (V := V) b
  have hcode : (ORingStructure.numeral (⌜b⌝ : ℕ) : V) =
      (⌜b⌝ : V) := by
    rw [numeral_eq_natCast_app]
    simp only [quote_derivation_def]
    exact LK2.Derivation.coe_quote_eq V
      (LK.Derivation.toDerivation2 (∅ : Theory ℒₒᵣ) b)
  rw [hcode]
  have hseq :
      (⌜(⦃(theta : FFL.FirstOrder.ArithmeticProposition)⦄ :
        LK.Sequent ℒₒᵣ).toFinset⌝ : V) =
        insert (⌜theta⌝ : V) 0 := by
    rw [show (⦃(theta : FFL.FirstOrder.ArithmeticProposition)⦄ :
      LK.Sequent ℒₒᵣ).toFinset =
        {(theta : FFL.FirstOrder.ArithmeticProposition)} by rfl]
    rw [LK2.Derivation.Sequent.quote_singleton]
    rw [singleton_eq_insert, ← Sentence.quote_def theta]
    rfl
  rw [← hseq]
  exact h

/-- Six varying arguments after fixing the standard seed, packed as
`(((((Gamma,e),p),q),r),c)`. -/
abbrev FixedSeedTransportArgs :=
  (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)

def transportCtxForSeed
    (seed Γ e p q r c : ℕ) : ℕ :=
  transportCtxWithSeed seed Γ e p q r c

def transportCtxForSeedPacked
    (seed : ℕ) (z : FixedSeedTransportArgs) : ℕ :=
  transportCtxForSeed seed z.1.1.1.1.1 z.1.1.1.1.2
    z.1.1.1.2 z.1.1.2 z.1.2 z.2

/-- After fixing any seed, the remaining six-input transport is primitive
recursive. -/
theorem primrec_transportCtxForSeedPacked (seed : ℕ) :
    Primrec (transportCtxForSeedPacked seed) := by
  have hΓ : Primrec (fun z : FixedSeedTransportArgs => z.1.1.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))
  have he : Primrec (fun z : FixedSeedTransportArgs => z.1.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp
      (Primrec.fst.comp Primrec.fst)))
  have hp : Primrec (fun z : FixedSeedTransportArgs => z.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hq : Primrec (fun z : FixedSeedTransportArgs => z.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun z : FixedSeedTransportArgs => z.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun z : FixedSeedTransportArgs => z.2) :=
    Primrec.snd
  have h := primrec_transportCtxWithSeedPacked.comp <|
    ((((((Primrec.const seed).pair hΓ).pair he).pair hp).pair hq).pair hr).pair hc
  apply h.of_eq
  intro z
  rfl

/-- The uniform seed theorem together with the primitive-recursive
six-input family and its internal preservation conclusion. -/
theorem exists_uniform_native_transport :
    ∃ seed : ℕ,
      Primrec (transportCtxForSeedPacked seed) ∧
      ∀ (S : ArithmeticTheory) [S.Δ₁]
        (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano],
        DerivationOf S (ORingStructure.numeral seed : V)
            (insert (⌜theta⌝ : V) 0) ∧
        ∀ Γ e p q r c : V,
          DerivationOf S e (insert (eqValue q r) Γ) →
          DerivationOf S p (insert (eqValue q c) Γ) →
          DerivationOf S
            (transportValue (ORingStructure.numeral seed : V)
              Γ e p q r c)
            (insert (eqValue r c) Γ) := by
  rcases exists_uniform_theta_seed with ⟨seed, hseed⟩
  refine ⟨seed, primrec_transportCtxForSeedPacked seed, ?_⟩
  intro S _ V _ _
  refine ⟨hseed S V, ?_⟩
  intro Γ e p q r c he hp
  exact derivationOf_transportValue S (hseed S V) he hp

/-! ## Standard, empty-context, singleton, and Craig applications -/

/-- Natural-number preservation for the total executable constructor. -/
theorem derivationOf_transportCtxWithSeed
    (S : ArithmeticTheory) [S.Δ₁]
    {k Γ e p q r c : ℕ}
    (hk : DerivationOf S k (insert (⌜theta⌝ : ℕ) 0))
    (he : DerivationOf S e (insert (nativeEqCode q r) Γ))
    (hp : DerivationOf S p (insert (nativeEqCode q c) Γ)) :
    DerivationOf S (transportCtxWithSeed k Γ e p q r c)
      (insert (nativeEqCode r c) Γ) := by
  rw [← transportValue_nat]
  have he' : DerivationOf S e (insert (eqValue q r) Γ) := by
    simpa only [eqValue_nat] using he
  have hp' : DerivationOf S p (insert (eqValue q c) Γ) := by
    simpa only [eqValue_nat] using hp
  simpa only [eqValue_nat] using
    derivationOf_transportValue S hk he' hp'

def transportWithSeed (seed e p q r c : ℕ) : ℕ :=
  transportCtxWithSeed seed 0 e p q r c

/-- Empty-context proof transport; after `seed` and its validity proof are
fixed, the varying numerical inputs are exactly `e,p,q,r,c`. -/
theorem proof_transportWithSeed
    (S : ArithmeticTheory) [S.Δ₁]
    (seed : ℕ) (hseed : Proof S seed (⌜theta⌝ : ℕ))
    {e p q r c : ℕ}
    (he : Proof S e (nativeEqCode q r))
    (hp : Proof S p (nativeEqCode q c)) :
    Proof S (transportWithSeed seed e p q r c)
      (nativeEqCode r c) := by
  have hseed' : DerivationOf S seed (insert (⌜theta⌝ : ℕ) 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using hseed
  have he' : DerivationOf S e (insert (nativeEqCode q r) 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using he
  have hp' : DerivationOf S p (insert (nativeEqCode q c) 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using hp
  have h := derivationOf_transportCtxWithSeed S hseed' he' hp'
  simpa [transportWithSeed, Proof, singleton_eq_insert,
    emptyset_def] using h

/-- A singleton context is retained verbatim by the native transport. -/
theorem derivationOf_transportCtxWithSeed_singleton
    (S : ArithmeticTheory) [S.Δ₁]
    {seed a e p q r c : ℕ}
    (hseed : DerivationOf S seed (insert (⌜theta⌝ : ℕ) 0))
    (he : DerivationOf S e
      (insert (nativeEqCode q r) (insert a 0)))
    (hp : DerivationOf S p
      (insert (nativeEqCode q c) (insert a 0))) :
    DerivationOf S
      (transportCtxWithSeed seed (insert a 0) e p q r c)
      (insert (nativeEqCode r c) (insert a 0)) :=
  derivationOf_transportCtxWithSeed S hseed he hp

/-- Internal graph preservation for Foundation's Craig companion of an
external recursively enumerable theory. -/
theorem craig_transportGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* Peano]
    (T : ArithmeticTheory) [T.RE]
    {y k Γ e p q r c : V}
    (hy : Semiformula.Evalb (M := V)
      ![y, k, Γ, e, p, q, r, c] transportGraph.val)
    (hk : Semiformula.Evalb (M := V)
      ![k, insert (⌜theta⌝ : V) 0]
      (derivationOf T.craig).sigma.val)
    (he : Semiformula.Evalb (M := V)
      ![e, insert (eqValue q r) Γ]
      (derivationOf T.craig).sigma.val)
    (hp : Semiformula.Evalb (M := V)
      ![p, insert (eqValue q c) Γ]
      (derivationOf T.craig).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert (eqValue r c) Γ]
      (derivationOf T.craig).sigma.val :=
  transportGraph_preserves_derivationOf T.craig hy hk he hp

theorem craig_proof_transportWithSeed
    (T : ArithmeticTheory) [T.RE]
    (seed : ℕ) (hseed : Proof T.craig seed (⌜theta⌝ : ℕ))
    {e p q r c : ℕ}
    (he : Proof T.craig e (nativeEqCode q r))
    (hp : Proof T.craig p (nativeEqCode q c)) :
    Proof T.craig (transportWithSeed seed e p q r c)
      (nativeEqCode r c) :=
  proof_transportWithSeed T.craig seed hseed he hp

/-- Standard adequacy of the native eventual/eventual equality code.  This
is a theorem-only bridge and supplies no conversion to the production proof
checker. -/
theorem craig_proof_nativeEqCode_iff_eqIndex
    (T : ArithmeticTheory) [T.RE] (q r : ℕ) :
    (∃ d : ℕ, Proof T.craig d (nativeEqCode q r)) ↔
      UniformIndexQuotient.EqIndex T q r := by
  change Provable T.craig (nativeEqCode q r) ↔
    T ⊢ uniformSentence (eventualGraph q) (eventualGraph r)
  have hcode : nativeEqCode q r =
      (⌜uniformSentence (eventualGraph q) (eventualGraph r)⌝ : ℕ) := by
    rw [nativeEqCode, equalityFormula_instance]
    exact (Sentence.quote_eq_encode_nat _).symm
  rw [hcode]
  exact NativeContextMP.craig_provable_iff T
    (uniformSentence (eventualGraph q) (eventualGraph r))

end FailureOfComposition.NativeEqualityTransport
