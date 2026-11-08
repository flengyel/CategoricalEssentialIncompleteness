/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxOperations
import CategoricalEssentialIncompleteness.V46MillerUniformFinite
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws
import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! # Positive value-stack invariants for arbitrary uniform algebra operations

The stored stack uses the existing arithmetic list and ordered pair codes.
Only temporary states and their positive operation witnesses are recorded;
the input syntax retains its original word and coefficient labels.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)

def fiberBlock (a : ℕ × ℕ) : Prop :=
  ((Nat.unpair a.2).2=0 ∧ fiber R X Y .term (a.1,(Nat.unpair a.2).1)) ∨
  ((Nat.unpair a.2).2=1 ∧ fiber R X Y .formula (a.1,(Nat.unpair a.2).1))

def fiberStack (a : ℕ × ℕ) : Prop :=
  ∀ block ∈ Nat.natToList a.2,fiberBlock R X Y (a.1,block)

def status (a : ℕ × ℕ) : Prop :=
  a.1 ∈ R.obj.support ∧ (a.2=0 ∨ fiberStack R X Y (a.1,a.2-1))

theorem fiberBlock_enumerable : Uniform.Enumerable P (fiberBlock R X Y) := by
  have hv : Computable (fun a : ℕ × ℕ => (a.1,(Nat.unpair a.2).1)) :=
    Computable.pair Computable.fst (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have ht : Primrec (fun a : ℕ × ℕ => (Nat.unpair a.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
  exact ((Uniform.Enumerable.of_re ((Primrec.eq.comp ht (.const 0)).computablePred.to_re)).and
    (Uniform.Enumerable.comp hv (fiber_enumerable R X Y .term))).or
    ((Uniform.Enumerable.of_re ((Primrec.eq.comp ht (.const 1)).computablePred.to_re)).and
      (Uniform.Enumerable.comp hv (fiber_enumerable R X Y .formula)))

def stackEntries (a : ℕ × ℕ) : List (ℕ × ℕ) :=
  (Nat.natToList a.2).map (fun block => (a.1,block))

theorem stackEntries_primrec : Primrec stackEntries := by
  exact Primrec.list_map (Primrec.nat_natToList.comp Primrec.snd)
    (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem fiberStack_enumerable : Uniform.Enumerable P (fiberStack R X Y) := by
  exact (Uniform.Enumerable.finiteRecord (fiberBlock_enumerable R X Y)
    stackEntries stackEntries_primrec.to_comp).of_eq (fun a => by
      simp only [fiberStack,stackEntries,List.forall_mem_map])

theorem status_enumerable : Uniform.Enumerable P (status R X Y) :=
  (Uniform.Enumerable.comp Computable.fst R.obj.enumerable).and
    ((Uniform.Enumerable.of_re ((Primrec.eq.comp Primrec.snd (.const 0)).computablePred.to_re)).or
      (Uniform.Enumerable.comp
        (Computable.pair Computable.fst (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)))
        (fiberStack_enumerable R X Y)))

@[simp] theorem fiberStack_nil (r : ℕ) : fiberStack R X Y (r,0) := by
  simp [fiberStack,Nat.natToList]

@[simp] theorem fiberStack_adjoin (r block stack : ℕ) :
    fiberStack R X Y (r,adjoin block stack) ↔
      fiberBlock R X Y (r,block) ∧ fiberStack R X Y (r,stack) := by
  simp only [fiberStack,natToList_adjoin,List.mem_cons,forall_eq_or_imp]

@[simp] theorem fiberBlock_term (r v : ℕ) :
    fiberBlock R X Y (r,Nat.pair v 0) ↔ fiber R X Y .term (r,v) := by
  simp [fiberBlock]

@[simp] theorem fiberBlock_formula (r v : ℕ) :
    fiberBlock R X Y (r,Nat.pair v 1) ↔ fiber R X Y .formula (r,v) := by
  simp [fiberBlock]

@[simp] theorem status_zero (r : ℕ) : status R X Y (r,0) ↔ r ∈ R.obj.support := by
  simp [status]

@[simp] theorem status_succ (r stack : ℕ) :
    status R X Y (r,stack+1) ↔ r ∈ R.obj.support ∧ fiberStack R X Y (r,stack) := by
  simp [status]

/-- This erases coefficient predicates only for the structural parser.
Coefficient membership remains an independent positive fiber condition. -/
def skeleton (p : SyntaxPolynomial (Total.TotalCategory P)) : SyntacticSyntax.RawPolynomial :=
  p.mapCoefficients (fun _ => Coding.zeroCarrier)

def refill (p : SyntaxPolynomial (Total.TotalCategory P)) (s stack : ℕ) : ℕ :=
  Coding.refill (skeleton p) s stack

theorem refill_primrec (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec₂ (refill p) :=
  NatVectors.refill_primrec (skeleton p)

theorem refill_fiber (q : SyntaxPolynomial (Total.TotalCategory P)) (r s stack u rest : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) q).support)
    (hst : fiberStack R X Y (r,stack))
    (h : refill q s stack = adjoin u rest) :
    fiber R X Y q (r,u) ∧ fiberStack R X Y (r,rest) := by
  induction q generalizing s stack u rest with
  | term =>
      obtain ⟨_,he⟩ := Coding.refillLeaf_sound false s stack u rest h
      rw [he,fiberStack_adjoin] at hst
      simpa [nat_pair_eq] using hst
  | formula =>
      obtain ⟨_,he⟩ := Coding.refillLeaf_sound true s stack u rest h
      rw [he,fiberStack_adjoin] at hst
      simpa [nat_pair_eq] using hst
  | coefficient C =>
      have hh : adjoin s stack = adjoin u rest := h
      obtain ⟨hu,hrest⟩ := (adjoin_inj _ _ _ _).mp hh
      exact ⟨by simpa [fiber,carrier,← hu] using And.intro hr hs,by simpa [← hrest] using hst⟩
  | unit =>
      by_cases hz : s=0
      · have hh : adjoin 0 stack = adjoin u rest := by
          simpa [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hz] using h
        obtain ⟨hu,hrest⟩ := (adjoin_inj _ _ _ _).mp hh
        exact ⟨by simp [fiber,← hu,hr],by simpa [← hrest] using hst⟩
      · simp [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hz] at h
  | product a b ia ib =>
      let x : ℕ := π₁ s
      let y : ℕ := π₂ s
      have hx : x ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) a).support := by
        simpa only [x,FiniteSigmaOne.nat_pi₁_eq] using hs.1
      have hy : y ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) b).support := by
        simpa only [y,NatVectors.nat_pi₂_eq] using hs.2
      rcases nil_or_adjoin (refill b y stack) with hbr | ⟨rv,rs,hbr⟩
      · dsimp [refill,skeleton,y] at hbr
        simp [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hbr] at h
      · dsimp [refill,skeleton,y] at hbr
        rcases nil_or_adjoin (refill a x rs) with har | ⟨lv,ls,har⟩
        · dsimp [refill,skeleton,x] at har
          simp [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hbr,har] at h
        · dsimp [refill,skeleton,x] at har
          have hh : adjoin ⟪lv,rv⟫ ls = adjoin u rest := by
            simpa [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hbr,har] using h
          obtain ⟨hu,hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hrv,hrs⟩ := ib y stack rv rs hy hst hbr
          obtain ⟨hlv,hls⟩ := ia x rs lv ls hx hrs har
          rw [← hu,← hrest]
          exact ⟨by simpa only [nat_pair_eq,fiber_product] using And.intro hlv hrv,hls⟩
  | sum a b ia ib =>
      rcases hs with ⟨hk,hv⟩ | ⟨hk,hv⟩
      · have hk' : π₂ s=0 := by simpa only [NatVectors.nat_pi₂_eq] using hk
        have hv' : π₁ s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) a).support := by
          simpa only [FiniteSigmaOne.nat_pi₁_eq] using hv
        rcases nil_or_adjoin (refill a (π₁ s) stack) with hl | ⟨v,rs,hl⟩
        · dsimp [refill,skeleton] at hl
          simp [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hk',hl] at h
        · dsimp [refill,skeleton] at hl
          have hh : adjoin ⟪v,0⟫ rs = adjoin u rest := by
            simpa [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hk',hl] using h
          obtain ⟨hu,hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv,hrs⟩ := ia (π₁ s) stack v rs hv' hst hl
          rw [← hu,← hrest]
          exact ⟨by simpa only [nat_pair_eq,fiber_sum_inl] using hv,hrs⟩
      · have hk' : π₂ s=1 := by simpa only [NatVectors.nat_pi₂_eq] using hk
        have hv' : π₁ s ∈ (carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) b).support := by
          simpa only [FiniteSigmaOne.nat_pi₁_eq] using hv
        rcases nil_or_adjoin (refill b (π₁ s) stack) with hl | ⟨v,rs,hl⟩
        · dsimp [refill,skeleton] at hl
          simp [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hk',hl] at h
        · dsimp [refill,skeleton] at hl
          have hh : adjoin ⟪v,1⟫ rs = adjoin u rest := by
            simpa [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill,hk',hl] using h
          obtain ⟨hu,hrest⟩ := (adjoin_inj _ _ _ _).mp hh
          obtain ⟨hv,hrs⟩ := ib (π₁ s) stack v rs hv' hst hl
          rw [← hu,← hrest]
          exact ⟨by simpa only [nat_pair_eq,fiber_sum_inr] using hv,hrs⟩

/-- The structural computation used on the original predicate polynomial
is unchanged by the temporary erasure of its coefficient guards. -/
theorem refill_mapped (Q : SyntacticSyntax.RawPolynomial)
    (F : SyntacticPredicates.Carrier → Total.TotalCategory P) (s stack : ℕ) :
    refill (Q.mapCoefficients F) s stack = Coding.refill Q s stack := by
  induction Q generalizing s stack with
  | term => rfl
  | formula => rfl
  | coefficient _ => rfl
  | unit => rfl
  | product a b ia ib =>
      simp only [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill] at *
      rw [ib,ia]
  | sum a b ia ib =>
      simp only [refill,skeleton,SyntaxPolynomial.mapCoefficients,Coding.refill] at *
      rw [ia,ib]

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
