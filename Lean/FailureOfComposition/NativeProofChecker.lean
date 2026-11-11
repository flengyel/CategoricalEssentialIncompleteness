/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NativeSyntaxShift
public import FailureOfComposition.NativeEqualityTransport

/-!
# Primitive-recursive checking of native derivations

Fix an executable axiom test `ax : ℕ → Bool`.  The checker recognizes the
entire ten-rule Foundation calculus over the natural numbers.  Primitive
recursiveness requires `Primrec ax`; correctness instead requires agreement
with the chosen theory presentation only on valid proposition codes.
Propositions may contain free variables.

Proof conclusions are finite-set sequent codes.  A computation at code `d`
uses a table of results at codes below `d`, so every recursive rule checks
both its child derivations and their exact concluding sequents.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic

namespace FailureOfComposition.NativeProofChecker

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution
open FailureOfComposition.NativeContextSpecialization
open FailureOfComposition.NativeSyntaxShift

/-- The semantic premise concerns valid formulas, including open formulas. -/
def AxiomAgreement (ax : ℕ → Bool) (S : ArithmeticTheory) [S.Δ₁] : Prop :=
  ∀ a : ℕ, IsFormula ℒₒᵣ a → (ax a = true ↔ a ∈ (S.Δ₁Class : Set ℕ))

/-- Exact sequent projection, total also at code zero. -/
def conclusionCode (d : ℕ) : ℕ := (d - 1).unpair.1

def sequentMemCode (p s : ℕ) : Bool := decide (s / 2 ^ p % 2 = 1)

def sequentSubsetCode (s t : ℕ) : Bool :=
  decide (∀ p ∈ List.range s, s / 2 ^ p % 2 = 1 → t / 2 ^ p % 2 = 1)

def childCheck (history : List Bool) (d s : ℕ) : Bool :=
  history.getD d false && (conclusionCode d == s)

/-- The payload is decoded according to its tag.  In particular, tag one
requires the literal residual payload zero.  Unsupported tags return false. -/
def ruleBodyCheck (ax : ℕ → Bool) (history : List Bool)
    (s tag u : ℕ) : Bool :=
  if tag = 0 then
    formulaCodeValid u && sequentMemCode u s &&
      sequentMemCode (formulaNegTotalCode u) s
  else if tag = 1 then (u == 0) && sequentMemCode (Nat.pair 2 0 + 1) s
  else if tag = 2 then
    let p := u.unpair.1
    let q := u.unpair.2.unpair.1
    let dp := u.unpair.2.unpair.2.unpair.1
    let dq := u.unpair.2.unpair.2.unpair.2
    sequentMemCode (formulaAndCode p q) s &&
      childCheck history dp (sequentInsertCode p s) &&
      childCheck history dq (sequentInsertCode q s)
  else if tag = 3 then
    let p := u.unpair.1
    let q := u.unpair.2.unpair.1
    let d := u.unpair.2.unpair.2
    sequentMemCode (formulaOrCode p q) s &&
      childCheck history d (sequentInsertCode p (sequentInsertCode q s))
  else if tag = 4 then
    let p := u.unpair.1
    let d := u.unpair.2
    formulaBodyCodeValid p && sequentMemCode (formulaAllCode p) s &&
      childCheck history d
        (sequentInsertCode (formulaFreeCode p) (sequentShiftCode s))
  else if tag = 5 then
    let p := u.unpair.1
    let t := u.unpair.2.unpair.1
    let d := u.unpair.2.unpair.2
    formulaBodyCodeValid p && termCodeValid t &&
      sequentMemCode (formulaExistsCode p) s &&
      childCheck history d (sequentInsertCode (subst1Code t p) s)
  else if tag = 6 then
    sequentSubsetCode (conclusionCode u) s && history.getD u false
  else if tag = 7 then
    (s == sequentShiftCode (conclusionCode u)) && history.getD u false
  else if tag = 8 then
    let p := u.unpair.1
    let d₁ := u.unpair.2.unpair.1
    let d₂ := u.unpair.2.unpair.2
    formulaCodeValid p &&
      childCheck history d₁ (sequentInsertCode p s) &&
      childCheck history d₂ (sequentInsertCode (formulaNegTotalCode p) s)
  else if tag = 9 then sequentMemCode u s && ax u
  else false

/-- One table step.  Zero fails before the constructor is decoded. -/
def ruleCheck (ax : ℕ → Bool) (history : List Bool) (d : ℕ) : Bool :=
  if d = 0 then false else
    formulaSetCodeValid (conclusionCode d) &&
      ruleBodyCheck ax history (conclusionCode d)
        (d - 1).unpair.2.unpair.1 (d - 1).unpair.2.unpair.2

/-- `checkTable ax n` contains the results at exactly the codes below `n`. -/
def checkTable (ax : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => let h := checkTable ax n; h ++ [ruleCheck ax h n]

def nativeDerivationCheck (ax : ℕ → Bool) (d : ℕ) : Bool :=
  (checkTable ax (d + 1)).getD d false

def nativeDerivationOfCheck (ax : ℕ → Bool) (d Γ : ℕ) : Bool :=
  nativeDerivationCheck ax d && (conclusionCode d == Γ)

def nativeProofCheck (ax : ℕ → Bool) (d a : ℕ) : Bool :=
  nativeDerivationOfCheck ax d (sequentInsertCode a 0)

theorem primrec_conclusionCode : Primrec conclusionCode :=
  Primrec.fst.comp <| Primrec.unpair.comp <|
    Primrec.nat_sub.comp Primrec.id (Primrec.const 1)

theorem primrec₂_sequentMemCode : Primrec₂ sequentMemCode := by
  exact (primrecPred_sequentMem.comp (Primrec.snd.pair Primrec.fst)).decide

theorem primrecPred_sequentSubsetCode :
    PrimrecPred fun z : ℕ × ℕ => sequentSubsetCode z.1 z.2 = true := by
  have h : PrimrecPred fun z : ℕ × (ℕ × ℕ) =>
      ¬z.2.1 / 2 ^ z.1 % 2 = 1 ∨ z.2.2 / 2 ^ z.1 % 2 = 1 :=
    (primrecPred_sequentMem.comp
      ((Primrec.fst.comp Primrec.snd).pair Primrec.fst)).not.or
      (primrecPred_sequentMem.comp
        ((Primrec.snd.comp Primrec.snd).pair Primrec.fst))
  exact (h.primrecRel.forall_mem_list.comp
    (Primrec.list_range.comp Primrec.fst) Primrec.id).of_eq fun z => by
      simp only [sequentSubsetCode, decide_eq_true_eq, List.mem_range]
      exact forall_congr' fun p => forall_congr' fun _ => imp_iff_not_or.symm

theorem primrec₂_sequentSubsetCode : Primrec₂ sequentSubsetCode := by
  exact primrecPred_sequentSubsetCode.decide.of_eq fun z => by simp

private theorem primrec_formulaCodeValid : Primrec formulaCodeValid :=
  primrecPred_formulaCodeValid.decide.of_eq fun _ => by simp

private theorem primrec_formulaBodyCodeValid : Primrec formulaBodyCodeValid :=
  primrecPred_formulaBodyCodeValid.decide.of_eq fun _ => by simp

private theorem primrec_termCodeValid : Primrec termCodeValid :=
  primrecPred_termCodeValid.decide.of_eq fun _ => by simp

private theorem primrec_formulaSetCodeValid : Primrec formulaSetCodeValid :=
  primrecPred_formulaSetCodeValid.decide.of_eq fun _ => by simp

private theorem primrec_childCheck {A : Type} [Primcodable A]
    {h : A → List Bool} {d s : A → ℕ}
    (hh : Primrec h) (hd : Primrec d) (hs : Primrec s) :
    Primrec fun x => childCheck (h x) (d x) (s x) :=
  Primrec.and.comp ((Primrec.list_getD false).comp hh hd)
    (Primrec.beq.comp (primrec_conclusionCode.comp hd) hs)

private theorem primrec_ruleBodyCheck {A : Type} [Primcodable A]
    {ax : ℕ → Bool} (hax : Primrec ax)
    {h : A → List Bool} {s tag u : A → ℕ}
    (hh : Primrec h) (hs : Primrec s) (ht : Primrec tag) (hu : Primrec u) :
    Primrec fun x => ruleBodyCheck ax (h x) (s x) (tag x) (u x) := by
  have haxu := hax.comp hu
  have hu₁ := Primrec.fst.comp (Primrec.unpair.comp hu)
  have hu₂ := Primrec.snd.comp (Primrec.unpair.comp hu)
  have hu₂₁ := Primrec.fst.comp (Primrec.unpair.comp hu₂)
  have hu₂₂ := Primrec.snd.comp (Primrec.unpair.comp hu₂)
  have hu₂₂₁ := Primrec.fst.comp (Primrec.unpair.comp hu₂₂)
  have hu₂₂₂ := Primrec.snd.comp (Primrec.unpair.comp hu₂₂)
  have hget := fun {d : A → ℕ} (hd : Primrec d) => (Primrec.list_getD false).comp hh hd
  have b₀ := Primrec.and.comp
    (Primrec.and.comp (primrec_formulaCodeValid.comp hu)
      (primrec₂_sequentMemCode.comp hu hs))
    (primrec₂_sequentMemCode.comp (primrec_formulaNegTotalCode.comp hu) hs)
  have b₁ := Primrec.and.comp (Primrec.beq.comp hu (Primrec.const 0))
    (primrec₂_sequentMemCode.comp (Primrec.const (Nat.pair 2 0 + 1)) hs)
  have b₂ := Primrec.and.comp
    (Primrec.and.comp (primrec₂_sequentMemCode.comp
      (primrec₂_formulaAndCode.comp hu₁ hu₂₁) hs)
      (primrec_childCheck hh hu₂₂₁ (primrec₂_sequentInsertCode.comp hu₁ hs)))
    (primrec_childCheck hh hu₂₂₂ (primrec₂_sequentInsertCode.comp hu₂₁ hs))
  have b₃ := Primrec.and.comp
    (primrec₂_sequentMemCode.comp (primrec₂_formulaOrCode.comp hu₁ hu₂₁) hs)
    (primrec_childCheck hh hu₂₂ (primrec₂_sequentInsertCode.comp hu₁
      (primrec₂_sequentInsertCode.comp hu₂₁ hs)))
  have b₄ := Primrec.and.comp
    (Primrec.and.comp (primrec_formulaBodyCodeValid.comp hu₁)
      (primrec₂_sequentMemCode.comp (primrec_formulaAllCode.comp hu₁) hs))
    (primrec_childCheck hh hu₂ (primrec₂_sequentInsertCode.comp
      (primrec_formulaFreeCode.comp hu₁) (primrec_sequentShiftCode.comp hs)))
  have b₅ := Primrec.and.comp
    (Primrec.and.comp
      (Primrec.and.comp (primrec_formulaBodyCodeValid.comp hu₁)
        (primrec_termCodeValid.comp hu₂₁))
      (primrec₂_sequentMemCode.comp (primrec_formulaExistsCode.comp hu₁) hs))
    (primrec_childCheck hh hu₂₂ (primrec₂_sequentInsertCode.comp
      (primrec₂_subst1Code.comp hu₂₁ hu₁) hs))
  have b₆ := Primrec.and.comp
    (primrec₂_sequentSubsetCode.comp (primrec_conclusionCode.comp hu) hs) (hget hu)
  have b₇ := Primrec.and.comp (Primrec.beq.comp hs
    (primrec_sequentShiftCode.comp (primrec_conclusionCode.comp hu))) (hget hu)
  have b₈ := Primrec.and.comp
    (Primrec.and.comp (primrec_formulaCodeValid.comp hu₁)
      (primrec_childCheck hh hu₂₁ (primrec₂_sequentInsertCode.comp hu₁ hs)))
    (primrec_childCheck hh hu₂₂ (primrec₂_sequentInsertCode.comp
      (primrec_formulaNegTotalCode.comp hu₁) hs))
  have b₉ := Primrec.and.comp (primrec₂_sequentMemCode.comp hu hs) haxu
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) b₀ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) b₁ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) b₂ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) b₃ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) b₄ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 5)) b₅ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 6)) b₆ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 7)) b₇ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 8)) b₈ <|
    Primrec.ite (Primrec.eq.comp ht (Primrec.const 9)) b₉ (Primrec.const false)

theorem primrec₂_ruleCheck {ax : ℕ → Bool} (hax : Primrec ax) :
    Primrec₂ (ruleCheck ax) := by
  have hb : Primrec fun z : List Bool × ℕ =>
      ruleBodyCheck ax z.1 (conclusionCode z.2)
        (z.2 - 1).unpair.2.unpair.1 (z.2 - 1).unpair.2.unpair.2 := by
    have hp := Primrec.unpair.comp
      (Primrec.nat_sub.comp (Primrec.snd (α := List Bool)) (Primrec.const 1))
    have hr := Primrec.unpair.comp (Primrec.snd.comp hp)
    exact primrec_ruleBodyCheck hax Primrec.fst
      (primrec_conclusionCode.comp Primrec.snd) (Primrec.fst.comp hr) (Primrec.snd.comp hr)
  unfold ruleCheck
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.const false) (Primrec.and.comp
      (primrec_formulaSetCodeValid.comp (primrec_conclusionCode.comp Primrec.snd)) hb)).to₂

theorem primrec_checkTable {ax : ℕ → Bool} (hax : Primrec ax) :
    Primrec (checkTable ax) := by
  exact (Primrec.nat_rec₁ ([] : List Bool)
    (f := fun n h => h ++ [ruleCheck ax h n])
    ((Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp ((primrec₂_ruleCheck hax).comp Primrec.snd Primrec.fst)
        (Primrec.const []))).to₂)).of_eq fun n => by
      induction n with
      | zero => rfl
      | succ n ih => simp only [checkTable, ih]

@[simp] theorem checkTable_length (ax : ℕ → Bool) (n : ℕ) :
    (checkTable ax n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [checkTable, ih]

theorem nativeDerivationCheck_eq_ruleCheck (ax : ℕ → Bool) (d : ℕ) :
    nativeDerivationCheck ax d = ruleCheck ax (checkTable ax d) d := by
  unfold nativeDerivationCheck
  rw [checkTable, List.getD_append_right]
  · simp
  · simp

theorem checkTable_getD (ax : ℕ → Bool) {n d : ℕ} (hd : d < n) :
    (checkTable ax n).getD d false = nativeDerivationCheck ax d := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hdn : d < n
      · rw [checkTable, List.getD_append _ _ _ _ (by simpa using hdn), ih hdn]
      · have hdeq : d = n := by omega
        subst d
        rfl

theorem primrec_nativeDerivationCheck {ax : ℕ → Bool} (hax : Primrec ax) :
    Primrec (nativeDerivationCheck ax) :=
  (Primrec.list_getD false).comp
    ((primrec_checkTable hax).comp Primrec.succ) Primrec.id

theorem primrec₂_nativeDerivationOfCheck {ax : ℕ → Bool} (hax : Primrec ax) :
    Primrec₂ (nativeDerivationOfCheck ax) :=
  (Primrec.and.comp ((primrec_nativeDerivationCheck hax).comp Primrec.fst)
    (Primrec.beq.comp (primrec_conclusionCode.comp Primrec.fst) Primrec.snd)).to₂

theorem primrec₂_nativeProofCheck {ax : ℕ → Bool} (hax : Primrec ax) :
    Primrec₂ (nativeProofCheck ax) :=
  ((primrec₂_nativeDerivationOfCheck hax).comp Primrec.fst
    (primrec₂_sequentInsertCode.comp Primrec.snd (Primrec.const 0))).to₂

set_option backward.isDefEq.respectTransparency false in
theorem conclusionCode_eq_fstIdx (d : ℕ) : conclusionCode d = fstIdx d := by
  cases d with
  | zero => simp [conclusionCode, fstIdx, pi₁_zero]
  | succ e =>
    obtain ⟨p, q, rfl⟩ : ∃ p q, e = Nat.pair p q :=
      ⟨e.unpair.1, e.unpair.2, (Nat.pair_unpair e).symm⟩
    simp only [conclusionCode, Nat.add_sub_cancel, Nat.unpair_pair]
    rw [← nat_pair_eq]
    simp [fstIdx]

theorem sequentMemCode_iff (p s : ℕ) : sequentMemCode p s = true ↔ p ∈ s := by
  simp [sequentMemCode, nat_mem_iff]

theorem sequentSubsetCode_iff (s t : ℕ) :
    sequentSubsetCode s t = true ↔ s ⊆ t := by
  simp only [sequentSubsetCode, decide_eq_true_eq, List.mem_range]
  constructor
  · intro h p hp
    exact nat_mem_iff.mpr (h p (lt_of_mem hp) (nat_mem_iff.mp hp))
  · intro h p _ hp
    exact nat_mem_iff.mp (h (nat_mem_iff.mpr hp))

private theorem insertCode_eq (p s : ℕ) : sequentInsertCode p s = insert p s :=
  (nat_insert_eq p s).symm

private theorem andCode_eq (p q : ℕ) : formulaAndCode p q = p ^⋏ q := by
  simp [formulaAndCode, qqAnd, nat_pair_eq]

private theorem orCode_eq (p q : ℕ) : formulaOrCode p q = p ^⋎ q := by
  simp [formulaOrCode, qqOr, nat_pair_eq]

private theorem allCode_eq (p : ℕ) : formulaAllCode p = ^∀ p := by
  simp [formulaAllCode, qqAll, nat_pair_eq]

private theorem exsCode_eq (p : ℕ) : formulaExistsCode p = ^∃ p := by
  simp [formulaExistsCode, qqExs, nat_pair_eq]

private theorem pair_cases (u : ℕ) : ∃ p q, u = Nat.pair p q :=
  ⟨u.unpair.1, u.unpair.2, (Nat.pair_unpair u).symm⟩

private theorem childCheck_iff {S : ArithmeticTheory} [S.Δ₁]
    {history : List Bool} {d c : ℕ}
    (ih : ∀ n < d, history.getD n false = true ↔ Derivation S n)
    (hc : c < d) (s : ℕ) :
    childCheck history c s = true ↔ DerivationOf S c s := by
  simp only [childCheck, Bool.and_eq_true, beq_iff_eq,
    conclusionCode_eq_fstIdx, ih c hc, DerivationOf, and_comm]

set_option backward.isDefEq.respectTransparency false in
private theorem ruleCheck_sound {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (history : List Bool) (d : ℕ)
    (ih : ∀ n < d, history.getD n false = true ↔ Derivation S n)
    (h : ruleCheck ax history d = true) : Derivation S d := by
  cases d with
  | zero => simp [ruleCheck] at h
  | succ e =>
      rcases pair_cases e with ⟨s, z, rfl⟩
      rcases pair_cases z with ⟨tag, u, rfl⟩
      simp only [ruleCheck, conclusionCode, Nat.add_sub_cancel,
        Nat.unpair_pair, Nat.succ_ne_zero, ↓reduceIte, Bool.and_eq_true] at h
      have hs : IsFormulaSet ℒₒᵣ s := (formulaSetCodeValid_iff s).mp h.1
      have hb := h.2
      unfold ruleBodyCheck at hb
      split_ifs at hb with h₀ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉
      · subst tag
        simp only [Bool.and_eq_true, and_assoc, formulaCodeValid_iff_isFormula,
          sequentMemCode_iff] at hb
        have hn := hb.2.2
        rw [formulaNegTotalCode_eq_neg hb.1] at hn
        simpa [Bootstrapping.axL, nat_pair_eq] using
          (Derivation.axL (T := S) hs hb.2.1 hn)
      · subst tag
        simp only [Bool.and_eq_true, beq_iff_eq, sequentMemCode_iff] at hb
        rcases hb with ⟨rfl, hv⟩
        have hv' : (^⊤ : ℕ) ∈ s := by simpa [qqVerum, nat_pair_eq] using hv
        simpa [verumIntro, nat_pair_eq] using (Derivation.verumIntro (T := S) hs hv')
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨q, w, rfl⟩
        rcases pair_cases w with ⟨dp, dq, rfl⟩
        simp only [Nat.unpair_pair, Bool.and_eq_true, and_assoc, sequentMemCode_iff,
          andCode_eq, insertCode_eq] at hb
        have hdp := (childCheck_iff ih
          (by simpa [andIntro, nat_pair_eq] using dp_lt_andIntro s p q dp dq)
          (insert p s)).mp hb.2.1
        have hdq := (childCheck_iff ih
          (by simpa [andIntro, nat_pair_eq] using dq_lt_andIntro s p q dp dq)
          (insert q s)).mp hb.2.2
        simpa [andIntro, nat_pair_eq] using (Derivation.andIntro hb.1 hdp hdq)
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨q, dc, rfl⟩
        simp only [Nat.unpair_pair, Bool.and_eq_true, sequentMemCode_iff,
          orCode_eq, insertCode_eq] at hb
        have hdc := (childCheck_iff ih
          (by simpa [orIntro, nat_pair_eq] using d_lt_orIntro s p q dc)
          (insert p (insert q s))).mp hb.2
        simpa [orIntro, nat_pair_eq] using (Derivation.orIntro hb.1 hdc)
      · subst tag
        rcases pair_cases u with ⟨p, dc, rfl⟩
        simp only [Nat.unpair_pair, Bool.and_eq_true, and_assoc,
          formulaBodyCodeValid_iff_isSemiformula, sequentMemCode_iff,
          allCode_eq, insertCode_eq] at hb
        rw [formulaFreeCode_eq_free hb.1, sequentShiftCode_eq_setShift hs] at hb
        have hdc := (childCheck_iff ih
          (by simpa [allIntro, nat_pair_eq] using s_lt_allIntro s p dc) _).mp hb.2.2
        simpa [allIntro, nat_pair_eq] using (Derivation.allIntro hb.2.1 hdc)
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨t, dc, rfl⟩
        simp only [Nat.unpair_pair, Bool.and_eq_true, and_assoc,
          formulaBodyCodeValid_iff_isSemiformula, termCodeValid_iff_isSemiterm,
          sequentMemCode_iff, exsCode_eq, insertCode_eq] at hb
        rw [subst1Code_eq_substs1 hb.2.1 hb.1] at hb
        have hdc := (childCheck_iff ih
          (by simpa [exsIntro, nat_pair_eq] using d_lt_exsIntro s p t dc) _).mp hb.2.2.2
        simpa [exsIntro, nat_pair_eq] using (Derivation.exsIntro hb.2.2.1 hb.2.1 hdc)
      · subst tag
        simp only [Bool.and_eq_true, sequentSubsetCode_iff,
          conclusionCode_eq_fstIdx] at hb
        have hdc := (ih u (by simpa [wkRule, nat_pair_eq] using d_lt_wkRule s u)).mp hb.2
        simpa [wkRule, nat_pair_eq] using
          (Derivation.wkRule hs hb.1 (show DerivationOf S u (fstIdx u) from ⟨rfl, hdc⟩))
      · subst tag
        simp only [Bool.and_eq_true, beq_iff_eq, conclusionCode_eq_fstIdx] at hb
        have hdc := (ih u (by simpa [shiftRule, nat_pair_eq] using d_lt_shiftRule s u)).mp hb.2
        have heq : s = setShift ℒₒᵣ (fstIdx u) :=
          hb.1.trans (sequentShiftCode_eq_setShift hdc.isFormulaSet)
        have hout := Derivation.shiftRule (show DerivationOf S u (fstIdx u) from ⟨rfl, hdc⟩)
        rw [← heq] at hout
        simpa [shiftRule, nat_pair_eq] using hout
      · subst tag
        rcases pair_cases u with ⟨p, v, rfl⟩
        rcases pair_cases v with ⟨d₁, d₂, rfl⟩
        simp only [Nat.unpair_pair, Bool.and_eq_true, and_assoc, formulaCodeValid_iff_isFormula,
          insertCode_eq] at hb
        rw [formulaNegTotalCode_eq_neg hb.1] at hb
        have hd₁ := (childCheck_iff ih
          (by simpa [cutRule, nat_pair_eq] using d₁_lt_cutRule s p d₁ d₂) _).mp hb.2.1
        have hd₂ := (childCheck_iff ih
          (by simpa [cutRule, nat_pair_eq] using d₂_lt_cutRule s p d₁ d₂) _).mp hb.2.2
        simpa [cutRule, nat_pair_eq] using (Derivation.cutRule hd₁ hd₂)
      · subst tag
        simp only [Bool.and_eq_true, sequentMemCode_iff] at hb
        simpa [axm, nat_pair_eq] using (Derivation.axm (T := S) hs hb.1
          ((hax u (hs u hb.1)).mp hb.2))

private theorem ruleCheck_pair (ax : ℕ → Bool) (history : List Bool) (s tag u : ℕ) :
    ruleCheck ax history (Nat.pair s (Nat.pair tag u) + 1) =
      (formulaSetCodeValid s && ruleBodyCheck ax history s tag u) := by
  simp [ruleCheck, conclusionCode]

set_option backward.isDefEq.respectTransparency false in
private theorem ruleCheck_complete {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (history : List Bool) (d : ℕ)
    (ih : ∀ n < d, history.getD n false = true ↔ Derivation S n)
    (hd : Derivation S d) : ruleCheck ax history d = true := by
  rcases hd.case with ⟨hs, H⟩
  rcases H with
    (⟨s, p, rfl, hp, hnp⟩ | ⟨s, rfl, hv⟩ |
      ⟨s, p, q, dp, dq, rfl, hpq, hdp, hdq⟩ |
      ⟨s, p, q, dc, rfl, hpq, hdc⟩ |
      ⟨s, p, dc, rfl, hp, hdc⟩ |
      ⟨s, p, t, dc, rfl, hp, ht, hdc⟩ |
      ⟨s, dc, rfl, hsub, hdc⟩ | ⟨s, dc, rfl, heq, hdc⟩ |
      ⟨s, p, d₁, d₂, rfl, hd₁, hd₂⟩ | ⟨s, p, rfl, hp, hSp⟩)
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hfp := hseq p hp
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck,
      Bootstrapping.axL, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, formulaCodeValid_iff_isFormula, hfp,
      sequentMemCode_iff, hp, formulaNegTotalCode_eq_neg hfp, hnp]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hv' : Nat.pair 2 0 + 1 ∈ s := by simpa [qqVerum, nat_pair_eq] using hv
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, verumIntro, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, sequentMemCode_iff, hv']
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hdp' := (ih dp (dp_lt_andIntro s p q dp dq)).mpr hdp.2
    have hdq' := (ih dq (dq_lt_andIntro s p q dp dq)).mpr hdq.2
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, andIntro, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, sequentMemCode_iff, andCode_eq, hpq,
      childCheck, insertCode_eq, conclusionCode_eq_fstIdx, hdp', hdq', hdp.1, hdq.1]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hdc' := (ih dc (d_lt_orIntro s p q dc)).mpr hdc.2
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, orIntro, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, sequentMemCode_iff, orCode_eq, hpq,
      childCheck, insertCode_eq, conclusionCode_eq_fstIdx, hdc', hdc.1]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hbody : IsSemiformula ℒₒᵣ 1 p := by simpa using hseq _ hp
    have hdc' := (ih dc (s_lt_allIntro s p dc)).mpr hdc.2
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, allIntro, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, formulaBodyCodeValid_iff_isSemiformula, hbody,
      sequentMemCode_iff, allCode_eq, hp, formulaFreeCode_eq_free hbody,
      sequentShiftCode_eq_setShift hseq, childCheck, insertCode_eq,
      conclusionCode_eq_fstIdx, hdc', hdc.1]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hbody : IsSemiformula ℒₒᵣ 1 p := by simpa using hseq _ hp
    have hdc' := (ih dc (d_lt_exsIntro s p t dc)).mpr hdc.2
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, exsIntro, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, formulaBodyCodeValid_iff_isSemiformula, hbody,
      termCodeValid_iff_isSemiterm, ht, sequentMemCode_iff, exsCode_eq, hp,
      subst1Code_eq_substs1 ht hbody, childCheck, insertCode_eq,
      conclusionCode_eq_fstIdx, hdc', hdc.1]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hdc' := (ih dc (d_lt_wkRule s dc)).mpr hdc
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, wkRule, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, sequentSubsetCode_iff,
      conclusionCode_eq_fstIdx, hsub, hdc']
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hdc' := (ih dc (d_lt_shiftRule s dc)).mpr hdc
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, shiftRule, nat_pair_eq,
      formulaSetCodeValid_iff, hdc.isFormulaSet, conclusionCode_eq_fstIdx,
      sequentShiftCode_eq_setShift hdc.isFormulaSet, heq, hdc']
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have hfp : IsFormula ℒₒᵣ p := hd₁.isFormulaSet _ (by simp)
    have hd₁' := (ih d₁ (d₁_lt_cutRule s p d₁ d₂)).mpr hd₁.2
    have hd₂' := (ih d₂ (d₂_lt_cutRule s p d₁ d₂)).mpr hd₂.2
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, cutRule, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, formulaCodeValid_iff_isFormula, hfp,
      formulaNegTotalCode_eq_neg hfp, childCheck, insertCode_eq,
      conclusionCode_eq_fstIdx, hd₁', hd₂', hd₁.1, hd₂.1]
  · have hseq : IsFormulaSet ℒₒᵣ s := by simpa using hs
    have haxp := (hax p (hseq p hp)).mpr hSp
    simp [ruleCheck_pair, -List.getD_eq_getElem?_getD, ruleBodyCheck, axm, nat_pair_eq,
      formulaSetCodeValid_iff, hseq, sequentMemCode_iff, hp, haxp]

/-- Exact recognition on every natural-number input; syntax validity is
derived inside the proof and is not a public input premise. -/
theorem nativeDerivationCheck_iff {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (d : ℕ) :
    nativeDerivationCheck ax d = true ↔ Derivation S d := by
  induction d using Nat.strongRec with
  | ind d ih =>
      rw [nativeDerivationCheck_eq_ruleCheck]
      have hhistory : ∀ n < d,
          (checkTable ax d).getD n false = true ↔ Derivation S n := by
        intro n hn
        rw [checkTable_getD ax hn]
        exact ih n hn
      exact ⟨ruleCheck_sound hax _ _ hhistory,
        ruleCheck_complete hax _ _ hhistory⟩

theorem nativeDerivationOfCheck_iff {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (d Γ : ℕ) :
    nativeDerivationOfCheck ax d Γ = true ↔ DerivationOf S d Γ := by
  simp only [nativeDerivationOfCheck, Bool.and_eq_true, beq_iff_eq,
    nativeDerivationCheck_iff hax, conclusionCode_eq_fstIdx, DerivationOf, and_comm]

theorem nativeProofCheck_iff {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (d a : ℕ) :
    nativeProofCheck ax d a = true ↔ Proof S d a := by
  simp only [nativeProofCheck, nativeDerivationOfCheck_iff hax, insertCode_eq,
    Proof, singleton_eq_insert, emptyset_def]

theorem primrecPred_derivationOf {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hpr : Primrec ax) (hax : AxiomAgreement ax S) :
    PrimrecPred fun z : ℕ × ℕ => DerivationOf S z.1 z.2 :=
  (Primrec.eq.comp (primrec₂_nativeDerivationOfCheck hpr) (Primrec.const true)).of_eq
    fun z => nativeDerivationOfCheck_iff hax z.1 z.2

theorem primrecPred_proof {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hpr : Primrec ax) (hax : AxiomAgreement ax S) :
    PrimrecPred fun z : ℕ × ℕ => Proof S z.1 z.2 :=
  (Primrec.eq.comp (primrec₂_nativeProofCheck hpr) (Primrec.const true)).of_eq
    fun z => nativeProofCheck_iff hax z.1 z.2

/-! ## Craig axiom tests, chosen only in existence proofs -/

/-- A valid formula code need not be closed.  Membership forces it to be
the embedding of one of the theory's sentences. -/
theorem craig_codes_iff_deltaOneClass (T : ArithmeticTheory) [T.RE]
    {a : ℕ} (ha : IsFormula ℒₒᵣ a) :
    a ∈ encode '' T.craig ↔ a ∈ (T.craig.Δ₁Class : Set ℕ) := by
  rcases ha.sound with ⟨φ, rfl⟩
  rw [Δ₁Class.mem_iff_s]
  constructor
  · rintro ⟨σ, hσ, hcode⟩
    refine ⟨σ, hσ, ?_⟩
    apply Semiformula.encode_inj_sentence'.mp
    simpa only [Semiformula.quote_eq_encode_nat] using hcode
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, by simp [Semiformula.quote_eq_encode_nat]⟩

theorem exists_craig_axiomTest (T : ArithmeticTheory) [T.RE] :
    ∃ ax : ℕ → Bool, Primrec ax ∧ AxiomAgreement ax T.craig := by
  rcases Theory.primrecPred_craig_codes (T := T) with ⟨decAx, hpr⟩
  let := decAx
  refine ⟨fun a => decide (a ∈ encode '' T.craig), hpr, ?_⟩
  intro a ha
  simpa only [decide_eq_true_eq] using craig_codes_iff_deltaOneClass T ha

theorem primrecPred_craig_derivationOf (T : ArithmeticTheory) [T.RE] :
    PrimrecPred fun z : ℕ × ℕ => DerivationOf T.craig z.1 z.2 := by
  rcases exists_craig_axiomTest T with ⟨ax, hpr, hax⟩
  exact primrecPred_derivationOf hpr hax

theorem primrecPred_craig_proof (T : ArithmeticTheory) [T.RE] :
    PrimrecPred fun z : ℕ × ℕ => Proof T.craig z.1 z.2 := by
  rcases exists_craig_axiomTest T with ⟨ax, hpr, hax⟩
  exact primrecPred_proof hpr hax

/-! ## Recognition and transport of native equality proofs -/

def nativeEqProofCheck (ax : ℕ → Bool) (p q r : ℕ) : Bool :=
  nativeProofCheck ax p (NativeEqualityTransport.nativeEqCode q r)

/-- The three numerical arguments vary jointly in the packing `((p,q),r)`. -/
def nativeEqProofCheckPacked (ax : ℕ → Bool) (z : (ℕ × ℕ) × ℕ) : Bool :=
  nativeEqProofCheck ax z.1.1 z.1.2 z.2

theorem primrec_nativeEqProofCheckPacked {ax : ℕ → Bool} (hpr : Primrec ax) :
    Primrec (nativeEqProofCheckPacked ax) :=
  (primrec₂_nativeProofCheck hpr).comp (Primrec.fst.comp Primrec.fst)
    (NativeEqualityTransport.primrec₂_nativeEqCode.comp
      (Primrec.snd.comp Primrec.fst) Primrec.snd)

theorem nativeEqProofCheck_iff {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (p q r : ℕ) :
    nativeEqProofCheck ax p q r = true ↔
      Proof S p (NativeEqualityTransport.nativeEqCode q r) :=
  nativeProofCheck_iff hax p (NativeEqualityTransport.nativeEqCode q r)

abbrev ProofTransportArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

/-- The seed is fixed before the five varying inputs `e,p,q,r,c`. -/
def proofTransportPacked (seed : ℕ) (z : ProofTransportArgs) : ℕ :=
  NativeEqualityTransport.transportWithSeed seed
    z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

theorem primrec_proofTransportPacked (seed : ℕ) :
    Primrec (proofTransportPacked seed) := by
  have he : Primrec fun z : ProofTransportArgs => z.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hp : Primrec fun z : ProofTransportArgs => z.1.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hq : Primrec fun z : ProofTransportArgs => z.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec fun z : ProofTransportArgs => z.1.2 := Primrec.snd.comp Primrec.fst
  have hc : Primrec fun z : ProofTransportArgs => z.2 := Primrec.snd
  have h := (NativeEqualityTransport.primrec_transportCtxForSeedPacked seed).comp
    ((((((Primrec.const 0).pair he).pair hp).pair hq).pair hr).pair hc)
  apply h.of_eq
  intro z
  rfl

/-- For each fixed external recursively enumerable theory, one axiom test
and one theory/model-uniform logical seed give exact primitive-recursive
recognition and preservation under the existing executable transport. -/
theorem exists_craig_nativeEq_checker_transport (T : ArithmeticTheory) [T.RE] :
    ∃ (ax : ℕ → Bool) (seed : ℕ),
      Primrec ax ∧ AxiomAgreement ax T.craig ∧
      Primrec (nativeEqProofCheckPacked ax) ∧
      Primrec (proofTransportPacked seed) ∧
      Proof T.craig seed (⌜NativeEqualityTransport.theta⌝ : ℕ) ∧
      (∀ p q r : ℕ, nativeEqProofCheck ax p q r = true ↔
        Proof T.craig p (NativeEqualityTransport.nativeEqCode q r)) ∧
      (∀ q r : ℕ, (∃ p, nativeEqProofCheck ax p q r = true) ↔
        UniformIndexQuotient.EqIndex T q r) ∧
      (∀ e p q r c : ℕ,
        nativeEqProofCheck ax e q r = true →
        nativeEqProofCheck ax p q c = true →
        nativeEqProofCheck ax
          (NativeEqualityTransport.transportWithSeed seed e p q r c) r c = true) := by
  rcases exists_craig_axiomTest T with ⟨ax, hpr, hax⟩
  rcases NativeEqualityTransport.exists_uniform_theta_seed.{0} with ⟨seed, hseed⟩
  have hseedNat : Proof T.craig seed (⌜NativeEqualityTransport.theta⌝ : ℕ) := by
    simpa [Proof, singleton_eq_insert, emptyset_def, numeral_eq_natCast_app]
      using hseed T.craig ℕ
  refine ⟨ax, seed, hpr, hax, primrec_nativeEqProofCheckPacked hpr,
    primrec_proofTransportPacked seed, hseedNat, nativeEqProofCheck_iff hax, ?_, ?_⟩
  · intro q r
    simpa only [nativeEqProofCheck_iff hax] using
      NativeEqualityTransport.craig_proof_nativeEqCode_iff_eqIndex T q r
  · intro e p q r c he hp
    apply (nativeEqProofCheck_iff hax _ r c).mpr
    exact NativeEqualityTransport.proof_transportWithSeed T.craig seed hseedNat
      ((nativeEqProofCheck_iff hax e q r).mp he)
      ((nativeEqProofCheck_iff hax p q c).mp hp)

/-! ## Rule and malformed-input examples -/

theorem reject_zero (ax : ℕ → Bool) : nativeDerivationCheck ax 0 = false := by
  rw [nativeDerivationCheck_eq_ruleCheck]
  simp [ruleCheck]

theorem reject_verum_payload (ax : ℕ → Bool) (s u : ℕ) (hu : u ≠ 0) :
    nativeDerivationCheck ax (Nat.pair s (Nat.pair 1 u) + 1) = false := by
  rw [nativeDerivationCheck_eq_ruleCheck, ruleCheck_pair]
  simp [ruleBodyCheck, hu]

theorem reject_unsupported_tag (ax : ℕ → Bool) (s tag u : ℕ) (htag : 10 ≤ tag) :
    nativeDerivationCheck ax (Nat.pair s (Nat.pair tag u) + 1) = false := by
  rw [nativeDerivationCheck_eq_ruleCheck, ruleCheck_pair]
  have hneq : ∀ n < 10, tag ≠ n := by omega
  simp [ruleBodyCheck, hneq 0 (by omega), hneq 1 (by omega),
    hneq 2 (by omega), hneq 3 (by omega), hneq 4 (by omega),
    hneq 5 (by omega), hneq 6 (by omega), hneq 7 (by omega),
    hneq 8 (by omega), hneq 9 (by omega)]

theorem reject_wrong_endpoint (ax : ℕ → Bool) (d Γ : ℕ)
    (h : conclusionCode d ≠ Γ) : nativeDerivationOfCheck ax d Γ = false := by
  simp [nativeDerivationOfCheck, h]

theorem reject_malformed_sequent (ax : ℕ → Bool) (d : ℕ)
    (h : formulaSetCodeValid (conclusionCode d) = false) :
    nativeDerivationCheck ax d = false := by
  rw [nativeDerivationCheck_eq_ruleCheck]
  by_cases hd : d = 0 <;> simp [ruleCheck, hd, h]

set_option backward.isDefEq.respectTransparency false in
theorem accepted_universal_rule {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (s p d : ℕ)
    (hs : IsFormulaSet ℒₒᵣ s) (hp : formulaAllCode p ∈ s)
    (hd : nativeDerivationOfCheck ax d
      (sequentInsertCode (formulaFreeCode p) (sequentShiftCode s)) = true) :
    nativeDerivationCheck ax (Nat.pair s (Nat.pair 4 (Nat.pair p d)) + 1) = true := by
  have hp' : ^∀ p ∈ s := by simpa only [allCode_eq] using hp
  have hb : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp'
  have hd' := (nativeDerivationOfCheck_iff hax _ _).mp hd
  rw [insertCode_eq, formulaFreeCode_eq_free hb, sequentShiftCode_eq_setShift hs] at hd'
  apply (nativeDerivationCheck_iff hax _).mpr
  simpa [allIntro, nat_pair_eq] using Derivation.allIntro hp' hd'

set_option backward.isDefEq.respectTransparency false in
theorem accepted_shift_rule {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (d : ℕ)
    (hd : nativeDerivationCheck ax d = true) :
    nativeDerivationCheck ax
      (Nat.pair (sequentShiftCode (conclusionCode d)) (Nat.pair 7 d) + 1) = true := by
  have hd' := (nativeDerivationCheck_iff hax d).mp hd
  apply (nativeDerivationCheck_iff hax _).mpr
  rw [conclusionCode_eq_fstIdx, sequentShiftCode_eq_setShift hd'.isFormulaSet]
  simpa [shiftRule, nat_pair_eq] using
    Derivation.shiftRule (show DerivationOf S d (fstIdx d) from ⟨rfl, hd'⟩)

set_option backward.isDefEq.respectTransparency false in
theorem accepted_axiom_rule {ax : ℕ → Bool} {S : ArithmeticTheory} [S.Δ₁]
    (hax : AxiomAgreement ax S) (s p : ℕ)
    (hs : IsFormulaSet ℒₒᵣ s) (hp : p ∈ s) (ha : ax p = true) :
    nativeDerivationCheck ax (Nat.pair s (Nat.pair 9 p) + 1) = true := by
  apply (nativeDerivationCheck_iff hax _).mpr
  simpa [axm, nat_pair_eq] using
    Derivation.axm (T := S) hs hp ((hax p (hs p hp)).mp ha)

end FailureOfComposition.NativeProofChecker
