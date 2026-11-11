/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Arith.FixedFormulaNumeralSubstitution
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Primrec
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.CraigTrick
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.DerivabilityCondition.D1

/-!
# Numerical modus ponens with a coded sequent context

This module gives an explicit primitive-recursive proof-code constructor for
modus ponens in Foundation's bootstrapped one-sided calculus.  Its first
argument is the finite-set code of a sequent context; it is not a list of
assumptions.  The constructor retains that context in its conclusion.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open Arith.FixedFormulaNumeralSubstitution

namespace FailureOfComposition.NativeContextMP

open FFL.FirstOrder.Arithmetic.Bootstrapping

abbrev ArithmeticProposition := ArithmeticSemiproposition 0

/-- A numerical test for codes of arithmetic propositions.  Such propositions
may have free variables, but have no dangling bound variables. -/
def formulaCodeValid (a : ℕ) : Bool :=
  (decode₂ ArithmeticProposition a).isSome

theorem formulaCodeValid_iff_isFormula (a : ℕ) :
    formulaCodeValid a = true ↔ IsFormula ℒₒᵣ a := by
  constructor
  · intro h
    have h' : (decode₂ ArithmeticProposition a).isSome := by
      simpa [formulaCodeValid] using h
    rcases Option.isSome_iff_exists.mp h' with ⟨φ, hφ⟩
    have ha : encode φ = a := decode₂_eq_some.mp hφ
    rw [← ha]
    have hquote := Semiformula.quote_isSemiformula (V := ℕ) φ
    rw [Semiformula.quote_eq_encode_nat] at hquote
    exact hquote
  · intro h
    rcases h.sound with ⟨φ, hφ⟩
    have hencode : encode φ = a := by
      simpa [Semiformula.quote_eq_encode_nat] using hφ
    have hdecode : decode₂ ArithmeticProposition a = some φ :=
      decode₂_eq_some.mpr hencode
    simp [formulaCodeValid, hdecode]

/-- Total numerical negation used by the proof constructor.  It agrees with
Foundation negation on proposition codes and returns zero on every other
input. -/
def formulaNegTotalCode (a : ℕ) : ℕ :=
  if formulaCodeValid a then formulaNegCode a else 0

theorem primrecPred_formulaCodeValid :
    PrimrecPred fun a => formulaCodeValid a = true := by
  exact (Primrec.eq.comp
    (Primrec.option_isSome.comp
      (Primrec.decode₂ (α := ArithmeticProposition)))
    (Primrec.const true)).of_eq fun a => by simp [formulaCodeValid]

theorem primrec_formulaNegTotalCode : Primrec formulaNegTotalCode := by
  exact Primrec.ite primrecPred_formulaCodeValid primrec_formulaNegCode
    (Primrec.const 0)

theorem formulaNegTotalCode_eq_neg {a : ℕ} (ha : IsFormula ℒₒᵣ a) :
    formulaNegTotalCode a = neg ℒₒᵣ a := by
  rcases ha.sound with ⟨φ, rfl⟩
  have hvalid : formulaCodeValid (⌜φ⌝ : ℕ) = true :=
    (formulaCodeValid_iff_isFormula _).mpr (by simp)
  unfold formulaNegTotalCode
  simp only [hvalid, ↓reduceIte]
  calc
    formulaNegCode (⌜φ⌝ : ℕ) = encode (∼φ) := by
      rw [Semiformula.quote_eq_encode_nat]
      exact formulaNegCode_encode φ
    _ = (⌜∼φ⌝ : ℕ) := (Semiformula.quote_eq_encode_nat _).symm
    _ = neg ℒₒᵣ (⌜φ⌝ : ℕ) := by simp [Semiformula.quote_def]

theorem formulaNegTotalCode_eq_zero {a : ℕ} (ha : ¬IsFormula ℒₒᵣ a) :
    formulaNegTotalCode a = 0 := by
  simp [formulaNegTotalCode, formulaCodeValid_iff_isFormula, ha]

/-! ## Explicit numerical constructor -/

def sequentInsertCode (x s : ℕ) : ℕ :=
  if s / 2 ^ x % 2 = 1 then s else s + 2 ^ x

def formulaAndCode (a b : ℕ) : ℕ :=
  Nat.pair 4 (Nat.pair a b) + 1

def formulaOrCode (a b : ℕ) : ℕ :=
  Nat.pair 5 (Nat.pair a b) + 1

def axLCode (s a : ℕ) : ℕ :=
  Nat.pair s (Nat.pair 0 a) + 1

def wkRuleCode (s d : ℕ) : ℕ :=
  Nat.pair s (Nat.pair 6 d) + 1

def andIntroCode (s a b d₁ d₂ : ℕ) : ℕ :=
  Nat.pair s (Nat.pair 2 (Nat.pair a (Nat.pair b (Nat.pair d₁ d₂)))) + 1

def cutRuleCode (s a d₁ d₂ : ℕ) : ℕ :=
  Nat.pair s (Nat.pair 8 (Nat.pair a (Nat.pair d₁ d₂))) + 1

/-- The explicit context-preserving modus-ponens proof code.  The arguments
are, in order, the sequent-context code, antecedent formula code, consequent
formula code, implication derivation, and antecedent derivation. -/
def mpCtx (Γ a b e p : ℕ) : ℕ :=
  let na := formulaNegTotalCode a
  let i := formulaOrCode na b
  let nb := formulaNegTotalCode b
  let c := formulaAndCode a nb
  let sb := sequentInsertCode b Γ
  let si := sequentInsertCode i sb
  let sa := sequentInsertCode a sb
  let snb := sequentInsertCode nb sb
  let sc := sequentInsertCode c sb
  let sac := sequentInsertCode a sc
  let snbc := sequentInsertCode nb sc
  let de := wkRuleCode si e
  let dp₀ := wkRuleCode sa p
  let dem := axLCode snb b
  let dp₁ := wkRuleCode sac dp₀
  let dnb := wkRuleCode snbc dem
  let dc := andIntroCode sc a nb dp₁ dnb
  cutRuleCode sb i de dc

abbrev MPCtxArgs := ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ)

/-- Left-associated packing of `(Γ,a,b,e,p)` used by the joint primitive-
recursiveness theorem. -/
def mpCtxPacked (z : MPCtxArgs) : ℕ :=
  mpCtx z.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2

theorem primrec₂_sequentInsertCode : Primrec₂ sequentInsertCode := by
  have hpow : Primrec fun z : ℕ × ℕ => 2 ^ z.1 :=
    (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (Primrec.const 2) Primrec.fst
  have hc : PrimrecPred fun z : ℕ × ℕ => z.2 / 2 ^ z.1 % 2 = 1 :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.snd hpow)
        (Primrec.const 2))
      (Primrec.const 1)
  exact (Primrec.ite hc Primrec.snd
    (Primrec.nat_add.comp Primrec.snd hpow)).to₂

theorem primrec₂_formulaAndCode : Primrec₂ formulaAndCode := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 4)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd))).to₂

theorem primrec₂_formulaOrCode : Primrec₂ formulaOrCode := by
  exact (Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.const 5)
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd))).to₂

private theorem primrec_mpCtx_components :
    let Γ : MPCtxArgs → ℕ := fun z => z.1.1.1.1
    let a : MPCtxArgs → ℕ := fun z => z.1.1.1.2
    let b : MPCtxArgs → ℕ := fun z => z.1.1.2
    let e : MPCtxArgs → ℕ := fun z => z.1.2
    let p : MPCtxArgs → ℕ := fun z => z.2
    Primrec Γ ∧ Primrec a ∧ Primrec b ∧ Primrec e ∧ Primrec p := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

/-- Joint primitive recursiveness in the left-associated product
`((((Γ,a),b),e),p)`. -/
theorem primrec_mpCtxPacked : Primrec mpCtxPacked := by
  rcases primrec_mpCtx_components with ⟨hΓ, ha, hb, he, hp⟩
  have hna := primrec_formulaNegTotalCode.comp ha
  have hi := primrec₂_formulaOrCode.comp hna hb
  have hnb := primrec_formulaNegTotalCode.comp hb
  have hc := primrec₂_formulaAndCode.comp ha hnb
  have hsb := primrec₂_sequentInsertCode.comp hb hΓ
  have hsi := primrec₂_sequentInsertCode.comp hi hsb
  have hsa := primrec₂_sequentInsertCode.comp ha hsb
  have hsnb := primrec₂_sequentInsertCode.comp hnb hsb
  have hsc := primrec₂_sequentInsertCode.comp hc hsb
  have hsac := primrec₂_sequentInsertCode.comp ha hsc
  have hsnbc := primrec₂_sequentInsertCode.comp hnb hsc
  have hde := primrec_wkRule hsi he
  have hdp₀ := primrec_wkRule hsa hp
  have hdem := primrec_axL hsnb hb
  have hdp₁ := primrec_wkRule hsac hdp₀
  have hdnb := primrec_wkRule hsnbc hdem
  have hdc := primrec_andIntro hsc ha hnb hdp₁ hdnb
  exact (primrec_cutRule hsb hi hde hdc).of_eq fun z => by
    simp [mpCtxPacked, mpCtx, sequentInsertCode, formulaAndCode,
      formulaOrCode, axLCode, wkRuleCode, andIntroCode, cutRuleCode,
      Bootstrapping.axL, Bootstrapping.wkRule, Bootstrapping.andIntro,
      Bootstrapping.cutRule, nat_pair_eq]

/-! ## Model-internal value and exact arithmetic graph -/

/-- The model-internal counterpart of `formulaNegTotalCode`.  Its validity
guard is the exact Foundation predicate for proposition codes. -/
noncomputable def guardedNegValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (a : V) : V :=
  @ite V (IsFormula ℒₒᵣ a) (Classical.propDecidable _)
    (neg ℒₒᵣ a) 0

noncomputable def guardedNegGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y a.
    (!(isSemiformula ℒₒᵣ).sigma 0 a ∧ !(negGraph ℒₒᵣ) y a) ∨
    (¬!(isSemiformula ℒₒᵣ).pi 0 a ∧ y = 0)”

theorem guardedNegGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y a : V) :
    Semiformula.Evalb (M := V) ![y, a] guardedNegGraph.val ↔
      y = guardedNegValue a := by
  by_cases ha : IsFormula ℒₒᵣ a <;>
    simp [guardedNegGraph, guardedNegValue, ha,
      HierarchySymbol.Semiformula.val_sigma, neg.defined.iff,
      IsSemiformula.defined.iff]

/-- The structural operation represented by `mpCtxGraph`.  All arguments are
elements of the ambient arithmetic model, rather than external naturals. -/
noncomputable def mpCtxValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (Γ a b e p : V) : V :=
  let na := guardedNegValue a
  let i := na ^⋎ b
  let nb := guardedNegValue b
  let c := a ^⋏ nb
  let sb := insert b Γ
  let si := insert i sb
  let sa := insert a sb
  let snb := insert nb sb
  let sc := insert c sb
  let sac := insert a sc
  let snbc := insert nb sc
  let de := wkRule si e
  let dp₀ := wkRule sa p
  let dem := axL snb b
  let dp₁ := wkRule sac dp₀
  let dnb := wkRule snbc dem
  let dc := andIntro sc a nb dp₁ dnb
  cutRule sb i de dc

/-- Exact compositional graph of `mpCtxValue`.  The output is coordinate zero;
the remaining coordinates are `(Γ,a,b,e,p)` in that order. -/
noncomputable def mpCtxGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “y Γ a b e p.
    ∃ na, !guardedNegGraph na a ∧
    ∃ i, !qqOrDef i na b ∧
    ∃ nb, !guardedNegGraph nb b ∧
    ∃ c, !qqAndDef c a nb ∧
    ∃ sb, !insertDef sb b Γ ∧
    ∃ si, !insertDef si i sb ∧
    ∃ sa, !insertDef sa a sb ∧
    ∃ snb, !insertDef snb nb sb ∧
    ∃ sc, !insertDef sc c sb ∧
    ∃ sac, !insertDef sac a sc ∧
    ∃ snbc, !insertDef snbc nb sc ∧
    ∃ de, !wkRuleGraph de si e ∧
    ∃ dp0, !wkRuleGraph dp0 sa p ∧
    ∃ dem, !axLGraph dem snb b ∧
    ∃ dp1, !wkRuleGraph dp1 sac dp0 ∧
    ∃ dnb, !wkRuleGraph dnb snbc dem ∧
    ∃ dc, !andIntroGraph dc sc a nb dp1 dnb ∧
      !cutRuleGraph y sb i de dc”

theorem mpCtxGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y Γ a b e p : V) :
    Semiformula.Evalb (M := V) ![y, Γ, a, b, e, p] mpCtxGraph.val ↔
      y = mpCtxValue Γ a b e p := by
  simp [mpCtxGraph, mpCtxValue, guardedNegGraph_iff]

theorem mpCtxGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Γ a b e p : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, Γ, a, b, e, p]
      mpCtxGraph.val :=
  ⟨mpCtxValue Γ a b e p, (mpCtxGraph_iff _ _ _ _ _ _).mpr rfl⟩

theorem mpCtxGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z Γ a b e p : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, a, b, e, p]
      mpCtxGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, Γ, a, b, e, p]
      mpCtxGraph.val) :
    y = z :=
  (mpCtxGraph_iff y Γ a b e p).mp hy |>.trans
    ((mpCtxGraph_iff z Γ a b e p).mp hz).symm

/-! ## Preservation of the internal derivation predicate -/

/-- The validity guard disappears on formula codes. -/
theorem guardedNegValue_eq_neg
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {a : V} (ha : IsFormula ℒₒᵣ a) :
    guardedNegValue a = neg ℒₒᵣ a := by
  simp [guardedNegValue, ha]

/-- The structural operation preserves Foundation's exact `DerivationOf`
predicate in every model of PA.  No semantic soundness or standardness
hypothesis is used. -/
theorem derivationOf_mpCtxValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {Γ a b e p : V}
    (he : DerivationOf S e (insert (imp ℒₒᵣ a b) Γ))
    (hp : DerivationOf S p (insert a Γ)) :
    DerivationOf S (mpCtxValue Γ a b e p) (insert b Γ) := by
  have hiFormula : IsFormula ℒₒᵣ (imp ℒₒᵣ a b) :=
    (IsFormulaSet.insert_iff.mp he.isFormulaSet).1
  have ha : IsFormula ℒₒᵣ a := (IsSemiformula.imp.mp hiFormula).1
  have hb : IsFormula ℒₒᵣ b := (IsSemiformula.imp.mp hiFormula).2
  have hΓ : IsFormulaSet ℒₒᵣ Γ :=
    (IsFormulaSet.insert_iff.mp he.isFormulaSet).2
  let na := neg ℒₒᵣ a
  let i := na ^⋎ b
  let nb := neg ℒₒᵣ b
  let c := a ^⋏ nb
  let sb := insert b Γ
  let si := insert i sb
  let sa := insert a sb
  let snb := insert nb sb
  let sc := insert c sb
  let sac := insert a sc
  let snbc := insert nb sc
  let de := wkRule si e
  let dp₀ := wkRule sa p
  let dem := axL snb b
  let dp₁ := wkRule sac dp₀
  let dnb := wkRule snbc dem
  let dc := andIntro sc a nb dp₁ dnb
  have hsi : IsFormulaSet ℒₒᵣ si := by
    simp [si, sb, i, na, ha, hb, hΓ]
  have hsa : IsFormulaSet ℒₒᵣ sa := by
    simp [sa, sb, ha, hb, hΓ]
  have hsnb : IsFormulaSet ℒₒᵣ snb := by
    simp [snb, sb, nb, hb, hΓ]
  have hsac : IsFormulaSet ℒₒᵣ sac := by
    simp [sac, sc, c, nb, sb, ha, hb, hΓ]
  have hsnbc : IsFormulaSet ℒₒᵣ snbc := by
    simp [snbc, sc, c, nb, sb, ha, hb, hΓ]
  have hde : DerivationOf S de si := by
    refine ⟨by simp [de], Derivation.wkRule hsi ?_ he⟩
    intro q hq
    rcases (by simpa [i, na, Bootstrapping.imp] using hq :
        q = i ∨ q ∈ Γ) with (rfl | hq)
    · simp [si]
    · simp [si, sb, hq]
  have hdp₀ : DerivationOf S dp₀ sa := by
    refine ⟨by simp [dp₀], Derivation.wkRule hsa ?_ hp⟩
    intro q hq
    rcases (by simpa using hq : q = a ∨ q ∈ Γ) with (rfl | hq)
    · simp [sa]
    · simp [sa, sb, hq]
  have hdem : DerivationOf S dem snb := by
    refine ⟨by simp [dem], Derivation.axL hsnb ?_ ?_⟩
    · simp [snb, sb]
    · simp [snb, nb]
  have hdp₁ : DerivationOf S dp₁ sac := by
    refine ⟨by simp [dp₁], Derivation.wkRule hsac ?_ hdp₀⟩
    intro q hq
    rcases (by simpa [sa] using hq : q = a ∨ q ∈ sb) with (rfl | hq)
    · simp [sac]
    · simp [sac, sc, hq]
  have hdnb : DerivationOf S dnb snbc := by
    refine ⟨by simp [dnb], Derivation.wkRule hsnbc ?_ hdem⟩
    intro q hq
    rcases (by simpa [snb] using hq : q = nb ∨ q ∈ sb) with (rfl | hq)
    · simp [snbc]
    · simp [snbc, sc, hq]
  have hdc : DerivationOf S dc sc := by
    exact ⟨by simp [dc], Derivation.andIntro (by simp [sc, c]) hdp₁ hdnb⟩
  have hneg : neg ℒₒᵣ i = c := by
    simp [i, c, na, nb, ha.isUFormula, hb.isUFormula]
  have hdc' : DerivationOf S dc (insert (neg ℒₒᵣ i) sb) := by
    simpa [sc, hneg] using hdc
  have hcut : DerivationOf S (cutRule sb i de dc) sb :=
    ⟨by simp, Derivation.cutRule hde hdc'⟩
  simpa [mpCtxValue, guardedNegValue, ha, hb, na, i, nb, c, sb, si,
    sa, snb, sc, sac, snbc, de, dp₀, dem, dp₁, dnb, dc,
    Bootstrapping.imp] using hcut

/-- The exact graph transfers internal input derivations to the internal
output derivation formula. -/
theorem mpCtxGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {y Γ a b e p : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, a, b, e, p]
      mpCtxGraph.val)
    (he : Semiformula.Evalb (M := V)
      ![e, insert (imp ℒₒᵣ a b) Γ] (derivationOf S).sigma.val)
    (hp : Semiformula.Evalb (M := V)
      ![p, insert a Γ] (derivationOf S).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert b Γ] (derivationOf S).sigma.val := by
  have hy' : y = mpCtxValue Γ a b e p :=
    (mpCtxGraph_iff y Γ a b e p).mp hy
  have he' : DerivationOf S e (insert (imp ℒₒᵣ a b) Γ) := by
    simpa using he
  have hp' : DerivationOf S p (insert a Γ) := by
    simpa using hp
  rw [hy']
  simpa using derivationOf_mpCtxValue S he' hp'

/-! ## Agreement with the numerical constructor -/

private theorem guardedNegValue_nat (a : ℕ) :
    guardedNegValue a = formulaNegTotalCode a := by
  by_cases ha : IsFormula ℒₒᵣ a
  · rw [guardedNegValue_eq_neg ha, formulaNegTotalCode_eq_neg ha]
  · simp [guardedNegValue, formulaNegTotalCode_eq_zero ha, ha]

private theorem insert_nat_eq_sequentInsertCode (x s : ℕ) :
    insert x s = sequentInsertCode x s := by
  simp [sequentInsertCode, nat_insert_eq]

private theorem qqAnd_nat_eq_formulaAndCode (a b : ℕ) :
    a ^⋏ b = formulaAndCode a b := by
  simp [formulaAndCode, Bootstrapping.qqAnd, nat_pair_eq]

private theorem qqOr_nat_eq_formulaOrCode (a b : ℕ) :
    a ^⋎ b = formulaOrCode a b := by
  simp [formulaOrCode, Bootstrapping.qqOr, nat_pair_eq]

private theorem axL_nat_eq_axLCode (s a : ℕ) :
    axL s a = axLCode s a := by
  simp [axLCode, Bootstrapping.axL, nat_pair_eq]

private theorem wkRule_nat_eq_wkRuleCode (s d : ℕ) :
    wkRule s d = wkRuleCode s d := by
  simp [wkRuleCode, Bootstrapping.wkRule, nat_pair_eq]

private theorem andIntro_nat_eq_andIntroCode (s a b d₁ d₂ : ℕ) :
    andIntro s a b d₁ d₂ = andIntroCode s a b d₁ d₂ := by
  simp [andIntroCode, Bootstrapping.andIntro, nat_pair_eq]

private theorem cutRule_nat_eq_cutRuleCode (s a d₁ d₂ : ℕ) :
    cutRule s a d₁ d₂ = cutRuleCode s a d₁ d₂ := by
  simp [cutRuleCode, Bootstrapping.cutRule, nat_pair_eq]

/-- In the standard model, the internal structural operation agrees with the
explicit numerical program on every input, including malformed formula
codes. -/
theorem mpCtxValue_nat (Γ a b e p : ℕ) :
    mpCtxValue Γ a b e p = mpCtx Γ a b e p := by
  simp only [mpCtxValue, mpCtx, guardedNegValue_nat,
    qqOr_nat_eq_formulaOrCode, qqAnd_nat_eq_formulaAndCode,
    insert_nat_eq_sequentInsertCode, wkRule_nat_eq_wkRuleCode,
    axL_nat_eq_axLCode, andIntro_nat_eq_andIntroCode,
    cutRule_nat_eq_cutRuleCode]

/-- Standard-model characterization of the arithmetic graph. -/
theorem mpCtxGraph_nat_iff (y Γ a b e p : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, Γ, a, b, e, p] mpCtxGraph.val ↔
      y = mpCtx Γ a b e p := by
  rw [mpCtxGraph_iff, mpCtxValue_nat]

/-! ## Standard and Craig specializations -/

/-- Numerical preservation of the exact Foundation derivation predicate. -/
theorem derivationOf_mpCtx
    (S : ArithmeticTheory) [S.Δ₁]
    {Γ a b e p : ℕ}
    (he : DerivationOf S e (insert (imp ℒₒᵣ a b) Γ))
    (hp : DerivationOf S p (insert a Γ)) :
    DerivationOf S (mpCtx Γ a b e p) (insert b Γ) := by
  rw [← mpCtxValue_nat]
  exact derivationOf_mpCtxValue S he hp

/-- Empty-context modus ponens, stated with Foundation's `Proof` predicate. -/
theorem proof_mpCtx
    (S : ArithmeticTheory) [S.Δ₁]
    {a b e p : ℕ}
    (he : Proof S e (imp ℒₒᵣ a b))
    (hp : Proof S p a) :
    Proof S (mpCtx 0 a b e p) b := by
  have he' : DerivationOf S e (insert (imp ℒₒᵣ a b) 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using he
  have hp' : DerivationOf S p (insert a 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using hp
  have h := derivationOf_mpCtx S he' hp'
  simpa [Proof, singleton_eq_insert, emptyset_def] using h

/-- A nonempty-context specialization.  The singleton context containing `c`
is retained verbatim in the output sequent. -/
theorem derivationOf_mpCtx_singleton
    (S : ArithmeticTheory) [S.Δ₁]
    {c a b e p : ℕ}
    (he : DerivationOf S e
      (insert (imp ℒₒᵣ a b) (insert c 0)))
    (hp : DerivationOf S p (insert a (insert c 0))) :
    DerivationOf S (mpCtx (insert c 0) a b e p)
      (insert b (insert c 0)) :=
  derivationOf_mpCtx S he hp

/-- Internal syntactic preservation for Foundation's Craig companion of an
external recursively enumerable arithmetic theory. -/
theorem craig_mpCtxGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (T : ArithmeticTheory) [T.RE]
    {y Γ a b e p : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, a, b, e, p]
      mpCtxGraph.val)
    (he : Semiformula.Evalb (M := V)
      ![e, insert (imp ℒₒᵣ a b) Γ]
      (derivationOf T.craig).sigma.val)
    (hp : Semiformula.Evalb (M := V)
      ![p, insert a Γ] (derivationOf T.craig).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert b Γ] (derivationOf T.craig).sigma.val :=
  mpCtxGraph_preserves_derivationOf T.craig hy he hp

/-- Standard theorem-set adequacy of the Craig companion.  The first
equivalence is Foundation's ordinary/internal proof-coding theorem; the
second is its established equivalence `T ≊ T.craig`. -/
theorem craig_provable_iff
    (T : ArithmeticTheory) [T.RE] (σ : ArithmeticSentence) :
    Provable T.craig (⌜σ⌝ : ℕ) ↔ T ⊢ σ := by
  rw [provable_iff_provable]
  exact (Entailment.Equiv.iff.mp
    (inferInstance : T ≊ T.craig) σ).symm

end FailureOfComposition.NativeContextMP
