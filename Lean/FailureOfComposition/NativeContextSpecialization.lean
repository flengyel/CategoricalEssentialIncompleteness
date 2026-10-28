/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import FailureOfComposition.NativeContextMP
import FailureOfComposition.NativeSubstitution

/-!
# Numerical universal specialization with a coded sequent context

The external inputs are natural-number codes.  The context `Γ` is
Foundation's finite-set code for a one-sided sequent, `p` is an arithmetic
formula body of bound arity one, `t` is an arithmetic term of bound arity
zero, and `d` is a derivation code.  Free variables may occur in `p` and `t`.

The total program `specializeCtx Γ p t d` returns zero unless the term and
formula-body codes have their stated arities.  On valid syntax it constructs
one explicit proof tree, using weakening, a logical axiom, existential
introduction, and cut.  It does not test the context or derivation code.
-/

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open Arith.FixedFormulaNumeralSubstitution

namespace FailureOfComposition.NativeContextSpecialization

open FFL.FirstOrder.Arithmetic.Bootstrapping
open FailureOfComposition.NativeContextMP
open FailureOfComposition.NativeSubstitution

/-! ## Explicit numerical constructor -/

def formulaAllCode (p : ℕ) : ℕ :=
  Nat.pair 6 p + 1

def formulaExistsCode (p : ℕ) : ℕ :=
  Nat.pair 7 p + 1

def exsIntroCode (s p t d : ℕ) : ℕ :=
  Nat.pair s (Nat.pair 5 (Nat.pair p (Nat.pair t d))) + 1

/-- The explicit context-preserving universal-specialization program.  Its
arguments are the finite-set context code, formula-body code, term code, and
input derivation code, in that order. -/
def specializeCtx (Γ p t d : ℕ) : ℕ :=
  if termCodeValid t && formulaBodyCodeValid p then
    let u := subst1Code t p
    let np := formulaNegCode p
    let A := formulaAllCode p
    let NA := formulaExistsCode np
    let nu := formulaNegCode u
    let s := sequentInsertCode u Γ
    let sl := sequentInsertCode A s
    let sr := sequentInsertCode NA s
    let sm := sequentInsertCode nu sr
    let dl := wkRuleCode sl d
    let dm := axLCode sm u
    let dr := exsIntroCode sr np t dm
    cutRuleCode s A dl dr
  else 0

abbrev SpecializeCtxArgs := (((ℕ × ℕ) × ℕ) × ℕ)

/-- Left-associated packing `(((Γ,p),t),d)` for the joint primitive-
recursiveness theorem. -/
def specializeCtxPacked (z : SpecializeCtxArgs) : ℕ :=
  specializeCtx z.1.1.1 z.1.1.2 z.1.2 z.2

theorem primrec_formulaAllCode : Primrec formulaAllCode := by
  exact Primrec.succ.comp <|
    Primrec₂.natPair.comp (Primrec.const 6) Primrec.id

theorem primrec_formulaExistsCode : Primrec formulaExistsCode := by
  exact Primrec.succ.comp <|
    Primrec₂.natPair.comp (Primrec.const 7) Primrec.id

private theorem primrec_specializeCtx_components :
    let Γ : SpecializeCtxArgs → ℕ := fun z => z.1.1.1
    let p : SpecializeCtxArgs → ℕ := fun z => z.1.1.2
    let t : SpecializeCtxArgs → ℕ := fun z => z.1.2
    let d : SpecializeCtxArgs → ℕ := fun z => z.2
    Primrec Γ ∧ Primrec p ∧ Primrec t ∧ Primrec d := by
  exact ⟨Primrec.fst.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst),
    Primrec.snd.comp Primrec.fst, Primrec.snd⟩

/-- Joint primitive recursiveness in the context, body, term, and derivation
code, packed as `(((Γ,p),t),d)`. -/
theorem primrec_specializeCtxPacked : Primrec specializeCtxPacked := by
  rcases primrec_specializeCtx_components with ⟨hΓ, hp, ht, hd⟩
  have hvalid : PrimrecPred fun z : SpecializeCtxArgs =>
      termCodeValid (z.1.2) = true ∧
        formulaBodyCodeValid (z.1.1.2) = true :=
    PrimrecPred.and
      (primrecPred_termCodeValid.comp ht)
      (primrecPred_formulaBodyCodeValid.comp hp)
  have hu := primrec₂_subst1Code.comp ht hp
  have hnp := primrec_formulaNegCode.comp hp
  have hA := primrec_formulaAllCode.comp hp
  have hNA := primrec_formulaExistsCode.comp hnp
  have hnu := primrec_formulaNegCode.comp hu
  have hs := primrec₂_sequentInsertCode.comp hu hΓ
  have hsl := primrec₂_sequentInsertCode.comp hA hs
  have hsr := primrec₂_sequentInsertCode.comp hNA hs
  have hsm := primrec₂_sequentInsertCode.comp hnu hsr
  have hdl := primrec_wkRule hsl hd
  have hdm := primrec_axL hsm hu
  have hdr := primrec_exsIntro hsr hnp ht hdm
  have hresult := primrec_cutRule hs hA hdl hdr
  exact (Primrec.ite hvalid hresult (Primrec.const 0)).of_eq fun z => by
    simp [specializeCtxPacked, specializeCtx, Bool.and_eq_true,
      formulaAllCode, formulaExistsCode, exsIntroCode,
      axLCode, wkRuleCode, cutRuleCode,
      Bootstrapping.axL, Bootstrapping.exsIntro,
      Bootstrapping.wkRule, Bootstrapping.cutRule, nat_pair_eq]
    rfl

/-! ## Model-internal value and exact graph -/

/-- The internal structural operation.  Its arguments and output are elements
of the ambient PA model, not external natural numbers. -/
noncomputable def specializeCtxValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Γ p t d : V) : V :=
  @ite V (IsSemiterm ℒₒᵣ 0 t ∧ IsSemiformula ℒₒᵣ 1 p)
    (Classical.propDecidable _)
    (let u := subst1Value t p
     let np := neg ℒₒᵣ p
     let A := ^∀ p
     let NA := ^∃ np
     let nu := neg ℒₒᵣ u
     let s := insert u Γ
     let sl := insert A s
     let sr := insert NA s
     let sm := insert nu sr
     let dl := wkRule sl d
     let dm := axL sm u
     let dr := exsIntro sr np t dm
     cutRule s A dl dr)
    0

/-- The arithmetic term-validity formula used in the fully syntactic
preservation statement. -/
noncomputable def termValidGraph : 𝚺₁.Semisentence 1 := .mkSigma
  “t. !(isSemiterm ℒₒᵣ).sigma 0 t”

theorem termValidGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t : V) :
    Semiformula.Evalb (M := V) ![t] termValidGraph.val ↔
      IsSemiterm ℒₒᵣ 0 t := by
  simp [termValidGraph, HierarchySymbol.Semiformula.val_sigma,
    IsSemiterm.defined.iff]

/-- Compositional graph of `specializeCtxValue`, in output-first coordinate
order `(y,Γ,p,t,d)`. -/
noncomputable def specializeCtxGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “y Γ p t d.
    ((!(isSemiterm ℒₒᵣ).sigma 0 t ∧
      !(isSemiformula ℒₒᵣ).sigma 1 p ∧
      ∃ u, !subst1Graph u t p ∧
      ∃ np, !(negGraph ℒₒᵣ) np p ∧
      ∃ A, !qqAllDef A p ∧
      ∃ NA, !qqExsDef NA np ∧
      ∃ nu, !(negGraph ℒₒᵣ) nu u ∧
      ∃ s, !insertDef s u Γ ∧
      ∃ sl, !insertDef sl A s ∧
      ∃ sr, !insertDef sr NA s ∧
      ∃ sm, !insertDef sm nu sr ∧
      ∃ dl, !wkRuleGraph dl sl d ∧
      ∃ dm, !axLGraph dm sm u ∧
      ∃ dr, !exsIntroGraph dr sr np t dm ∧
        !cutRuleGraph y s A dl dr) ∨
    ((¬!(isSemiterm ℒₒᵣ).pi 0 t ∨
      ¬!(isSemiformula ℒₒᵣ).pi 1 p) ∧ y = 0))”

theorem specializeCtxGraph_iff
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (y Γ p t d : V) :
    Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
        specializeCtxGraph.val ↔
      y = specializeCtxValue Γ p t d := by
  by_cases ht : IsSemiterm ℒₒᵣ 0 t <;>
    by_cases hp : IsSemiformula ℒₒᵣ 1 p <;>
    simp [specializeCtxGraph, specializeCtxValue, ht, hp,
      HierarchySymbol.Semiformula.val_sigma,
      IsSemiterm.defined.iff, IsSemiformula.defined.iff,
      subst1Graph_iff]

theorem specializeCtxGraph_total
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Γ p t d : V) :
    ∃ y : V, Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
      specializeCtxGraph.val :=
  ⟨specializeCtxValue Γ p t d,
    (specializeCtxGraph_iff _ _ _ _ _).mpr rfl⟩

theorem specializeCtxGraph_functional
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {y z Γ p t d : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
      specializeCtxGraph.val)
    (hz : Semiformula.Evalb (M := V) ![z, Γ, p, t, d]
      specializeCtxGraph.val) :
    y = z :=
  (specializeCtxGraph_iff y Γ p t d).mp hy |>.trans
    ((specializeCtxGraph_iff z Γ p t d).mp hz).symm

/-! ## Preservation of the exact derivation predicate -/

/-- The explicit proof tree preserves an arbitrary finite one-sided sequent
context.  Body and context well-formedness are consequences of the input
derivation. -/
theorem derivationOf_specializeCtxValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {Γ p t d : V}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : DerivationOf S d (insert (^∀ p) Γ)) :
    DerivationOf S (specializeCtxValue Γ p t d)
      (insert (substs1 ℒₒᵣ t p) Γ) := by
  have hAFormula : IsFormula ℒₒᵣ (^∀ p) :=
    (IsFormulaSet.insert_iff.mp hd.isFormulaSet).1
  have hp : IsSemiformula ℒₒᵣ 1 p := by
    simpa using hAFormula
  have hΓ : IsFormulaSet ℒₒᵣ Γ :=
    (IsFormulaSet.insert_iff.mp hd.isFormulaSet).2
  let u := substs1 ℒₒᵣ t p
  let np := neg ℒₒᵣ p
  let A := ^∀ p
  let NA := ^∃ np
  let nu := neg ℒₒᵣ u
  let s := insert u Γ
  let sl := insert A s
  let sr := insert NA s
  let sm := insert nu sr
  let dl := wkRule sl d
  let dm := axL sm u
  let dr := exsIntro sr np t dm
  have hu : IsFormula ℒₒᵣ u := hp.substs1 ht
  have hsl : IsFormulaSet ℒₒᵣ sl := by
    simp [sl, s, A, hu, hp, hΓ]
  have hsm : IsFormulaSet ℒₒᵣ sm := by
    simp [sm, sr, s, NA, np, nu, hu, hp, hΓ]
  have hdl : DerivationOf S dl sl := by
    refine ⟨by simp [dl], Derivation.wkRule hsl ?_ hd⟩
    intro q hq
    rcases (by simpa [A] using hq : q = A ∨ q ∈ Γ) with (rfl | hq)
    · simp [sl]
    · simp [sl, s, hq]
  have hdm : DerivationOf S dm sm := by
    refine ⟨by simp [dm], Derivation.axL hsm ?_ ?_⟩
    · simp [sm, sr, s]
    · simp [sm, nu]
  have hsubNeg : substs1 ℒₒᵣ t np = nu := by
    have h := subst1Value_neg (V := V) ht hp
    rw [subst1Value_eq_substs1 ht hp.neg,
      subst1Value_eq_substs1 ht hp] at h
    simpa [np, nu, u] using h
  have hdm' : DerivationOf S dm
      (insert (substs1 ℒₒᵣ t np) sr) := by
    simpa [sm, hsubNeg] using hdm
  have hdr : DerivationOf S dr sr := by
    refine ⟨by simp [dr], Derivation.exsIntro ?_ ?_ hdm'⟩
    · simp [sr, NA]
    · simpa using ht
  have hnegAll : neg ℒₒᵣ A = NA := by
    simp [A, NA, np, hp.isUFormula]
  have hdr' : DerivationOf S dr (insert (neg ℒₒᵣ A) s) := by
    simpa [sr, hnegAll] using hdr
  have hcut : DerivationOf S (cutRule s A dl dr) s :=
    ⟨by simp, Derivation.cutRule hdl hdr'⟩
  simpa [specializeCtxValue, ht, hp,
    subst1Value_eq_substs1 ht hp,
    u, np, A, NA, nu, s, sl, sr, sm, dl, dm, dr] using hcut

/-- Graph-level preservation with semantic hypotheses for term validity and
the exact internal derivation predicate. -/
theorem specializeCtxGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {y Γ p t d : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
      specializeCtxGraph.val)
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : Semiformula.Evalb (M := V)
      ![d, insert (^∀ p) Γ] (derivationOf S).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert (substs1 ℒₒᵣ t p) Γ]
      (derivationOf S).sigma.val := by
  have hy' : y = specializeCtxValue Γ p t d :=
    (specializeCtxGraph_iff y Γ p t d).mp hy
  have hd' : DerivationOf S d (insert (^∀ p) Γ) := by
    simpa using hd
  rw [hy']
  simpa using derivationOf_specializeCtxValue S ht hd'

/-- The same preservation law with term validity stated by evaluation of its
arithmetic formula. -/
theorem specializeCtxGraph_preserves_derivationOf_arith
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {y Γ p t d : V} :
    Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
        specializeCtxGraph.val →
    Semiformula.Evalb (M := V) ![t] termValidGraph.val →
    Semiformula.Evalb (M := V)
        ![d, insert (^∀ p) Γ] (derivationOf S).sigma.val →
    Semiformula.Evalb (M := V)
        ![y, insert (substs1 ℒₒᵣ t p) Γ]
        (derivationOf S).sigma.val := by
  intro hy ht hd
  exact specializeCtxGraph_preserves_derivationOf S hy
    ((termValidGraph_iff t).mp ht) hd

/-! ## Agreement with the numerical program -/

private theorem formulaNegCode_eq_neg {n p : ℕ}
    (hp : IsSemiformula ℒₒᵣ n p) :
    formulaNegCode p = neg ℒₒᵣ p := by
  rcases hp.sound with ⟨φ, rfl⟩
  calc
    formulaNegCode (⌜φ⌝ : ℕ) = encode (∼φ) := by
      rw [Semiformula.quote_eq_encode_nat]
      exact formulaNegCode_encode φ
    _ = (⌜∼φ⌝ : ℕ) := (Semiformula.quote_eq_encode_nat _).symm
    _ = neg ℒₒᵣ (⌜φ⌝ : ℕ) := by
      simp [Semiformula.quote_def]

private theorem qqAll_nat_eq_formulaAllCode (p : ℕ) :
    (^∀ p : ℕ) = formulaAllCode p := by
  simp [formulaAllCode, Bootstrapping.qqAll, nat_pair_eq]

private theorem qqExs_nat_eq_formulaExistsCode (p : ℕ) :
    (^∃ p : ℕ) = formulaExistsCode p := by
  simp [formulaExistsCode, Bootstrapping.qqExs, nat_pair_eq]

private theorem insert_nat_eq_sequentInsertCode (x s : ℕ) :
    insert x s = sequentInsertCode x s := by
  simp [sequentInsertCode, nat_insert_eq]

private theorem axL_nat_eq_axLCode (s a : ℕ) :
    axL s a = axLCode s a := by
  simp [axLCode, Bootstrapping.axL, nat_pair_eq]

private theorem exsIntro_nat_eq_exsIntroCode (s p t d : ℕ) :
    exsIntro s p t d = exsIntroCode s p t d := by
  simp [exsIntroCode, Bootstrapping.exsIntro, nat_pair_eq]

private theorem wkRule_nat_eq_wkRuleCode (s d : ℕ) :
    wkRule s d = wkRuleCode s d := by
  simp [wkRuleCode, Bootstrapping.wkRule, nat_pair_eq]

private theorem cutRule_nat_eq_cutRuleCode (s a d₁ d₂ : ℕ) :
    cutRule s a d₁ d₂ = cutRuleCode s a d₁ d₂ := by
  simp [cutRuleCode, Bootstrapping.cutRule, nat_pair_eq]

/-- Entire-domain agreement, including invalid syntax and malformed context
or derivation codes. -/
theorem specializeCtxValue_nat (Γ p t d : ℕ) :
    specializeCtxValue Γ p t d = specializeCtx Γ p t d := by
  by_cases ht : IsSemiterm ℒₒᵣ 0 t
  · by_cases hp : IsSemiformula ℒₒᵣ 1 p
    · have hu : IsSemiformula ℒₒᵣ 0 (subst1Code t p) := by
        rw [← subst1Value_nat]
        exact subst1Value_isSemiformula ht hp
      simp [specializeCtxValue, specializeCtx, ht, hp,
        termCodeValid_iff_isSemiterm,
        formulaBodyCodeValid_iff_isSemiformula,
        subst1Value_nat, formulaNegCode_eq_neg hp,
        formulaNegCode_eq_neg hu,
        qqAll_nat_eq_formulaAllCode,
        qqExs_nat_eq_formulaExistsCode,
        insert_nat_eq_sequentInsertCode,
        axL_nat_eq_axLCode, exsIntro_nat_eq_exsIntroCode,
        wkRule_nat_eq_wkRuleCode, cutRule_nat_eq_cutRuleCode]
    · simp [specializeCtxValue, specializeCtx, ht, hp,
        termCodeValid_iff_isSemiterm,
        formulaBodyCodeValid_iff_isSemiformula]
  · simp [specializeCtxValue, specializeCtx, ht,
      termCodeValid_iff_isSemiterm]

/-- Standard-model characterization of the graph on every tuple. -/
theorem specializeCtxGraph_nat_iff (y Γ p t d : ℕ) :
    Semiformula.Evalb (M := ℕ) ![y, Γ, p, t, d]
        specializeCtxGraph.val ↔
      y = specializeCtx Γ p t d := by
  rw [specializeCtxGraph_iff, specializeCtxValue_nat]

/-! ## Standard, empty-context, singleton, and Craig applications -/

theorem derivationOf_specializeCtx
    (S : ArithmeticTheory) [S.Δ₁]
    {Γ p t d : ℕ}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : DerivationOf S d (insert (^∀ p) Γ)) :
    DerivationOf S (specializeCtx Γ p t d)
      (insert (substs1 ℒₒᵣ t p) Γ) := by
  rw [← specializeCtxValue_nat]
  exact derivationOf_specializeCtxValue S ht hd

theorem proof_specializeCtxValue
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {p t d : V}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : Proof S d (^∀ p)) :
    Proof S (specializeCtxValue 0 p t d) (substs1 ℒₒᵣ t p) := by
  have hd' : DerivationOf S d (insert (^∀ p) 0) := by
    simpa [Proof, singleton_eq_insert, emptyset_def] using hd
  have h := derivationOf_specializeCtxValue S ht hd'
  simpa [Proof, singleton_eq_insert, emptyset_def] using h

theorem proof_specializeCtx
    (S : ArithmeticTheory) [S.Δ₁]
    {p t d : ℕ}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : Proof S d (^∀ p)) :
    Proof S (specializeCtx 0 p t d) (substs1 ℒₒᵣ t p) := by
  rw [← specializeCtxValue_nat]
  exact proof_specializeCtxValue S ht hd

theorem derivationOf_specializeCtxValue_singleton
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (S : ArithmeticTheory) [S.Δ₁]
    {c p t d : V}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : DerivationOf S d (insert (^∀ p) (insert c 0))) :
    DerivationOf S (specializeCtxValue (insert c 0) p t d)
      (insert (substs1 ℒₒᵣ t p) (insert c 0)) :=
  derivationOf_specializeCtxValue S ht hd

theorem derivationOf_specializeCtx_singleton
    (S : ArithmeticTheory) [S.Δ₁]
    {c p t d : ℕ}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : DerivationOf S d (insert (^∀ p) (insert c 0))) :
    DerivationOf S (specializeCtx (insert c 0) p t d)
      (insert (substs1 ℒₒᵣ t p) (insert c 0)) :=
  derivationOf_specializeCtx S ht hd

/-- Internal syntactic preservation for Foundation's Craig companion of an
external recursively enumerable arithmetic theory. -/
theorem craig_specializeCtxGraph_preserves_derivationOf
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (T : ArithmeticTheory) [T.RE]
    {y Γ p t d : V}
    (hy : Semiformula.Evalb (M := V) ![y, Γ, p, t, d]
      specializeCtxGraph.val)
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : Semiformula.Evalb (M := V)
      ![d, insert (^∀ p) Γ]
      (derivationOf T.craig).sigma.val) :
    Semiformula.Evalb (M := V)
      ![y, insert (substs1 ℒₒᵣ t p) Γ]
      (derivationOf T.craig).sigma.val :=
  specializeCtxGraph_preserves_derivationOf T.craig hy ht hd

theorem craig_proof_specializeCtx
    (T : ArithmeticTheory) [T.RE]
    {p t d : ℕ}
    (ht : IsSemiterm ℒₒᵣ 0 t)
    (hd : Proof T.craig d (^∀ p)) :
    Proof T.craig (specializeCtx 0 p t d) (substs1 ℒₒᵣ t p) :=
  proof_specializeCtx T.craig ht hd

/-- Standard theorem-set adequacy is inherited from Foundation's existing
Craig companion; it is separate from internal graph preservation. -/
theorem craig_provable_iff
    (T : ArithmeticTheory) [T.RE] (σ : ArithmeticSentence) :
    Provable T.craig (⌜σ⌝ : ℕ) ↔ T ⊢ σ :=
  NativeContextMP.craig_provable_iff T σ

end FailureOfComposition.NativeContextSpecialization
