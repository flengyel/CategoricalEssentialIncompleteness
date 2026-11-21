/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedOpenTranslation
public import CategoricalEssentialIncompleteness.V46NamedHilbertQuantifiers

/-! # Proof compatibility for arithmetic NNF connectives

Foundation uses negation-normal forms, so its implication does not translate by
syntactic equality to the Hilbert implication constructor. The comparisons below are
Hilbert proofs, using the constructed classical entailment instance and the derived
Hilbert quantifier rules.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofConnectives
open NamedArithmeticSignature
open ArithmeticNamedOpenTranslation

local instance proofConnectivesFormulaDecidableEq : DecidableEq NamedArithmeticSignature.Formula :=
  Classical.decEq _

def system (Γ : SyntacticPredicates.Carrier) :
    NamedHilbertPropositional.System functionSymbols relationSymbols bound := ⟨Γ⟩

variable (Γ : SyntacticPredicates.Carrier)
local notation "S" => system Γ
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ

private theorem toNative (φ : NamedArithmeticSignature.Formula) (h : S ⊢ φ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff
    functionSymbols relationSymbols bound (system Γ) φ).mp h

private theorem fromNative (φ : NamedArithmeticSignature.Formula) (h : D φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff
    functionSymbols relationSymbols bound (system Γ) φ).mpr h

/-- Universal congruence comes from proved Hilbert monotonicity, rather than from any
assumed first-order entailment class. -/
theorem all_equivalence (x : ℕ) {φ ψ : NamedArithmeticSignature.Formula}
    (h : S ⊢ φ 🡘 ψ) : S ⊢ (NamedFiniteSyntax.Formula.all x φ) 🡘 (.all x ψ) := by
  apply E_intro
  · exact fromNative Γ _ (NamedHilbertQuantifiers.all_mono
      functionSymbols relationSymbols bound Γ x (toNative Γ _ (K_left h)))
  · exact fromNative Γ _ (NamedHilbertQuantifiers.all_mono
      functionSymbols relationSymbols bound Γ x (toNative Γ _ (K_right h)))

/-- De Morgan for the named connective encodings follows from ordinary classical proof
combinators; no semantic entailment argument is used. -/
theorem deMorgan_and (φ ψ : NamedArithmeticSignature.Formula) :
    S ⊢ ArithmeticNamedTranslation.disjunction (.neg φ) (.neg ψ) 🡘
      (.neg (ArithmeticNamedTranslation.conjunction φ ψ)) := by
  have h : S ⊢ ((∼∼φ) 🡒 (∼ψ)) 🡘 (φ 🡒 ∼ψ) :=
    ECC_of_E_of_E (E_symm (dn (φ := φ))) E_id
  exact E_trans h (dn (φ := φ 🡒 ∼ψ))

theorem deMorgan_or (φ ψ : NamedArithmeticSignature.Formula) :
    S ⊢ ArithmeticNamedTranslation.conjunction (.neg φ) (.neg ψ) 🡘
      (.neg (ArithmeticNamedTranslation.disjunction φ ψ)) := by
  exact ENN_of_E (ECC_of_E_of_E E_id (E_symm (dn (φ := ψ))))

/-- Translation of source NNF negation is provably equivalent to the named negation,
including both quantifier constructors. -/
theorem nnf_neg {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ),
      S ⊢ formula next bn fn (∼φ) 🡘 (.neg (formula next bn fn φ)) := by
  induction φ with
  | verum => intros; exact E_id
  | falsum => intros; exact dn
  | rel r children => intro next bn fn; cases r <;> exact E_id
  | nrel r children => intro next bn fn; cases r <;> exact dn
  | and φ ψ il ir =>
      intro next bn fn
      exact E_trans (EAA_of_E_of_E (il next bn fn) (ir next bn fn))
        (deMorgan_and Γ (formula next bn fn φ) (formula next bn fn ψ))
  | or φ ψ il ir =>
      intro next bn fn
      exact E_trans (EKK_of_E_of_E (il next bn fn) (ir next bn fn))
        (deMorgan_or Γ (formula next bn fn φ) (formula next bn fn ψ))
  | all φ ih =>
      intro next bn fn
      have hn : S ⊢
          (.neg (formula (next+1) (Matrix.vecCons next bn) fn (∼φ))) 🡘
            formula (next+1) (Matrix.vecCons next bn) fn φ :=
        E_trans (ENN_of_E (ih (next+1) (Matrix.vecCons next bn) fn)) (E_symm dn)
      exact ENN_of_E (all_equivalence Γ next hn)
  | exs φ ih =>
      intro next bn fn
      exact E_trans (all_equivalence Γ next (ih (next+1) (Matrix.vecCons next bn) fn)) dn

/-- Source implication is NNF disjunction with NNF negation. Its target has a
proof-equivalence to the implication constructor. -/
theorem implication {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₒᵣ ξ n)
    (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ) :
    S ⊢ formula next bn fn (φ 🡒 ψ) 🡘
      (NamedFiniteSyntax.Formula.imp (formula next bn fn φ) (formula next bn fn ψ)) := by
  have hn := nnf_neg Γ φ next bn fn
  exact E_trans (EAA_of_E_of_E hn E_id) (E_symm ECAN)

/-- A source MP step is realized by ordered Hilbert MP after the proved implication
comparison. -/
theorem modusPonens {ξ : Type} {n : ℕ} (φ ψ : Semiformula ℒₒᵣ ξ n)
    (next : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ)
    (hp : D (formula next bn fn φ)) (hi : D (formula next bn fn (φ 🡒 ψ))) :
    D (formula next bn fn ψ) := by
  have he := implication Γ φ ψ next bn fn
  have himp : S ⊢ (NamedFiniteSyntax.Formula.imp (formula next bn fn φ) (formula next bn fn ψ)) :=
    (K_left he) ⨀ (fromNative Γ _ hi)
  exact .modusPonens hp (toNative Γ _ himp)

private theorem rename_body {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ (n+1))
    (seed x y : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ)
    (hx : x < seed) (hy : y < seed)
    (hb : ∀ i, bn i ≠ x) (hf : ∀ i, fn i ≠ x) :
    (formula seed (Matrix.vecCons x bn) fn φ).substitute x (.var y) =
      some (formula seed (Matrix.vecCons y bn) fn φ) := by
  have h := formula_substitution_rew φ (Rew.id (L := ℒₒᵣ)) seed
    (Matrix.vecCons y bn) fn (Matrix.vecCons x bn) fn x (NamedFiniteSyntax.Term.var y) hx
    (by
      intro z hz
      have he : z = y := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
      subst z
      exact hy)
  have hqb : ∀ i, (NamedFiniteSyntax.Term.var (Matrix.vecCons x bn i)).substitute x (.var y) =
      term (Matrix.vecCons y bn) fn ((Rew.id (L := ℒₒᵣ)) (.bvar i)) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [term,NamedFiniteSyntax.Term.substitute]
    · simp only [Matrix.cons_val_succ,Rew.id_app,term,NamedFiniteSyntax.Term.substitute,ite_eq_right (hb j)]
  have hqf : ∀ i, (NamedFiniteSyntax.Term.var (fn i)).substitute x (.var y) =
      term (Matrix.vecCons y bn) fn ((Rew.id (L := ℒₒᵣ)) (.fvar i)) := by
    intro i
    simp only [Rew.id_app,term,NamedFiniteSyntax.Term.substitute,ite_eq_right (hf i)]
  simpa only [ReflectiveRewriting.id_app] using h hqb hqf

private theorem body_absent {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ (n+1))
    (seed x z : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ)
    (hz : z ≠ x) (hb : ∀ i, bn i ≠ z) (hf : ∀ i, fn i ≠ z) :
    z ∉ (formula seed (Matrix.vecCons x bn) fn φ).freeVariables := by
  intro h
  rcases formula_names φ seed (Matrix.vecCons x bn) fn z h with ⟨i,hi⟩ | ⟨i,hi⟩
  · revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      exact hz (by simpa only [Matrix.cons_val_zero] using hi.symm)
    · intro hi
      exact hb j (by simpa only [Matrix.cons_val_succ] using hi)
  · exact hf i hi

/-- The two-way alpha step is carried by computed substitutions under one common inner
seed. Both query names are below all inner binders. -/
private theorem all_alpha_body {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ (n+1))
    (negative : Bool) (low high : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ)
    (hlt : low < high) (hb : ∀ i, bn i < low) (hf : ∀ i, fn i < low) :
    let A := formula (high+1) (Matrix.vecCons low bn) fn φ
    let B := formula (high+1) (Matrix.vecCons high bn) fn φ
    S ⊢ (NamedFiniteSyntax.Formula.all low (if negative then .neg A else A)) 🡘
      (.all high (if negative then .neg B else B)) := by
  let A := formula (high+1) (Matrix.vecCons low bn) fn φ
  let B := formula (high+1) (Matrix.vecCons high bn) fn φ
  have hs : A.substitute low (.var high) = some B :=
    rename_body φ (high+1) low high bn fn (Nat.lt_succ_of_lt hlt) (Nat.lt_succ_self high)
      (fun i => Nat.ne_of_lt (hb i)) (fun i => Nat.ne_of_lt (hf i))
  have hr : B.substitute high (.var low) = some A :=
    rename_body φ (high+1) high low bn fn (Nat.lt_succ_self high) (Nat.lt_succ_of_lt hlt)
      (fun i => Nat.ne_of_lt ((hb i).trans hlt)) (fun i => Nat.ne_of_lt ((hf i).trans hlt))
  have hff : A.FreeFor low (.var high) := formula_freeFor_bounded φ (high+1)
    (Matrix.vecCons low bn) fn low (.var high)
      (by
        intro z hz
        have he : z = high := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
        subst z
        exact Nat.lt_succ_self high)
  have hfr : B.FreeFor high (.var low) := formula_freeFor_bounded φ (high+1)
    (Matrix.vecCons high bn) fn high (.var low)
      (by
        intro z hz
        have he : z = low := by simpa [NamedFiniteSyntax.Term.freeVariables] using hz
        subst z
        exact Nat.lt_succ_of_lt hlt)
  have ha : high ∉ A.freeVariables := body_absent φ (high+1) low high bn fn
    (Ne.symm (Nat.ne_of_lt hlt))
    (fun i => Nat.ne_of_lt ((hb i).trans hlt)) (fun i => Nat.ne_of_lt ((hf i).trans hlt))
  have hbn : low ∉ B.freeVariables := body_absent φ (high+1) high low bn fn
    (Nat.ne_of_lt hlt) (fun i => Nat.ne_of_lt (hb i)) (fun i => Nat.ne_of_lt (hf i))
  have hs' : (if negative then .neg A else A).substitute low (.var high) =
      some (if negative then .neg B else B) := by cases negative <;> simp [NamedFiniteSyntax.Formula.substitute,hs]
  have hr' : (if negative then .neg B else B).substitute high (.var low) =
      some (if negative then .neg A else A) := by cases negative <;> simp [NamedFiniteSyntax.Formula.substitute,hr]
  have hff' : (if negative then .neg A else A).FreeFor low (.var high) := by cases negative <;> exact hff
  have hfr' : (if negative then .neg B else B).FreeFor high (.var low) := by cases negative <;> exact hfr
  have ha' : high ∉ (if negative then .neg A else A).freeVariables := by cases negative <;> exact ha
  have hb' : low ∉ (if negative then .neg B else B).freeVariables := by cases negative <;> exact hbn
  have hav : high ∉ (NamedFiniteSyntax.Formula.all low (if negative then .neg A else A)).freeVariables :=
    fun h => ha' (List.mem_of_mem_filter h)
  have hbv : low ∉ (NamedFiniteSyntax.Formula.all high (if negative then .neg B else B)).freeVariables :=
    fun h => hb' (List.mem_of_mem_filter h)
  exact E_intro
    (fromNative Γ _ (NamedHilbertQuantifiers.all_rename_forward functionSymbols relationSymbols bound Γ
      low high _ _ hff' hs' hav))
    (fromNative Γ _ (NamedHilbertQuantifiers.all_rename_forward functionSymbols relationSymbols bound Γ
      high low _ _ hfr' hr' hbv))

/-- Changing the fresh binder seed has a Hilbert proof comparison. Inner binders are
changed first; only then is the outer binder renamed through its computed capture-free
substitution. -/
theorem seed_mono {ξ : Type} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) :
    ∀ (low high : ℕ) (bn : Fin n → ℕ) (fn : ξ → ℕ),
      (∀ i, bn i < low) → (∀ i, fn i < low) → low ≤ high →
      S ⊢ formula low bn fn φ 🡘 formula high bn fn φ := by
  induction φ with
  | verum => intros; exact E_id
  | falsum => intros; exact E_id
  | rel r children => intros; cases r <;> exact E_id
  | nrel r children => intros; cases r <;> exact E_id
  | and φ ψ il ir =>
      intro low high bn fn hb hf hle
      exact EKK_of_E_of_E (il low high bn fn hb hf hle) (ir low high bn fn hb hf hle)
  | or φ ψ il ir =>
      intro low high bn fn hb hf hle
      exact EAA_of_E_of_E (il low high bn fn hb hf hle) (ir low high bn fn hb hf hle)
  | all φ ih =>
      intro low high bn fn hb hf hle
      by_cases he : low = high
      · subst high; exact E_id
      · have hlt : low < high := Nat.lt_of_le_of_ne hle he
        have hbody := ih (low+1) (high+1) (Matrix.vecCons low bn) fn
          (fun i => Fin.cases (Nat.lt_succ_self low) (fun j => Nat.lt_succ_of_lt (hb j)) i)
          (fun i => Nat.lt_succ_of_lt (hf i)) (Nat.succ_le_succ hle)
        exact E_trans (all_equivalence Γ low hbody) (all_alpha_body Γ φ false low high bn fn hlt hb hf)
  | exs φ ih =>
      intro low high bn fn hb hf hle
      by_cases he : low = high
      · subst high; exact E_id
      · have hlt : low < high := Nat.lt_of_le_of_ne hle he
        have hbody := ih (low+1) (high+1) (Matrix.vecCons low bn) fn
          (fun i => Fin.cases (Nat.lt_succ_self low) (fun j => Nat.lt_succ_of_lt (hb j)) i)
          (fun i => Nat.lt_succ_of_lt (hf i)) (Nat.succ_le_succ hle)
        exact E_trans (ENN_of_E (all_equivalence Γ low (ENN_of_E hbody)))
          (ENN_of_E (all_alpha_body Γ φ true low high bn fn hlt hb hf))

/-- The LK universal eigenvariable body is converted by the exact free rewrite. The only
side condition is the named antecedent absence needed by the distribution scheme. -/
theorem lk_all_under (φ : Semiproposition ℒₒᵣ 1) (next : ℕ) (fn : ℕ → ℕ)
    (δ : NamedArithmeticSignature.Formula) (hδ : next ∉ δ.freeVariables)
    (h : D (.imp δ (formula (next+1) ![] (freeCons next fn) (Rewriting.free φ)))) :
    D (.imp δ (formula next ![] fn (∀¹ φ))) := by
  have he : formula (next+1) ![] (freeCons next fn) (Rewriting.free φ) =
      formula (next+1) ![next] fn φ := by
    have hn : Fin.snoc (![] : Fin 0 → ℕ) next = ![next] := by
      funext i
      fin_cases i
      rfl
    simpa [hn] using formula_free φ (next+1) ![] (freeCons next fn)
  have hb : D (.imp δ (formula (next+1) ![next] fn φ)) := he ▸ h
  exact NamedHilbertQuantifiers.all_intro_under functionSymbols relationSymbols bound Γ
    next δ (formula (next+1) ![next] fn φ) hδ hb

/-- The LK existential step is a Hilbert implication. Its source substitution is compared
syntactically, and the one-step seed change is proved by alpha conversion; no semantic
compatibility premise is used. -/
theorem lk_exs_instance (φ : Semiproposition ℒₒᵣ 1) (t : SyntacticTerm ℒₒᵣ)
    (next : ℕ) (fn : ℕ → ℕ) (hf : ∀ i, fn i < next) :
    D (.imp (formula next ![] fn (φ/[t])) (formula next ![] fn (∃¹ φ))) := by
  let body := formula (next+1) ![next] fn φ
  let value := term ![] fn t
  let instFormula := formula (next+1) ![] fn (φ/[t])
  have hs : body.substitute next value = some instFormula :=
    instance_substitution φ t next fn hf
  have hff : body.FreeFor next value := formula_freeFor_bounded φ (next+1) ![next] fn next value
    (fun z hz => Nat.lt_succ_of_lt
      (term_names_bound t ![] fn next (fun i => i.elim0) hf z hz))
  have hi : D (.imp instFormula (formula next ![] fn (∃¹ φ))) :=
    NamedHilbertQuantifiers.exists_intro functionSymbols relationSymbols bound Γ next body instFormula value hff hs
  have he := seed_mono Γ (φ/[t]) next (next+1) ![] fn
    (fun i => i.elim0) hf (Nat.le_succ next)
  exact NamedHilbertPropositional.implication_trans functionSymbols relationSymbols bound Γ
    (toNative Γ _ (K_left he)) hi


/-- The conjunction step in a one-sided source sequent is a propositional proof in the
constructed Hilbert entailment. -/
theorem disjunction_and (φ ψ δ : NamedArithmeticSignature.Formula)
    (hp : S ⊢ φ ⋎ δ) (hq : S ⊢ ψ ⋎ δ) : S ⊢ (φ ⋏ ψ) ⋎ δ := by
  apply of_C_of_C_of_A ?_ or₂ hp
  apply FiniteContext.deduct'
  apply of_C_of_C_of_A ?_ or₂ (FiniteContext.of' hq)
  apply FiniteContext.deduct
  exact or₁ ⨀ (K_intro FiniteContext.by_axm₁ FiniteContext.by_axm₀)

/-- The Hilbert cut step combines two disjunction proofs. -/
theorem disjunction_cut (φ δ : NamedArithmeticSignature.Formula)
    (hp : S ⊢ φ ⋎ δ) (hn : S ⊢ (∼φ) ⋎ δ) : S ⊢ δ := by
  apply of_C_of_C_of_A ?_ C_id hp
  apply FiniteContext.deduct'
  apply of_C_of_C_of_A ?_ C_id (FiniteContext.of' hn)
  apply FiniteContext.deduct
  exact of_O ((N_iff_CO.mp FiniteContext.by_axm₀) ⨀ FiniteContext.by_axm₁)

/-- Universal quantification commutes past a disjunct with the absence guard. The
derivation uses instantiation, Gen and distribution. -/
theorem all_disjunction_right (x : ℕ) (φ δ : NamedArithmeticSignature.Formula)
    (hx : x ∉ δ.freeVariables) :
    D (.imp (.all x (ArithmeticNamedTranslation.disjunction φ δ))
      (ArithmeticNamedTranslation.disjunction (.all x φ) δ)) := by
  let A := NamedFiniteSyntax.Formula.all x (ArithmeticNamedTranslation.disjunction φ δ)
  have hi : S ⊢ A 🡒 (φ ⋎ δ) := fromNative Γ _
    (NamedHilbertQuantifiers.all_elim_self functionSymbols relationSymbols bound Γ x _)
  have he : S ⊢ (A ⋏ ∼δ) 🡒 φ := by
    apply FiniteContext.deduct'
    have ho : [A ⋏ ∼δ] ⊢[S] φ ⋎ δ := (FiniteContext.of' hi) ⨀ (K_left FiniteContext.by_axm₀)
    have hδ : [A ⋏ ∼δ] ⊢[S] ∼δ := K_right FiniteContext.by_axm₀
    exact of_A_of_N (CAA ⨀ ho) hδ
  have ha : x ∉ (A ⋏ ∼δ).freeVariables := by
    change x ∉ A.freeVariables ++ δ.freeVariables
    simp only [List.mem_append,not_or]
    exact ⟨NamedHilbertQuantifiers.bound_absent x _,hx⟩
  have hg : S ⊢ (A ⋏ ∼δ) 🡒 (NamedFiniteSyntax.Formula.all x φ) :=
    fromNative Γ _ (NamedHilbertQuantifiers.all_intro_under functionSymbols relationSymbols bound Γ
      x (A ⋏ ∼δ) φ ha (toNative Γ _ he))
  apply toNative Γ _
  apply FiniteContext.deduct'
  have hcur : [A] ⊢[S] (∼δ) 🡒 (NamedFiniteSyntax.Formula.all x φ) := by
    apply FiniteContext.deduct
    exact (FiniteContext.of' hg) ⨀ (K_intro FiniteContext.by_axm₁ FiniteContext.by_axm₀)
  have ho : [A] ⊢[S] (∼∼δ) ⋎ (NamedFiniteSyntax.Formula.all x φ) := AN_of_C hcur
  have ho' : [A] ⊢[S] δ ⋎ (NamedFiniteSyntax.Formula.all x φ) :=
    of_C_of_C_of_A (C_trans dne or₁) or₂ ho
  exact CAA ⨀ ho'

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofConnectives
