/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofConnectives
public import CategoricalEssentialIncompleteness.V46ArithmeticNamedProofNumerals
public import Foundation.FirstOrder.LK.Simplified

/-! # Translation of finite LK2 proofs to named proofs

Induction on LK2 derivations translates proofs under the stated
axiom-admissibility premise. The axiom-comparison modules instantiate
this premise for PA.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofTranslation
open NamedArithmeticSignature ArithmeticNamedOpenTranslation ArithmeticNamedProofConnectives

local instance proofTranslationNamedDecidableEq : DecidableEq NamedArithmeticSignature.Formula :=
  Classical.decEq _

variable (A : SyntacticPredicates.Carrier)
local notation "S" => ArithmeticNamedProofConnectives.system A
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A

def sequent (seed : ℕ) (fn : ℕ → ℕ) (Δ : Finset (Proposition ℒₒᵣ)) :
    NamedArithmeticSignature.Formula :=
  Δ.disj' (fun φ => formula seed ![] fn φ)

private theorem native {φ : NamedArithmeticSignature.Formula} (h : S ⊢ φ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mp h

private theorem provable {φ : NamedArithmeticSignature.Formula} (h : D φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mpr h

private theorem sequent_intro (seed : ℕ) (fn : ℕ → ℕ)
    (Δ : Finset (Proposition ℒₒᵣ)) {φ : Proposition ℒₒᵣ} (hφ : φ ∈ Δ) :
    S ⊢ formula seed ![] fn φ 🡒 sequent seed fn Δ :=
  right_Fdisj'_intro Δ (fun ψ => formula seed ![] fn ψ) hφ

private theorem sequent_cases (seed : ℕ) (fn : ℕ → ℕ)
    (Δ : Finset (Proposition ℒₒᵣ)) (χ : NamedArithmeticSignature.Formula)
    (h : ∀ φ ∈ Δ, S ⊢ formula seed ![] fn φ 🡒 χ) :
    S ⊢ sequent seed fn Δ 🡒 χ :=
  left_Fdisj'_intro Δ (fun φ => formula seed ![] fn φ) h

private theorem sequent_insert (seed : ℕ) (fn : ℕ → ℕ)
    (Δ : Finset (Proposition ℒₒᵣ)) (φ : Proposition ℒₒᵣ) :
    S ⊢ sequent seed fn (insert φ Δ) 🡘
      (formula seed ![] fn φ ⋎ sequent seed fn Δ) := by
  apply E_intro
  · apply sequent_cases A seed fn
    intro ψ hψ
    rcases Finset.mem_insert.mp hψ with rfl | hψ
    · exact or₁
    · exact C_trans (sequent_intro A seed fn Δ hψ) or₂
  · apply left_A_intro
    · exact sequent_intro A seed fn (insert φ Δ) (by simp)
    · apply sequent_cases A seed fn
      intro ψ hψ
      exact sequent_intro A seed fn (insert φ Δ) (Finset.mem_insert_of_mem hψ)

private theorem list_disj_absent (x : ℕ) (hx : x ≠ 0) :
    ∀ l : List NamedArithmeticSignature.Formula,
      (∀ φ ∈ l, x ∉ φ.freeVariables) → x ∉ l.disj₂.freeVariables := by
  intro l
  induction l using List.induction_with_singleton with
  | hnil =>
      intro _
      change x ∉ [0,0]
      simp [hx]
  | hsingle φ =>
      intro h
      exact h φ (by simp)
  | hcons φ l hl ih =>
      intro h
      rw [List.disj₂_cons_nonempty hl]
      change x ∉ φ.freeVariables ++ l.disj₂.freeVariables
      simp only [List.mem_append,not_or]
      exact ⟨h φ (by simp),ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))⟩

private theorem sequent_absent (seed : ℕ) (fn : ℕ → ℕ)
    (hf : ∀ i, fn i < seed) (Δ : Finset (Proposition ℒₒᵣ)) :
    seed ∉ (sequent seed fn Δ).freeVariables := by
  unfold sequent Finset.disj' List.disj'
  apply list_disj_absent seed (Nat.ne_of_gt ((Nat.zero_le (fn 0)).trans_lt (hf 0)))
  intro ψ hψ
  obtain ⟨φ,_,rfl⟩ := List.mem_map.mp hψ
  intro hseed
  exact (Nat.lt_irrefl seed)
    (formula_names_bound φ seed ![] fn seed (fun i => i.elim0) hf seed hseed)

/-- Source axiom admissibility is checked at the fixed named translation.
This premise does not assert translation of any source proof. -/
def AxiomsAdmissible (T : Theory ℒₒᵣ) : Prop :=
  ∀ φ ∈ T, D (ArithmeticNamedTranslation.translateFormula 0 ![] φ)

/-- An actual finite LK2 derivation gives an actual native proof of its
translated sequent, for every bounded explicit eigenvariable assignment.
No injectivity, semantic soundness or standard-model hypothesis is used. -/
theorem derivation (T : Theory ℒₒᵣ) (hA : AxiomsAdmissible A T)
    {Δ : Finset (Proposition ℒₒᵣ)} (b : LK2.Derivation T Δ) :
    ∀ (seed : ℕ) (fn : ℕ → ℕ), (∀ i, fn i < seed) →
      S ⊢ sequent seed fn Δ := by
  induction b with
  | closed Δ φ hp hn =>
      intro seed fn hf
      have hneg := nnf_neg A φ seed ![] fn
      exact of_C_of_C_of_A (sequent_intro A seed fn Δ hp)
        (C_trans (K_right hneg) (sequent_intro A seed fn Δ hn)) lem
  | axm φ hT hΔ =>
      intro seed fn hf
      have hs := seed_mono A φ 0 seed ![] Empty.elim
        (fun i => i.elim0) (fun i => i.elim) (Nat.zero_le seed)
      have ht : S ⊢ ArithmeticNamedTranslation.translateFormula seed ![] φ := by
        have ha : S ⊢ formula 0 ![] Empty.elim φ := by
          rw [formula_empty]
          exact provable A (hA φ hT)
        simpa only [formula_empty] using ((K_left hs) ⨀ ha)
      have he : S ⊢ formula seed ![] fn (Rewriting.emb φ : Proposition ℒₒᵣ) := by
        simpa only [formula_emb] using ht
      exact (sequent_intro A seed fn _ hΔ) ⨀ he
  | verum hΔ =>
      intro seed fn hf
      exact (sequent_intro A seed fn _ hΔ) ⨀
        (provable A (SyntacticNamedHilbert.Derives.reflexivity NamedArithmeticSignature.zero))
  | @and Δ φ ψ hΔ bp bq ip iq =>
      intro seed fn hf
      have hp := (K_left (sequent_insert A seed fn Δ φ)) ⨀ (ip seed fn hf)
      have hq := (K_left (sequent_insert A seed fn Δ ψ)) ⨀ (iq seed fn hf)
      exact of_C_of_C_of_A (sequent_intro A seed fn Δ hΔ) C_id
        (disjunction_and A _ _ _ hp hq)
  | @or Δ φ ψ hΔ b ih =>
      intro seed fn hf
      have hmap : S ⊢ sequent seed fn (insert φ (insert ψ Δ)) 🡒 sequent seed fn Δ := by
        apply sequent_cases A seed fn
        intro χ hχ
        rcases Finset.mem_insert.mp hχ with rfl | hχ
        · exact C_trans or₁ (sequent_intro A seed fn Δ hΔ)
        · rcases Finset.mem_insert.mp hχ with rfl | hχ
          · exact C_trans or₂ (sequent_intro A seed fn Δ hΔ)
          · exact sequent_intro A seed fn Δ hχ
      exact hmap ⨀ (ih seed fn hf)
  | @all Δ φ hΔ b ih =>
      intro seed fn hf
      let δ := sequent seed fn Δ
      let body := formula (seed+1) ![seed] fn φ
      let names := freeCons seed fn
      have hnames : ∀ i, names i < seed+1 := by
        intro i
        cases i with
        | zero => exact Nat.lt_succ_self seed
        | succ i => exact Nat.lt_succ_of_lt (hf i)
      have hc := ih (seed+1) names hnames
      have hmap : S ⊢
          sequent (seed+1) names (insert (Rewriting.free φ) (Δ.image Rewriting.shift)) 🡒
            (body ⋎ δ) := by
        apply sequent_cases A (seed+1) names
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · have he : formula (seed+1) ![] names (Rewriting.free φ) = body := by
            have hn : Fin.snoc (![] : Fin 0 → ℕ) seed = ![seed] := by
              funext i
              fin_cases i
              rfl
            simpa [names,body,hn] using formula_free φ (seed+1) ![] names
          simpa only [he] using (or₁ (𝓢 := S) (φ := body) (ψ := δ))
        · obtain ⟨χ,hχ,hχeq⟩ := Finset.mem_image.mp hψ
          subst ψ
          have he : formula (seed+1) ![] names (Rewriting.shift χ) = formula (seed+1) ![] fn χ := by
            simpa only [names,freeCons_succ] using formula_shift χ (seed+1) ![] names
          have hs := seed_mono A χ seed (seed+1) ![] fn (fun i => i.elim0) hf (Nat.le_succ seed)
          have hi : S ⊢ formula (seed+1) ![] fn χ 🡒 (body ⋎ δ) :=
            C_trans (K_right hs) (C_trans (sequent_intro A seed fn Δ hχ) or₂)
          simpa only [he] using hi
      have hd : D (body ⋎ δ) := native A (hmap ⨀ hc)
      have hg : D (.all seed (body ⋎ δ)) := .generalization seed hd
      have ho : S ⊢ (.all seed body) ⋎ δ := provable A
        (.modusPonens hg (all_disjunction_right A seed body δ (sequent_absent seed fn hf Δ)))
      exact of_C_of_C_of_A (sequent_intro A seed fn Δ hΔ) C_id ho
  | @exs Δ φ hΔ t b ih =>
      intro seed fn hf
      have hmap : S ⊢ sequent seed fn (insert (φ/[t]) Δ) 🡒 sequent seed fn Δ := by
        apply sequent_cases A seed fn
        intro ψ hψ
        rcases Finset.mem_insert.mp hψ with rfl | hψ
        · exact C_trans (provable A (lk_exs_instance A φ t seed fn hf)) (sequent_intro A seed fn Δ hΔ)
        · exact sequent_intro A seed fn Δ hψ
      exact hmap ⨀ (ih seed fn hf)
  | @wk Δ Γ b hsub ih =>
      intro seed fn hf
      have hmap : S ⊢ sequent seed fn Δ 🡒 sequent seed fn Γ := by
        apply sequent_cases A seed fn
        intro φ hφ
        exact sequent_intro A seed fn Γ (hsub hφ)
      exact hmap ⨀ (ih seed fn hf)
  | @shift Δ b ih =>
      intro seed fn hf
      have hmap : S ⊢ sequent seed (fun i => fn (i+1)) Δ 🡒 sequent seed fn (Δ.image Rewriting.shift) := by
        apply sequent_cases A seed (fun i => fn (i+1))
        intro φ hφ
        have hi := sequent_intro A seed fn (Δ.image Rewriting.shift) (Finset.mem_image_of_mem Rewriting.shift hφ)
        simpa only [formula_shift] using hi
      exact hmap ⨀ (ih seed (fun i => fn (i+1)) (fun i => hf (i+1)))
  | @cut Δ φ bp bn ip ineg =>
      intro seed fn hf
      have hp := (K_left (sequent_insert A seed fn Δ φ)) ⨀ (ip seed fn hf)
      have hn := (K_left (sequent_insert A seed fn Δ (∼φ))) ⨀ (ineg seed fn hf)
      have hn' := (CAA_of_C_left (K_left (nnf_neg A φ seed ![] fn))) ⨀ hn
      exact disjunction_cut A _ _ hp hn'

/-- Closed source proofs are translated at the fixed seed, after an
explicit open-proof induction and a proved change of fresh binder names. -/
theorem sentence (T : Theory ℒₒᵣ) (hA : AxiomsAdmissible A T)
    (φ : ArithmeticSentence) (h : T ⊢ φ) :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] φ) := by
  obtain ⟨b⟩ := (provable_iff_derivable2 (T := T) (φ := φ)).mp h
  have hb := derivation A T hA b 1 (fun _ => 0) (by intro i; exact Nat.zero_lt_one)
  have hc : S ⊢ ArithmeticNamedTranslation.translateFormula 1 ![] φ := by
    simpa only [sequent,Finset.disj',Finset.toList_singleton,List.disj',List.map_singleton,
      List.disj₂_singleton,formula_emb] using hb
  have hs := seed_mono A φ 0 1 ![] Empty.elim (fun i => i.elim0) (fun i => i.elim) (by decide)
  apply native A
  have he : S ⊢ ArithmeticNamedTranslation.translateFormula 1 ![] φ 🡒
      ArithmeticNamedTranslation.translateFormula 0 ![] φ := by
    simpa only [formula_empty] using K_right hs
  exact he ⨀ hc


/-- The expanded source instance has exactly the successful literal
named substitution output, with the original generated binder names. -/
theorem expanded_instance_substitution (φ : ArithmeticSemisentence 1) (n : ℕ) :
    (ArithmeticNamedTranslation.translateFormula 1 ![0] φ).substitute 0
      (NamedArithmeticSignature.numeral n) =
        some (ArithmeticNamedTranslation.translateFormula 1 ![]
          (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence)) := by
  have h := formula_substitution_rew φ
    (Rew.subst ![ArithmeticNamedProofNumerals.expandedNumeral n]) 1 ![] Empty.elim
    ![0] Empty.elim 0 (NamedArithmeticSignature.numeral n) (by decide)
    (by intro z hz; simp only [NamedArithmeticSignature.numeral_freeVariables,List.not_mem_nil] at hz)
  have hb : ∀ i : Fin 1,
      (NamedFiniteSyntax.Term.var (![0] i)).substitute 0 (NamedArithmeticSignature.numeral n) =
        term ![] Empty.elim
          ((Rew.subst ![ArithmeticNamedProofNumerals.expandedNumeral n]) (.bvar i)) := by
    intro i
    fin_cases i
    change NamedArithmeticSignature.numeral n =
      term ![] Empty.elim (ArithmeticNamedProofNumerals.expandedNumeral n)
    exact ((term_empty ![] (ArithmeticNamedProofNumerals.expandedNumeral n)).trans
      (ArithmeticNamedProofNumerals.translate_expandedNumeral ![] n)).symm
  have hf : ∀ i : Empty,
      (NamedFiniteSyntax.Term.var (Empty.elim i)).substitute 0 (NamedArithmeticSignature.numeral n) =
        term ![] Empty.elim
          ((Rew.subst ![ArithmeticNamedProofNumerals.expandedNumeral n]) (.fvar i)) := by
    intro i
    exact i.elim
  simpa only [formula_empty] using h hb hf

/-- Under individual source PA-axiom admissibility, a source proof gives
an actual native proof of the expanded instance computed by substitution. -/
theorem expanded_instance_proof (hPA : AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    D (ArithmeticNamedTranslation.translateFormula 1 ![]
      (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence)) := by
  let χ : ArithmeticSentence := φ/[ArithmeticNamedProofNumerals.expandedNumeral n]
  have hp := sentence A 𝗣𝗔 hPA χ
    (ArithmeticNamedProofNumerals.expanded_instance_PA φ n h)
  have hs := seed_mono A χ 0 1 ![] Empty.elim
    (fun i => i.elim0) (fun i => i.elim) (by decide)
  apply native A
  have he : S ⊢ ArithmeticNamedTranslation.translateFormula 0 ![] χ 🡒
      ArithmeticNamedTranslation.translateFormula 1 ![] χ := by
    simpa only [formula_empty] using K_left hs
  exact he ⨀ (provable A hp)

/-- The negative source instance is transported by the same actual
proof induction and the NNF-negation comparison. -/
theorem expanded_instance_refutation (hPA : AxiomsAdmissible A 𝗣𝗔)
    (φ : ArithmeticSemisentence 1) (n : ℕ)
    (h : 𝗣𝗔 ⊢ ∼(φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :
    D (.neg (ArithmeticNamedTranslation.translateFormula 1 ![]
      (φ/[ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence))) := by
  let χ : ArithmeticSentence := φ/[ArithmeticNamedProofNumerals.expandedNumeral n]
  have hp := sentence A 𝗣𝗔 hPA (∼χ)
    (ArithmeticNamedProofNumerals.expanded_instance_refutation_PA φ n h)
  have hs := seed_mono A (∼χ) 0 1 ![] Empty.elim
    (fun i => i.elim0) (fun i => i.elim) (by decide)
  have he : S ⊢ ArithmeticNamedTranslation.translateFormula 0 ![] (∼χ) 🡒
      ArithmeticNamedTranslation.translateFormula 1 ![] (∼χ) := by
    simpa only [formula_empty] using K_left hs
  have hn := (K_left (nnf_neg A χ 1 ![] Empty.elim))
  apply native A
  have he' : S ⊢ ArithmeticNamedTranslation.translateFormula 0 ![] (∼χ) 🡒 formula 1 ![] Empty.elim (∼χ) := by
    simpa only [formula_empty] using he
  have hresult : S ⊢ (.neg (formula 1 ![] Empty.elim χ)) := hn ⨀ (he' ⨀ (provable A hp))
  simpa only [formula_empty] using hresult

end CategoricalEssentialIncompleteness.V46.ArithmeticNamedProofTranslation
