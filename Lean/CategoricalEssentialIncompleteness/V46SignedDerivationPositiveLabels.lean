/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationLeafCodes

/-! # Finite positive axiom labels from numerical derivation words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

def positiveLabelsBlueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “o. o = 0”
  adjoin := .mkSigma “o r rs ih. ∃ n p, !labelGraph.val n r ∧ !leafGraph.val p n 0 ∧
    ((r = p ∧ !adjoinDef.val o n ih) ∨ (r ≠ p ∧ o = ih))”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : DecidableEq M := Classical.decEq M

def positiveLabelsConstruction : VecRec.Construction M positiveLabelsBlueprint where
  nil _ := 0
  adjoin _ r _ ih := if r = leaf (label r) 0 then adjoin (label r) ih else ih
  nil_defined := .mk fun v => by simp [positiveLabelsBlueprint]
  adjoin_defined := .mk fun v => by
    have hg : positiveLabelsBlueprint.adjoin.val.Evalb v ↔
        (v 1 = leaf (label (v 1)) 0 ∧ v 0 = adjoin (label (v 1)) (v 3)) ∨
        (v 1 ≠ leaf (label (v 1)) 0 ∧ v 0 = v 3) := by
      simp [positiveLabelsBlueprint]
    rw [hg]
    change _ ↔ v 0 = if v 1 = leaf (label (v 1)) 0 then
      adjoin (label (v 1)) (v 3) else v 3
    split_ifs with h
    · constructor
      · rintro (⟨_, ho⟩ | ⟨hn, _⟩)
        · exact ho
        · exact (hn h).elim
      · intro ho
        exact Or.inl ⟨h, ho⟩
    · constructor
      · rintro (⟨hy, _⟩ | ⟨_, ho⟩)
        · exact (h hy).elim
        · exact ho
      · intro ho
        exact Or.inr ⟨h, ho⟩

def positiveLabels (word : M) : M := positiveLabelsConstruction.result ![] word

@[simp] theorem positiveLabels_nil : positiveLabels (0 : M) = 0 := by
  simp [positiveLabels, positiveLabelsConstruction]

@[simp] theorem positiveLabels_adjoin (r word : M) :
    positiveLabels (adjoin r word) =
      if r = leaf (label r) 0 then adjoin (label r) (positiveLabels word)
      else positiveLabels word := by
  simp [positiveLabels, positiveLabelsConstruction]

end Models

def positiveLabelsGraph : 𝚺₁.Semisentence 2 := positiveLabelsBlueprint.resultDef

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem positiveLabelsGraph_eval (out word : M) :
    positiveLabelsGraph.val.Evalb ![out, word] ↔ out = positiveLabels word := by
  have he := (positiveLabelsConstruction (M := M)).eval_resultDef ![out, word]
  have hv : (fun i : Fin 0 => (![out, word] : Fin 2 → M) (i.succ.succ)) = ![] := by
    funext i
    exact Fin.elim0 i
  rw [hv] at he
  change positiveLabelsBlueprint.resultDef.val.Evalb ![out, word] ↔
    out = positiveLabelsConstruction.result ![] word
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using he

instance positiveLabels_defined : 𝚺₁-Function₁ (positiveLabels : M → M) via
    positiveLabelsGraph := .mk fun v => by
  have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv, Fin.succ_zero_eq_one] using positiveLabelsGraph_eval (v 0) (v 1)
instance positiveLabels_definable : 𝚺₁-Function₁ (positiveLabels : M → M) :=
  positiveLabels_defined.to_definable
instance positiveLabels_definable' (Γ m) : Γ-[m + 1]-Function₁ (positiveLabels : M → M) :=
  positiveLabels_definable.of_sigmaOne

/-- Occurrence is in the numerical word, with its model-internal length. The extraction
retains every occurrence, including repetitions. -/
theorem member_positiveLabels (n word : M) :
    member n (positiveLabels word) = 1 ↔ MemVec (leaf n 0) word := by
  classical
  induction word using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin r word ih =>
    rw [positiveLabels_adjoin, memVec_adjoin_iff]
    by_cases h : r = leaf (label r) 0
    · rw [ite_eq_left h, member_adjoin]
      have he : label r = n ↔ leaf n 0 = r := by
        constructor
        · intro hn
          rw [← hn]
          exact h.symm
        · intro hr
          simpa only [label_leaf] using congrArg label hr.symm
      by_cases hn : label r = n
      · simp [hn, he.mp hn]
      · have hr : leaf n 0 ≠ r := fun e => hn (he.mpr e)
        simp [hn, hr, ih]
    · have hr : leaf n 0 ≠ r := by
        intro e
        subst r
        exact h (by rw [label_leaf])
      rw [ite_eq_right h]
      simp only [hr, false_or, ih]

theorem positiveLabels_append (left right : M) :
    positiveLabels (Words.append left right) =
      Words.append (positiveLabels left) (positiveLabels right) := by
  classical
  induction left using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin r left ih =>
    rw [Words.append_adjoin, positiveLabels_adjoin, positiveLabels_adjoin, ih]
    split_ifs <;> simp only [Words.append_adjoin]

/-- Well-typed coefficients imply that every extracted label satisfies
the positive axiom predicate, for arbitrary internal word lengths. -/
theorem positiveLabels_carrier (L A B R₁ R₂ : Carrier) (word : M)
    (hw : (Coding.coefficients (rulePolynomial L A B R₁ R₂) .unit).val.Evalb ![word]) :
    (SyntacticLists.listCarrier A).val.Evalb ![positiveLabels word] := by
  rw [SyntacticLists.listCarrier_eval]
  have hc := (FiniteSigmaOne.allEntriesCondition_eval _ word).mp
    ((FiniteSigmaOne.finite_membership_model _ word).mpr hw)
  intro i hi
  let n := nth (positiveLabels word) i
  have hm : member n (positiveLabels word) = 1 :=
    (member_eq_one_iff _ _).mpr ⟨i, hi, rfl⟩
  obtain ⟨j, hj, he⟩ := (member_positiveLabels n word).mp hm
  exact (positive_record L A B R₁ R₂ n).mp (he ▸ hc j hj)

end Models

open SyntacticSyntax.NatVectors
local instance : DecidableEq ℕ := Classical.decEq ℕ

theorem positiveLabels_primrec : Primrec (positiveLabels : ℕ → ℕ) := by
  have hn : Primrec (fun _ : ℕ => (positiveLabelsConstruction (M := ℕ)).nil ![]) :=
    Primrec.const 0
  have hs : Primrec₂ (fun (_ : ℕ) (t : ℕ × List ℕ × ℕ) =>
      (positiveLabelsConstruction (M := ℕ)).adjoin ![] t.1 (pack t.2.1) t.2.2) := by
    have hr := Primrec.fst.comp (Primrec.snd : Primrec (fun p : ℕ × (ℕ × List ℕ × ℕ) => p.2))
    have hl := label_primrec.comp hr
    have hi : Primrec (fun p : ℕ × (ℕ × List ℕ × ℕ) => p.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    exact Primrec.ite (Primrec.eq.comp hr (leaf_primrec.comp hl (Primrec.const 0)))
      (adjoin_primrec.comp hl hi) hi
  exact (vecRec_primrec _ (fun _ : ℕ => ![]) hn hs).comp
    (Primrec.pair (Primrec.const 0) Primrec.id)

end CategoricalEssentialIncompleteness.V46.SignedDerivation
