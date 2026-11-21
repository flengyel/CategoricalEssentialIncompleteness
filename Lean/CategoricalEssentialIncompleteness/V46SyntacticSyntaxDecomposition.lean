/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # Root decomposition of accepted postfix words -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
open Coding
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance decompositionDecidableEq : DecidableEq M := Classical.decEq M

/-- Positive record membership and existing accepted children suffice
to preserve the stack invariant through every successful parser step. -/
theorem step_stack_valid (a b : RawPolynomial) (record stack : M)
    (hr : (recordCarrier a b).val.Evalb ![record])
    (hs : (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb ![stack]) :
    step a b record (stack + 1) = 0 ∨
      (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb
        ![step a b record (stack + 1) - 1] := by
  obtain ⟨s, k, rfl⟩ : ∃ s k : M, record = ⟪s, k⟫ :=
    ⟨π₁ record, π₂ record, (pair_unpair record).symm⟩
  rcases (recordCarrier_eval a b ⟪s, k⟫).mp hr with ⟨hk, hshape⟩ | ⟨hk, hshape⟩
  · have hk' : k = 0 := by simpa using hk
    subst k
    rcases nil_or_adjoin (refill a s stack) with hz | ⟨u, rest, hu⟩
    · exact Or.inl (by simp [step, hz])
    · obtain ⟨hraw, hrest⟩ := refill_typed (carrier false a b) (carrier true a b)
        a s stack u rest (by simpa using hshape) hs hu
      have hsu := (refill_sound a s stack u rest hu).1
      have hc := term_constructor_carrier a b u hraw
      right
      simpa [step, hu, constructor, hsu] using
        (stackCarrier_adjoin (carrier false a b) (carrier true a b)
          ⟪constructor false a u, 0⟫ rest).mpr ⟨by simpa using hc, hrest⟩
  · have hk' : k = 1 := by simpa using hk
    subst k
    rcases nil_or_adjoin (refill b s stack) with hz | ⟨u, rest, hu⟩
    · exact Or.inl (by simp [step, hz])
    · obtain ⟨hraw, hrest⟩ := refill_typed (carrier false a b) (carrier true a b)
        b s stack u rest (by simpa using hshape) hs hu
      have hsu := (refill_sound b s stack u rest hu).1
      have hc := formula_constructor_carrier a b u hraw
      right
      simpa [step, hu, constructor, hsu] using
        (stackCarrier_adjoin (carrier false a b) (carrier true a b)
          ⟪constructor true b u, 1⟫ rest).mpr ⟨by simpa using hc, hrest⟩

private def prefixStackInvariant (a b : RawPolynomial) : 𝚺₁.Semisentence 2 :=
  let R := prefixGraph a b
  let S := stackCarrier (carrier false a b) (carrier true a b)
  .mkSigma “n word. ∃ state stack, !R.val state n word 1 ∧
    !subDef.val stack state 1 ∧ (state = 0 ∨ !S.val stack)”

private theorem prefixStackInvariant_eval (a b : RawPolynomial) (n word : M) :
    (prefixStackInvariant a b).val.Evalb ![n, word] ↔
      runPrefix a b word n 1 = 0 ∨
        (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb
          ![runPrefix a b word n 1 - 1] := by
  simp [prefixStackInvariant]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
private theorem prefixStackInvariant_definable (a b : RawPolynomial) :
    𝚺₁.DefinableRel (fun n word : M => (prefixStackInvariant a b).val.Evalb ![n, word]) := by
  have h : 𝚺₁.Definable (fun v : Fin 2 → M => (prefixStackInvariant a b).val.Evalb v) :=
    HierarchySymbol.Defined.to_definable (prefixStackInvariant a b) (.mk (fun _ => Iff.rfl))
  exact h.of_iff fun v => by
    have hv : ![v 0, v 1] = v := (Matrix.fun_eq_vec_two v).symm
    change (prefixStackInvariant a b).val.Evalb ![v 0, v 1] ↔
      (prefixStackInvariant a b).val.Evalb v
    rw [hv]

/-- Sigma-one induction constructs the accepted-block invariant for every bounded
runPrefix of a coefficient-valid word. -/
theorem prefix_stack_valid (a b : RawPolynomial) (word n : M)
    (hw : (coefficients a b).val.Evalb ![word]) (hn : n ≤ len word) :
    runPrefix a b word n 1 = 0 ∨
      (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb
        ![runPrefix a b word n 1 - 1] := by
  have hrecords : ∀ i < len word, (recordCarrier a b).val.Evalb ![nth word i] :=
    (FiniteSigmaOne.allEntriesCondition_eval (recordCarrier a b) word).mp
      ((FiniteSigmaOne.finite_membership_model (recordCarrier a b) word).mpr hw)
  apply (prefixStackInvariant_eval a b n word).mp
  induction n using ISigma1.sigma1_succ_induction
  · apply HierarchySymbol.Definable.imp (by definability)
    exact HierarchySymbol.DefinableRel.comp (prefixStackInvariant_definable a b)
      (by definability) (by definability)
  case zero => apply (prefixStackInvariant_eval a b 0 word).mpr; right; simp
  case succ n ih =>
    have hnlt : n < len word := Arithmetic.succ_le_iff_lt.mp hn
    have hv := (prefixStackInvariant_eval a b n word).mp (ih (le_trans (by simp) hn))
    apply (prefixStackInvariant_eval a b (n + 1) word).mpr
    rcases zero_or_succ (runPrefix a b word n 1) with hz | ⟨stack, hstack⟩
    · left; simp [prefix_succ, hz]
    · have ht : (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb ![stack] := by
        rcases hv with hv | hv
        · simp [hstack] at hv
        · simpa [hstack] using hv
      simpa [prefix_succ, hstack] using step_stack_valid a b (nth word n) stack (hrecords n hnlt) ht

/-- A complete successful step exposes its unique polynomial source.
The numeric root tag itself forces the claimed output sort. -/
theorem step_root (a b : RawPolynomial) (record stack word k : M)
    (hr : (recordCarrier a b).val.Evalb ![record])
    (hs : (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb ![stack])
    (h : step a b record (stack + 1) = adjoin ⟪word, k⟫ 0 + 1) :
    (k = 0 ∧ ∃ u : M,
      (rawCarrier (carrier false a b) (carrier true a b) a).val.Evalb ![u] ∧
        word = constructor false a u) ∨
    (k = 1 ∧ ∃ u : M,
      (rawCarrier (carrier false a b) (carrier true a b) b).val.Evalb ![u] ∧
        word = constructor true b u) := by
  obtain ⟨s, tag, rfl⟩ : ∃ s tag : M, record = ⟪s, tag⟫ :=
    ⟨π₁ record, π₂ record, (pair_unpair record).symm⟩
  rcases (recordCarrier_eval a b ⟪s, tag⟫).mp hr with ⟨hk, hshape⟩ | ⟨hk, hshape⟩
  · have hk' : tag = 0 := by simpa using hk
    subst tag
    rcases nil_or_adjoin (refill a s stack) with hz | ⟨u, rest, hu⟩
    · simp [step, hz] at h
    · have he : adjoin ⟪concat (childrenWord a u) ⟪s, 0⟫, 0⟫ rest = adjoin ⟪word, k⟫ 0 := by
        simpa [step, hu] using h
      obtain ⟨hp, _⟩ := (adjoin_inj _ _ _ _).mp he
      have hp' : concat (childrenWord a u) ⟪s, 0⟫ = word ∧ (0 : M) = k := by simpa using hp
      obtain ⟨hraw, _⟩ := refill_typed (carrier false a b) (carrier true a b)
        a s stack u rest (by simpa using hshape) hs hu
      have hsu := (refill_sound a s stack u rest hu).1
      exact Or.inl ⟨hp'.2.symm, u, hraw, by simpa [constructor, hsu] using hp'.1.symm⟩
  · have hk' : tag = 1 := by simpa using hk
    subst tag
    rcases nil_or_adjoin (refill b s stack) with hz | ⟨u, rest, hu⟩
    · simp [step, hz] at h
    · have he : adjoin ⟪concat (childrenWord b u) ⟪s, 1⟫, 1⟫ rest = adjoin ⟪word, k⟫ 0 := by
        simpa [step, hu] using h
      obtain ⟨hp, _⟩ := (adjoin_inj _ _ _ _).mp he
      have hp' : concat (childrenWord b u) ⟪s, 1⟫ = word ∧ (1 : M) = k := by simpa using hp
      obtain ⟨hraw, _⟩ := refill_typed (carrier false a b) (carrier true a b)
        b s stack u rest (by simpa using hshape) hs hu
      have hsu := (refill_sound b s stack u rest hu).1
      exact Or.inr ⟨hp'.2.symm, u, hraw, by simpa [constructor, hsu] using hp'.1.symm⟩

/-- Every accepted literal word has a last-record root and an ordered polynomial tuple of
accepted child words. -/
theorem carrier_decomposition (formula : Bool) (a b : RawPolynomial) (word : M)
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃ u : M, (rawCarrier (carrier false a b) (carrier true a b)
      (if formula then b else a)).val.Evalb ![u] ∧
      word = constructor formula (if formula then b else a) u := by
  rcases Words.nil_or_snoc word with hz | ⟨prefixWord, record, he⟩
  · subst word
    exact False.elim (not_carrier_nil formula a b hw)
  · subst word
    obtain ⟨hcoeff, hrun⟩ := (carrier_eval formula a b _).mp hw
    have hr : (recordCarrier a b).val.Evalb ![record] := by
      have hh := (FiniteSigmaOne.allEntriesCondition_eval (recordCarrier a b) (concat prefixWord record)).mp
        ((FiniteSigmaOne.finite_membership_model (recordCarrier a b) (concat prefixWord record)).mpr hcoeff)
      simpa using hh (len prefixWord) (by simp)
    have hpref : runPrefix a b (concat prefixWord record) (len prefixWord) 1 = run a b prefixWord 1 := by
      exact prefix_congr a b (concat prefixWord record) prefixWord (len prefixWord) 1
        (fun i hi => concat_nth_lt prefixWord record hi)
    have hv := prefix_stack_valid a b (concat prefixWord record) (len prefixWord) hcoeff (by simp)
    rw [hpref] at hv
    rw [run_snoc] at hrun
    rcases zero_or_succ (run a b prefixWord 1) with hz | ⟨stack, hs⟩
    · simp [hz] at hrun
    · have hst : (stackCarrier (carrier false a b) (carrier true a b)).val.Evalb ![stack] := by
        rcases hv with hv | hv
        · simp [hs] at hv
        · simpa [hs] using hv
      rw [hs] at hrun
      have hroot := step_root a b record stack (concat prefixWord record) (if formula then 1 else 0) hr hst hrun
      cases formula
      · rcases hroot with ⟨_, u, hu, he⟩ | ⟨hz, _⟩
        · exact ⟨u, hu, he⟩
        · simp at hz
      · rcases hroot with ⟨hz, _⟩ | ⟨_, u, hu, he⟩
        · simp at hz
        · exact ⟨u, hu, he⟩

/-- Ordered child words are recovered by running their literal common runPrefix, so equal
constructor words have equal raw inputs. -/
theorem constructor_injective (formula : Bool) (a b q : RawPolynomial) (u v : M)
    (hu : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u])
    (hv : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![v])
    (he : constructor formula q u = constructor formula q v) : u = v := by
  obtain ⟨hw, hr⟩ := Words.snoc_injective (childrenWord q u) (childrenWord q v)
    ⟪shape q u, if formula then 1 else 0⟫ ⟪shape q v, if formula then 1 else 0⟫ he
  have hshape : shape q u = shape q v := by
    simpa using congrArg (pi₁ : M → M) hr
  have hstack : childStack q u 0 = childStack q v 0 := by
    have hl : run a b (childrenWord q u) 1 = childStack q u 0 + 1 := by
      simpa using children_run a b q u 0 hu
    have hr : run a b (childrenWord q v) 1 = childStack q v 0 + 1 := by
      simpa using children_run a b q v 0 hv
    rw [hw] at hl
    exact add_right_cancel (hl.symm.trans hr)
  have hl := refill_shape q u 0 hu
  rw [hshape, hstack] at hl
  have hr := refill_shape q v 0 hv
  exact ((adjoin_inj _ _ _ _).mp (hl.symm.trans hr)).1

/-- The final record distinguishes the two output sorts in PA. -/
theorem constructor_sorts_disjoint (a b : RawPolynomial) (u v : M) :
    constructor false a u ≠ constructor true b v := by
  intro he
  obtain ⟨_, hr⟩ := Words.snoc_injective (childrenWord a u) (childrenWord b v)
    ⟪shape a u, 0⟫ ⟪shape b v, 1⟫ he
  have hz := congrArg (pi₂ : M → M) hr
  simp at hz

/-- Literal term and formula carriers are disjoint before quotienting. -/
theorem carrier_sorts_disjoint (a b : RawPolynomial) (word : M)
    (ht : (carrier false a b).val.Evalb ![word])
    (hf : (carrier true a b).val.Evalb ![word]) : False := by
  have he := ((carrier_eval false a b word).mp ht).2.symm.trans
    ((carrier_eval true a b word).mp hf).2
  have hb := ((adjoin_inj _ _ _ _).mp (add_right_cancel he)).1
  have hk := congrArg (pi₂ : M → M) hb
  simp at hk

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
