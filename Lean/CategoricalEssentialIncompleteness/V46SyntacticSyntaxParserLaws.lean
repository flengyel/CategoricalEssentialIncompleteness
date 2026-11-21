/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParser
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws

/-! # Postfix constructors are accepted and preserve every stack frame -/

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
local instance : DecidableEq M := Classical.decEq M

/-- A successful step never reads past the existing consumed stack. -/
theorem step_frame (a b : RawPolynomial) (record stack out tail : M)
    (h : step a b record (stack + 1) = out + 1) :
    step a b record (Words.append stack tail + 1) = Words.append out tail + 1 := by
  by_cases hk₀ : π₂ record = 0
  · rcases nil_or_adjoin (refill a (π₁ record) stack) with hl | ⟨u, rest, hl⟩
    · simp [step, hk₀, hl] at h
    · have hout : out = adjoin ⟪concat (childrenWord a u) record, 0⟫ rest := by
        symm
        simpa [step, hk₀, hl] using h
      rw [hout]
      simp [step, hk₀, refill_frame a (π₁ record) stack u rest tail hl]
  · by_cases hk₁ : π₂ record = 1
    · rcases nil_or_adjoin (refill b (π₁ record) stack) with hr | ⟨u, rest, hr⟩
      · simp [step, hk₁, hr] at h
      · have hout : out = adjoin ⟪concat (childrenWord b u) record, 1⟫ rest := by
          symm
          simpa [step, hk₁, hr] using h
        rw [hout]
        simp [step, hk₁, refill_frame b (π₁ record) stack u rest tail hr]
    · simp [step, hk₀, hk₁] at h

/-- The frame theorem is proved by Pi-one induction on the number of consumed records,
including nonstandard runPrefix lengths. -/
theorem prefix_frame (a b : RawPolynomial) (word n stack out tail : M)
    (h : runPrefix a b word n (stack + 1) = out + 1) :
    runPrefix a b word n (Words.append stack tail + 1) = Words.append out tail + 1 := by
  induction n using ISigma1.pi1_succ_induction generalizing stack out tail
  · definability
  case zero =>
    have ho : stack = out := by simpa using h
    simp [ho]
  case succ n ih =>
    rcases zero_or_succ (runPrefix a b word n (stack + 1)) with hz | ⟨prev, hp⟩
    · simp [prefix_succ, hz] at h
    · rw [prefix_succ, hp] at h
      rw [prefix_succ, ih stack prev tail hp]
      exact step_frame a b (nth word n) prev out tail h

theorem run_frame (a b : RawPolynomial) (word stack out tail : M)
    (h : run a b word (stack + 1) = out + 1) :
    run a b word (Words.append stack tail + 1) = Words.append out tail + 1 :=
  prefix_frame a b word (len word) stack out tail h

/-- Membership of an appended word preserves all explicit coefficient
witnesses; this argument splits the bounded index, not the predicate. -/
theorem finiteMembership_append (C : Carrier) (word suffix : M)
    (hw : (FiniteSigmaOne.finiteMembership C).val.Evalb ![word])
    (hs : (FiniteSigmaOne.finiteMembership C).val.Evalb ![suffix]) :
    (FiniteSigmaOne.finiteMembership C).val.Evalb ![Words.append word suffix] := by
  rw [← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval] at hw hs ⊢
  intro i hi
  by_cases hil : i < len word
  · simpa only [Words.nth_append_left word suffix i hil] using hw i hil
  · have hle : len word ≤ i := le_of_not_gt hil
    obtain ⟨j, rfl⟩ := exists_add_of_le hle
    have hj : j < len suffix := by simpa using hi
    simpa only [Words.nth_append_right] using hs j hj

theorem finiteMembership_snoc (C : Carrier) (word record : M)
    (hw : (FiniteSigmaOne.finiteMembership C).val.Evalb ![word])
    (hr : C.val.Evalb ![record]) :
    (FiniteSigmaOne.finiteMembership C).val.Evalb ![concat word record] := by
  have hs : (FiniteSigmaOne.finiteMembership C).val.Evalb ![adjoin record (0 : M)] := by
    rw [← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval]
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    simpa [hi0] using hr
  simpa only [Words.append_singleton] using finiteMembership_append C word (adjoin record (0 : M)) hw hs

/-- Parsing the child words in their order produces precisely the stack consumed by the
polynomial refiller. -/
theorem children_run (a b q : RawPolynomial) (u stack : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u]) :
    run a b (childrenWord q u) (stack + 1) = childStack q u stack + 1 := by
  induction q generalizing u stack with
  | term =>
      have hr := ((carrier_eval false a b u).mp h).2
      have hh := run_frame a b u 0 (adjoin ⟪u, 0⟫ 0) stack (by simpa using hr)
      simpa [childrenWord, childStack] using hh
  | formula =>
      have hr := ((carrier_eval true a b u).mp h).2
      have hh := run_frame a b u 0 (adjoin ⟪u, 1⟫ 0) stack (by simpa using hr)
      simpa [childrenWord, childStack] using hh
  | coefficient C => simp [childrenWord, childStack]
  | unit => simp [childrenWord, childStack]
  | product c d ic id =>
      obtain ⟨x, y, rfl, hx, hy⟩ :=
        (rawCarrier_product_eval (carrier false a b) (carrier true a b) c d u).mp h
      simp [childrenWord, childStack, run_append, ic x stack hx, id y (childStack c x stack) hy]
  | sum c d ic id =>
      rcases (rawCarrier_sum_eval (carrier false a b) (carrier true a b) c d u).mp h with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · simpa [childrenWord, childStack] using ic x stack hx
      · simpa [childrenWord, childStack] using id y stack hy

/-- Coefficient assertions for child words combine into the coefficient assertion for
their concatenated blocks. -/
theorem children_coefficients (a b q : RawPolynomial) (u : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u]) :
    (coefficients a b).val.Evalb ![childrenWord q u] := by
  induction q generalizing u with
  | term => exact ((carrier_eval false a b u).mp h).1
  | formula => exact ((carrier_eval true a b u).mp h).1
  | coefficient C =>
      rw [coefficients, ← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval]
      simp [childrenWord]
  | unit =>
      rw [coefficients, ← FiniteSigmaOne.finite_membership_model, FiniteSigmaOne.allEntriesCondition_eval]
      simp [childrenWord]
  | product c d ic id =>
      obtain ⟨x, y, rfl, hx, hy⟩ :=
        (rawCarrier_product_eval (carrier false a b) (carrier true a b) c d u).mp h
      simpa [childrenWord, coefficients] using finiteMembership_append (recordCarrier a b)
        (childrenWord c x) (childrenWord d y) (ic x hx) (id y hy)
  | sum c d ic id =>
      rcases (rawCarrier_sum_eval (carrier false a b) (carrier true a b) c d u).mp h with
        ⟨x, rfl, hx⟩ | ⟨y, rfl, hy⟩
      · simpa [childrenWord] using ic x hx
      · simpa [childrenWord] using id y hy

/-- Every term constructor is accepted by the postfix carrier, with no tree representation
substituted for that carrier. -/
theorem term_constructor_carrier (a b : RawPolynomial) (u : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) a).val.Evalb ![u]) :
    (carrier false a b).val.Evalb ![constructor false a u] := by
  apply (carrier_eval false a b _).mpr
  constructor
  · exact finiteMembership_snoc (recordCarrier a b) (childrenWord a u) ⟪shape a u, 0⟫
      (children_coefficients a b a u h) (by simp [shape_carrier a u h])
  · have hc : run a b (childrenWord a u) 1 = childStack a u 0 + 1 := by
      simpa using children_run a b a u 0 h
    rw [constructor, run_snoc, hc]
    exact step_term_constructor a b u 0 h

theorem formula_constructor_carrier (a b : RawPolynomial) (u : M)
    (h : (rawCarrier (carrier false a b) (carrier true a b) b).val.Evalb ![u]) :
    (carrier true a b).val.Evalb ![constructor true b u] := by
  apply (carrier_eval true a b _).mpr
  constructor
  · exact finiteMembership_snoc (recordCarrier a b) (childrenWord b u) ⟪shape b u, 1⟫
      (children_coefficients a b b u h) (by simp [shape_carrier b u h])
  · have hc : run a b (childrenWord b u) 1 = childStack b u 0 + 1 := by
      simpa using children_run a b b u 0 h
    rw [constructor, run_snoc, hc]
    exact step_formula_constructor a b u 0 h

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix
