/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticPredicates
public import FailureOfComposition.ConcreteGodelRE

/-! # Connected restriction idempotents in the unprimed syntactic category

In Appendix D, local connectedness would detect equality after restriction to every connected
idempotent. On the number object a connected idempotent decides each complementary pair of
arithmetic predicates.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (zero_comp)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Relative implication between domain predicates, in every model of the theory. -/
def Implies (C D : Carrier) : Prop :=
  ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M), C.val.Evalb ![x] → D.val.Evalb ![x]

theorem restricted_program_model (C : Carrier) (q : ProgramQuotient T)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x y : M) :
    SyntacticModel.programRelation T M (q * predicateClass T C) x y ↔
      C.val.Evalb ![x] ∧ SyntacticModel.programRelation T M q x y := by
  rw [SyntacticModel.programRelation_mul]
  constructor
  · rintro ⟨z, hc, hq⟩
    obtain ⟨hx, rfl⟩ := (predicateClass_model T C M x z).mp hc
    exact ⟨hx, hq⟩
  · rintro ⟨hc, hq⟩
    exact ⟨x, (predicateClass_model T C M x x).mpr ⟨hc, rfl⟩, hq⟩

theorem predicate_le (C D : Carrier) : predicateIdem T C ≤ predicateIdem T D ↔ Implies T C D := by
  rw [Idem.le_def]
  constructor
  · intro he M _ _ x hc
    have h := congrArg (fun f : omegaObject T ⟶ omegaObject T => f.val) he
    change predicateClass T D * predicateClass T C = predicateClass T C at h
    have hx := (predicateClass_model T C M x x).mpr ⟨hc, rfl⟩
    rw [← h] at hx
    exact ((predicateClass_model T D M x x).mp ((restricted_program_model T _ _ M x x).mp hx).2).1
  · intro h
    apply CodedHom.ext
    apply programClass_ext T
    intro M _ _ x y
    change SyntacticModel.programRelation T M (predicateClass T D * predicateClass T C) x y ↔ _
    rw [restricted_program_model, predicateClass_model]
    change _ ↔ SyntacticModel.programRelation T M (predicateClass T C) x y
    rw [predicateClass_model]
    exact ⟨fun ⟨hx, _, he⟩ => ⟨hx, he⟩, fun ⟨hx, he⟩ => ⟨hx, h M x hx, he⟩⟩

theorem predicate_bot (C : Carrier)
    (h : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M), ¬C.val.Evalb ![x]) :
    predicateIdem T C = ⊥ := by
  apply bot_unique
  obtain ⟨D, hD⟩ := omegaIdem_is_predicate T (⊥ : Idem (omegaObject T))
  rw [hD, predicate_le]
  exact fun M _ _ x hx => (h M x hx).elim

attribute [local irreducible] predicateIdem

private def conjunction (C P : Carrier) : Carrier := .mkSigma “x. !C.val x ∧ !P.val x”

private theorem conjunction_eval {M : Type} [ORingStructure M] (C P : Carrier) (x : M) :
    (conjunction C P).val.Evalb ![x] ↔ C.val.Evalb ![x] ∧ P.val.Evalb ![x] := by
  simp [conjunction]

attribute [local irreducible] conjunction

/-- Connectedness decides a partition by two complementary domain formulas. -/
theorem connected_decides (C P N : Carrier) (hc : Connected (predicateIdem T C))
    (hPN : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M),
      N.val.Evalb ![x] ↔ ¬P.val.Evalb ![x]) : Implies T C P ∨ Implies T C N := by
  let L := conjunction C P
  let R := conjunction C N
  have hl {M : Type} [ORingStructure M] (x : M) : L.val.Evalb ![x] ↔
      C.val.Evalb ![x] ∧ P.val.Evalb ![x] := conjunction_eval C P x
  have hr {M : Type} [ORingStructure M] (x : M) : R.val.Evalb ![x] ↔
      C.val.Evalb ![x] ∧ N.val.Evalb ![x] := conjunction_eval C N x
  have htop : predicateIdem T C = predicateIdem T L ⊔ predicateIdem T R := by
    apply le_antisymm
    · obtain ⟨D, hD⟩ := omegaIdem_is_predicate T (predicateIdem T L ⊔ predicateIdem T R)
      have hLD := (predicate_le T L D).mp (by rw [← hD]; exact le_sup_left)
      have hRD := (predicate_le T R D).mp (by rw [← hD]; exact le_sup_right)
      rw [hD, predicate_le]
      intro M _ _ x hx
      by_cases hp : P.val.Evalb ![x]
      · exact hLD M x ((hl x).mpr ⟨hx, hp⟩)
      · exact hRD M x ((hr x).mpr ⟨hx, (hPN M x).mpr hp⟩)
    · exact sup_le ((predicate_le T L C).mpr (fun _ _ _ x hx => ((hl x).mp hx).1))
        ((predicate_le T R C).mpr (fun _ _ _ x hx => ((hr x).mp hx).1))
  have hbot : predicateIdem T L ⊓ predicateIdem T R = ⊥ := by
    obtain ⟨D, hD⟩ := omegaIdem_is_predicate T (predicateIdem T L ⊓ predicateIdem T R)
    have hDL := (predicate_le T D L).mp (by rw [← hD]; exact inf_le_left)
    have hDR := (predicate_le T D R).mp (by rw [← hD]; exact inf_le_right)
    rw [hD]
    apply predicate_bot T D
    intro M _ _ x hx
    exact (hPN M x).mp ((hr x).mp (hDR M x hx)).2 ((hl x).mp (hDL M x hx)).2
  rcases hc _ _ htop hbot with he | he
  · right
    rw [he, bot_sup_eq] at htop
    apply (predicate_le T C N).mp
    rw [htop, predicate_le]
    exact fun _ _ _ x hx => ((hr x).mp hx).2
  · left
    rw [he, sup_bot_eq] at htop
    apply (predicate_le T C P).mp
    rw [htop, predicate_le]
    exact fun _ _ _ x hx => ((hl x).mp hx).2

/-- The partial identity on a standard numeral. -/
def numeralPredicate (n : ℕ) : Carrier := .mkSigma “x. x = !!(n)”

theorem numeralPredicate_eval {M : Type} [ORingStructure M] (n : ℕ) (x : M) :
    (numeralPredicate n).val.Evalb ![x] ↔ x = ORingStructure.numeral n := by
  simp [numeralPredicate]

theorem bounds_of_no_numeral (C : Carrier) (hc : Connected (predicateIdem T C))
    (hn : ¬∃ n, Implies T C (numeralPredicate n)) (t : ℕ)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) (hx : C.val.Evalb ![x]) :
    ORingStructure.numeral t ≤ x := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗥₀ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  by_contra! hlt
  obtain ⟨i, hi⟩ := Arithmetic.lt_numeral_iff.mp hlt
  let N : Carrier := .mkSigma “x. x ≠ !!(i.val)”
  have hn' := (connected_decides T C (numeralPredicate i) N hc
    (fun K _ _ y => by simp [N, numeralPredicate])).resolve_left fun h => hn ⟨i, h⟩
  have hneg := hn' M x hx
  simp [N, hi] at hneg

end CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains
