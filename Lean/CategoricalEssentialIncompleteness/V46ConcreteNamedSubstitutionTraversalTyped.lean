import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversalConstructors

/-! Positive typed-stack invariants for a numerical traversal. Local root
closure is supplied by the concrete root equations; all nonstandard-length
invariant witnesses are constructed by internal Sigma-one induction. -/
noncomputable section
local instance primitiveNamedTraversalTypedDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
open SyntacticSyntax SyntacticSyntax.Coding

def statusGraph (X Y : Carrier) : 𝚺₁.Semisentence 1 :=
  let S := stackCarrier X Y
  .mkSigma “state. state = 0 ∨ ∃ stack, !subDef.val stack state 1 ∧
    state ≠ 0 ∧ !S.val stack”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3)
  (f g : M → M → M) [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G]
  (param : M) (X Y : Carrier)
  (ht : ∀ u : M,(rawCarrier X Y a).val.Evalb ![u] → X.val.Evalb ![f param u])
  (hf : ∀ u : M,(rawCarrier X Y b).val.Evalb ![u] → Y.val.Evalb ![g param u])
local instance primitiveNamedTraversalTypedModelDecidableEq : DecidableEq M := Classical.decEq M

@[simp] theorem statusGraph_eval (state : M) :
    (statusGraph X Y).val.Evalb ![state] ↔
      state = 0 ∨ (state ≠ 0 ∧ (stackCarrier X Y).val.Evalb ![state - 1]) := by
  simp [statusGraph]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
instance status_definable : 𝚺₁.DefinablePred
    (fun state : M => (statusGraph X Y).val.Evalb ![state]) := by
  refine ⟨(statusGraph X Y).rew Rew.emb,?_⟩
  intro v
  have hv : ![v 0] = v := by funext i; fin_cases i; rfl
  simp [hv]

@[simp] theorem statusGraph_zero : (statusGraph X Y).val.Evalb (M := M) ![0] := by simp
@[simp] theorem statusGraph_initial : (statusGraph X Y).val.Evalb (M := M) ![1] := by simp

include ht hf

theorem step_status (record state : M)
    (hr : (recordCarrier a b).val.Evalb ![record])
    (hs : (statusGraph X Y).val.Evalb ![state]) :
    (statusGraph X Y).val.Evalb ![step a b f g param record state] := by
  rcases (statusGraph_eval X Y state).mp hs with hz | ⟨hn,hstack⟩
  · simp [hz]
  · rcases (recordCarrier_eval a b record).mp hr with ⟨hk,hshape⟩ | ⟨hk,hshape⟩
    · rcases nil_or_adjoin (refill a (π₁ record) (state - 1)) with he | ⟨u,rest,he⟩
      · simp [step,hn,hk,he]
      · obtain ⟨hu,hrs⟩ := refill_typed X Y a (π₁ record) (state - 1) u rest hshape hstack he
        have hx := ht u hu
        have hout : (stackCarrier X Y).val.Evalb ![adjoin ⟪f param u,0⟫ rest] := by
          simp [stackCarrier_adjoin,blockCarrier_eval,hx,hrs]
        simp [step,hn,hk,he,hout]
    · rcases nil_or_adjoin (refill b (π₁ record) (state - 1)) with he | ⟨u,rest,he⟩
      · simp [step,hn,hk,he]
      · obtain ⟨hu,hrs⟩ := refill_typed X Y b (π₁ record) (state - 1) u rest hshape hstack he
        have hy := hf u hu
        have hout : (stackCarrier X Y).val.Evalb ![adjoin ⟪g param u,1⟫ rest] := by
          simp [stackCarrier_adjoin,blockCarrier_eval,hy,hrs]
        simp [step,hn,hk,he,hout]

/-- Only positive witnesses to coefficient and payload membership occur
in this invariant. No test decides either of these Sigma-one predicates. -/
theorem run_status (word : M)
    (hc : (coefficients a b).val.Evalb ![word]) :
    (statusGraph X Y).val.Evalb ![run a b F G f g param word 1] := by
  have hr : ∀ i < len word,(recordCarrier a b).val.Evalb ![nth word i] :=
    (FiniteSigmaOne.allEntriesCondition_eval (recordCarrier a b) word).mp
      ((FiniteSigmaOne.finite_membership_model (recordCarrier a b) word).mpr hc)
  have h : ∀ n ≤ len word,
      (statusGraph X Y).val.Evalb ![runPrefix a b F G f g param word n 1] := by
    intro n hn
    induction n using ISigma1.sigma1_succ_induction
    · apply HierarchySymbol.Definable.imp (by definability)
      exact HierarchySymbol.DefinablePred.comp (status_definable X Y) (by definability)
    case zero => simp
    case succ n ih =>
      have hlt : n < len word := Arithmetic.succ_le_iff_lt.mp hn
      have hs := ih (le_trans (by simp) hn)
      rw [prefix_succ]
      exact step_status a b f g param X Y ht hf (nth word n)
        (runPrefix a b F G f g param word n 1) (hr n hlt) hs
  exact h (len word) le_rfl

/-- The success shape proved independently from numerical parsing turns
the positive stack invariant into actual output carrier preservation. -/
theorem output_typed (formula : Bool) (word : M)
    (hw : (Postfix.carrier formula a b).val.Evalb ![word]) :
    (if formula then Y else X).val.Evalb ![output a b F G f g param word] := by
  have hc := ((Postfix.carrier_eval formula a b word).mp hw).1
  have hs := run_status a b F G f g param X Y ht hf word hc
  have hg := accepted_good a b F G f g param formula word hw
  rw [Good] at hg
  rw [hg] at hs
  cases formula <;> simpa [stackCarrier_adjoin,blockCarrier_eval] using hs

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution.Traversal
