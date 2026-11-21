/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRootEquations
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInterpretation
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize

/-! # Numerical node-count comparison from constructor equations -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
open Coding Postfix
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T] in
private theorem ternaryGraph_definable (R : TernaryGraph) :
    𝚺₁.DefinableRel₃ (fun p word x : M => R.val.Evalb ![p, word, x]) := by
  have h : 𝚺₁.Definable (fun v : Fin 3 → M => R.val.Evalb v) :=
    HierarchySymbol.Defined.to_definable R (.mk (fun _ => Iff.rfl))
  exact h.of_iff fun v => by
    change R.val.Evalb ![v 0, v 1, v 2] ↔ R.val.Evalb v
    rw [(Matrix.fun_eq_vec_three v).symm]

omit [M↓[ℒₒᵣ] ⊧* T] in
private theorem pointwiseComparison_definable (H E : TernaryGraph) :
    𝚷₁.DefinablePred (fun n : M => ∀ p word x y : M,
      len word = n → H.val.Evalb ![p, word, x] → E.val.Evalb ![p, word, y] → x = y) := by
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.all
  apply HierarchySymbol.Definable.imp (by definability)
  apply HierarchySymbol.Definable.imp
  · exact HierarchySymbol.DefinableRel₃.comp (ternaryGraph_definable H)
      (by definability) (by definability) (by definability)
  · apply HierarchySymbol.Definable.imp
    · exact HierarchySymbol.DefinableRel₃.comp (ternaryGraph_definable E)
        (by definability) (by definability) (by definability)
    · definability

/-- Internal Pi-one strong induction compares candidate outputs at arbitrary model node
counts. The evaluator's root equations remain explicit arguments of this intermediate
comparison lemma; its later public application must supply their proved finite-record
laws. -/
theorem comparison_of_root_equations (hT hF : TernaryGraph)
    (hroot : A.RootEquations (M := M) hT hF)
    (eroot : A.RootEquations (M := M) (A.evaluationFormula false) (A.evaluationFormula true))
    (formula : Bool) (p word x y : M)
    (hx : (if formula then hF else hT).val.Evalb ![p, word, x])
    (hy : (A.evaluationFormula formula).val.Evalb ![p, word, y]) : x = y := by
  let Compare (formula : Bool) (n : M) : Prop := ∀ p word x y : M,
    len word = n → (if formula then hF else hT).val.Evalb ![p, word, x] →
      (A.evaluationFormula formula).val.Evalb ![p, word, y] → x = y
  have hc : ∀ n : M, Compare false n ∧ Compare true n := by
    intro n
    induction n using ISigma1.pi1_order_induction
    · dsimp [Compare]
      exact HierarchySymbol.Definable.and
        (pointwiseComparison_definable hT (A.evaluationFormula false))
        (pointwiseComparison_definable hF (A.evaluationFormula true))
    case ind n ih =>
      constructor
      · intro p word x y hlen hx hy
        obtain ⟨hp, hw, _⟩ := A.evaluation_fiber false p word y hy
        obtain ⟨u, hu, he⟩ := carrier_decomposition false a b word hw
        subst word
        obtain ⟨v, hv, hop⟩ := (hroot.1 p u x hp hu).mp hx
        obtain ⟨w, hw', eop⟩ := (eroot.1 p u y hp hu).mp hy
        have hsize : (childSizeGraph a).val.Evalb ![n, u] := by
          rw [← hlen]
          exact children_smaller false a u
        have heq : v = w := mapRaw_compare P hT hF
          (A.evaluationFormula false) (A.evaluationFormula true) a n p u v w hsize
          (fun child r s hlt hr hs => (ih (len child) hlt).1 p child r s rfl hr hs)
          (fun child r s hlt hr hs => (ih (len child) hlt).2 p child r s rfl hr hs) hv hw'
        rw [heq] at hop
        exact A.term_functional_model p w x y hop eop
      · intro p word x y hlen hx hy
        obtain ⟨hp, hw, _⟩ := A.evaluation_fiber true p word y hy
        obtain ⟨u, hu, he⟩ := carrier_decomposition true a b word hw
        subst word
        obtain ⟨v, hv, hop⟩ := (hroot.2 p u x hp hu).mp hx
        obtain ⟨w, hw', eop⟩ := (eroot.2 p u y hp hu).mp hy
        have hsize : (childSizeGraph b).val.Evalb ![n, u] := by
          rw [← hlen]
          exact children_smaller true b u
        have heq : v = w := mapRaw_compare P hT hF
          (A.evaluationFormula false) (A.evaluationFormula true) b n p u v w hsize
          (fun child r s hlt hr hs => (ih (len child) hlt).1 p child r s rfl hr hs)
          (fun child r s hlt hr hs => (ih (len child) hlt).2 p child r s rfl hr hs) hv hw'
        rw [heq] at hop
        exact A.formula_functional_model p w x y hop eop
  cases formula
  · exact (hc (len word)).1 p word x y rfl hx hy
  · exact (hc (len word)).2 p word x y rfl hx hy

end Models
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SliceAlgebra
