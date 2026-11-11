/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticNamedAxiomComparisonBasic

/-! # Native equality proofs for the source arithmetic equality axioms -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
open NamedArithmeticSignature ArithmeticNamedProofConnectives
local instance equalityComparisonDecidableEq : DecidableEq Fm := Classical.decEq _
variable (A : SyntacticPredicates.Carrier)
local notation "D" => SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A
local notation "S" => ArithmeticNamedProofConnectives.system A

private theorem native (φ : Fm) (h : S ⊢ φ) : D φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mp h
private theorem propositional (φ : Fm) (h : D φ) : S ⊢ φ :=
  (NamedHilbertPropositional.system_provable_iff functionSymbols relationSymbols bound
    (ArithmeticNamedProofConnectives.system A) φ).mpr h
private theorem equivalent {φ ψ : Fm} (h : S ⊢ φ 🡘 ψ) (hp : D ψ) : D φ :=
  native A _ ((K_right h) ⨀ propositional A _ hp)

private theorem substitute_add_native (r s : Tm) (x : ℕ) (t : Tm) :
    (add r s).substitute x t = add (r.substitute x t) (s.substitute x t) := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem substitute_mul_native (r s : Tm) (x : ℕ) (t : Tm) :
    (mul r s).substitute x t = mul (r.substitute x t) (s.substitute x t) := by
  change NamedFiniteSyntax.Term.app _ _ _ = NamedFiniteSyntax.Term.app _ _ _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem substitute_less_native (r s : Tm) (x : ℕ) (t : Tm) :
    (less r s).substitute x t = some (less (r.substitute x t) (s.substitute x t)) := by
  change some (NamedFiniteSyntax.Formula.relation _ _ _) =
    some (NamedFiniteSyntax.Formula.relation _ _ _)
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Symmetry uses the native equality scheme and reflexivity. -/
theorem equality_symmetry :
    D (.imp (.equal (.var 0) (.var 1)) (.equal (.var 1) (.var 0))) := by
  have he : D (.imp (.equal (.var 0) (.var 1))
      (.imp (.equal (.var 0) (.var 0)) (.equal (.var 1) (.var 0)))) :=
    .equality 2 (.equal (.var 2) (.var 0)) (.var 0) (.var 1)
      _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
  exact native A _ ((C_swap (propositional A _ he)) ⨀
    (propositional A _ (.reflexivity (.var 0))))

/-- Transitivity retains three independent variable names. -/
theorem equality_transitivity :
    D (.imp (.equal (.var 0) (.var 1))
      (.imp (.equal (.var 1) (.var 2)) (.equal (.var 0) (.var 2)))) := by
  have he : D (.imp (.equal (.var 1) (.var 2))
      (.imp (.equal (.var 0) (.var 1)) (.equal (.var 0) (.var 2)))) :=
    .equality 3 (.equal (.var 0) (.var 3)) (.var 1) (.var 2)
      _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
  exact native A _ (C_swap (propositional A _ he))

theorem eqRefl_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.refl ℒₒᵣ)) :=
  .generalization 0 (.reflexivity (.var 0))

theorem eqSymm_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.symm ℒₒᵣ)) := by
  have h := all_equivalence A 0 (all_equivalence A 1
    (implication A (“#1 = #0” : ArithmeticSemisentence 2)
      (“#0 = #1” : ArithmeticSemisentence 2) 2 ![1,0] Empty.elim))
  exact equivalent A h (.generalization 0 (.generalization 1 (equality_symmetry A)))

theorem eqTrans_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.trans ℒₒᵣ)) := by
  have ho := implication A (“#2 = #1” : ArithmeticSemisentence 3)
    (“#1 = #0 → #2 = #0” : ArithmeticSemisentence 3) 3 ![2,1,0] Empty.elim
  have hi := implication A (“#1 = #0” : ArithmeticSemisentence 3)
    (“#2 = #0” : ArithmeticSemisentence 3) 3 ![2,1,0] Empty.elim
  have h := all_equivalence A 0 (all_equivalence A 1 (all_equivalence A 2
    (E_trans ho (ECC_of_E_of_E E_id hi))))
  exact equivalent A h (.generalization 0 (.generalization 1
    (.generalization 2 (equality_transitivity A))))


private def extensionalityPremises : ArithmeticSemisentence 4 :=
  .and “#0 = #2” (.and “#1 = #3” .verum)

private def namedExtensionalityPremises : Fm :=
  ArithmeticNamedTranslation.conjunction (.equal (.var 3) (.var 1))
    (ArithmeticNamedTranslation.conjunction (.equal (.var 2) (.var 0))
      ArithmeticNamedTranslation.truth)

private theorem addExt_native :
    D (.imp namedExtensionalityPremises
      (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 0)))) := by
  have h₁ : D (.imp (.equal (.var 3) (.var 1))
      (.imp (.equal (add (.var 3) (.var 2)) (add (.var 3) (.var 2)))
        (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 2))))) :=
    .equality 4 (.equal (add (.var 3) (.var 2)) (add (.var 4) (.var 2)))
      (.var 3) (.var 1) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_add_native,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_add_native,NamedFiniteSyntax.Term.substitute])
  have h₂ : D (.imp (.equal (.var 2) (.var 0))
      (.imp (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 2)))
        (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 0))))) :=
    .equality 4 (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 4)))
      (.var 2) (.var 0) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_add_native,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_add_native,NamedFiniteSyntax.Term.substitute])
  have h₃ : S ⊢ (.equal (.var 3) (.var 1)) 🡒
      (.equal (add (.var 3) (.var 2)) (add (.var 1) (.var 2))) :=
    (C_swap (propositional A _ h₁)) ⨀
      (propositional A _ (.reflexivity (add (.var 3) (.var 2))))
  apply native A _
  apply FiniteContext.deduct'
  have h31 : [namedExtensionalityPremises] ⊢[S] (.equal (.var 3) (.var 1)) :=
    K_left FiniteContext.by_axm₀
  have h20 : [namedExtensionalityPremises] ⊢[S] (.equal (.var 2) (.var 0)) :=
    K_left (K_right FiniteContext.by_axm₀)
  exact (FiniteContext.of' (propositional A _ h₂)) ⨀ h20 ⨀
    ((FiniteContext.of' h₃) ⨀ h31)

theorem eqAddExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .add)) := by
  have he := implication A extensionalityPremises
    (“#0 + #1 = #2 + #3” : ArithmeticSemisentence 4)
    4 ![3,2,1,0] Empty.elim
  have h := all_equivalence A 0 (all_equivalence A 1
    (all_equivalence A 2 (all_equivalence A 3 he)))
  exact equivalent A h (.generalization 0 (.generalization 1
    (.generalization 2 (.generalization 3 (addExt_native A)))))

private theorem mulExt_native :
    D (.imp namedExtensionalityPremises
      (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 0)))) := by
  have h₁ : D (.imp (.equal (.var 3) (.var 1))
      (.imp (.equal (mul (.var 3) (.var 2)) (mul (.var 3) (.var 2)))
        (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 2))))) :=
    .equality 4 (.equal (mul (.var 3) (.var 2)) (mul (.var 4) (.var 2)))
      (.var 3) (.var 1) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_mul_native,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_mul_native,NamedFiniteSyntax.Term.substitute])
  have h₂ : D (.imp (.equal (.var 2) (.var 0))
      (.imp (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 2)))
        (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 0))))) :=
    .equality 4 (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 4)))
      (.var 2) (.var 0) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_mul_native,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,substitute_mul_native,NamedFiniteSyntax.Term.substitute])
  have h₃ : S ⊢ (.equal (.var 3) (.var 1)) 🡒
      (.equal (mul (.var 3) (.var 2)) (mul (.var 1) (.var 2))) :=
    (C_swap (propositional A _ h₁)) ⨀
      (propositional A _ (.reflexivity (mul (.var 3) (.var 2))))
  apply native A _
  apply FiniteContext.deduct'
  have h31 : [namedExtensionalityPremises] ⊢[S] (.equal (.var 3) (.var 1)) :=
    K_left FiniteContext.by_axm₀
  have h20 : [namedExtensionalityPremises] ⊢[S] (.equal (.var 2) (.var 0)) :=
    K_left (K_right FiniteContext.by_axm₀)
  exact (FiniteContext.of' (propositional A _ h₂)) ⨀ h20 ⨀
    ((FiniteContext.of' h₃) ⨀ h31)

theorem eqMulExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .mul)) := by
  have he := implication A extensionalityPremises
    (“#0 * #1 = #2 * #3” : ArithmeticSemisentence 4)
    4 ![3,2,1,0] Empty.elim
  have h := all_equivalence A 0 (all_equivalence A 1
    (all_equivalence A 2 (all_equivalence A 3 he)))
  exact equivalent A h (.generalization 0 (.generalization 1
    (.generalization 2 (.generalization 3 (mulExt_native A)))))

private theorem equalExt_native :
    D (.imp namedExtensionalityPremises
      (.imp (NamedFiniteSyntax.Formula.equal (.var 3) (.var 2)) (NamedFiniteSyntax.Formula.equal (.var 1) (.var 0)))) := by
  have h₁ : D (.imp (.equal (.var 3) (.var 1))
      (.imp (NamedFiniteSyntax.Formula.equal (.var 3) (.var 2)) (NamedFiniteSyntax.Formula.equal (.var 1) (.var 2)))) :=
    .equality 4 (NamedFiniteSyntax.Formula.equal (.var 4) (.var 2))
      (.var 3) (.var 1) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
  have h₂ : D (.imp (.equal (.var 2) (.var 0))
      (.imp (NamedFiniteSyntax.Formula.equal (.var 1) (.var 2)) (NamedFiniteSyntax.Formula.equal (.var 1) (.var 0)))) :=
    .equality 4 (NamedFiniteSyntax.Formula.equal (.var 1) (.var 4))
      (.var 2) (.var 0) _ _ True.intro True.intro
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
      (by simp [NamedFiniteSyntax.Formula.substitute,NamedFiniteSyntax.Term.substitute])
  apply native A _
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  have h31 : [(NamedFiniteSyntax.Formula.equal (.var 3) (.var 2)),namedExtensionalityPremises] ⊢[S]
      (.equal (.var 3) (.var 1)) := K_left FiniteContext.by_axm₁
  have h20 : [(NamedFiniteSyntax.Formula.equal (.var 3) (.var 2)),namedExtensionalityPremises] ⊢[S]
      (.equal (.var 2) (.var 0)) := K_left (K_right FiniteContext.by_axm₁)
  exact (FiniteContext.of' (propositional A _ h₂)) ⨀ h20 ⨀
    ((FiniteContext.of' (propositional A _ h₁)) ⨀ h31 ⨀ FiniteContext.by_axm₀)

theorem eqEqRelExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.relExt .eq)) := by
  have ho := implication A extensionalityPremises
    (“#0 = #1 → #2 = #3” : ArithmeticSemisentence 4) 4 ![3,2,1,0] Empty.elim
  have hi := implication A (“#0 = #1” : ArithmeticSemisentence 4)
    (“#2 = #3” : ArithmeticSemisentence 4) 4 ![3,2,1,0] Empty.elim
  have h := all_equivalence A 0 (all_equivalence A 1
    (all_equivalence A 2 (all_equivalence A 3
      (E_trans ho (ECC_of_E_of_E E_id hi)))))
  exact equivalent A h (.generalization 0 (.generalization 1
    (.generalization 2 (.generalization 3 (equalExt_native A)))))

private theorem lessExt_native :
    D (.imp namedExtensionalityPremises
      (.imp (less (.var 3) (.var 2)) (less (.var 1) (.var 0)))) := by
  have h₁ : D (.imp (.equal (.var 3) (.var 1))
      (.imp (less (.var 3) (.var 2)) (less (.var 1) (.var 2)))) :=
    .equality 4 (less (.var 4) (.var 2))
      (.var 3) (.var 1) _ _ True.intro True.intro
      (by simp [substitute_less_native,NamedFiniteSyntax.Term.substitute])
      (by simp [substitute_less_native,NamedFiniteSyntax.Term.substitute])
  have h₂ : D (.imp (.equal (.var 2) (.var 0))
      (.imp (less (.var 1) (.var 2)) (less (.var 1) (.var 0)))) :=
    .equality 4 (less (.var 1) (.var 4))
      (.var 2) (.var 0) _ _ True.intro True.intro
      (by simp [substitute_less_native,NamedFiniteSyntax.Term.substitute])
      (by simp [substitute_less_native,NamedFiniteSyntax.Term.substitute])
  apply native A _
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  have h31 : [(less (.var 3) (.var 2)),namedExtensionalityPremises] ⊢[S]
      (.equal (.var 3) (.var 1)) := K_left FiniteContext.by_axm₁
  have h20 : [(less (.var 3) (.var 2)),namedExtensionalityPremises] ⊢[S]
      (.equal (.var 2) (.var 0)) := K_left (K_right FiniteContext.by_axm₁)
  exact (FiniteContext.of' (propositional A _ h₂)) ⨀ h20 ⨀
    ((FiniteContext.of' (propositional A _ h₁)) ⨀ h31 ⨀ FiniteContext.by_axm₀)

theorem eqLtRelExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.relExt .lt)) := by
  have ho := implication A extensionalityPremises
    (“#0 < #1 → #2 < #3” : ArithmeticSemisentence 4) 4 ![3,2,1,0] Empty.elim
  have hi := implication A (“#0 < #1” : ArithmeticSemisentence 4)
    (“#2 < #3” : ArithmeticSemisentence 4) 4 ![3,2,1,0] Empty.elim
  have h := all_equivalence A 0 (all_equivalence A 1
    (all_equivalence A 2 (all_equivalence A 3
      (E_trans ho (ECC_of_E_of_E E_id hi)))))
  exact equivalent A h (.generalization 0 (.generalization 1
    (.generalization 2 (.generalization 3 (lessExt_native A)))))

theorem eqZeroExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .zero)) := by
  have h := implication A (.verum : ArithmeticSemisentence 0)
    (“0 = 0” : ArithmeticSemisentence 0) 0 ![] Empty.elim
  exact equivalent A h (native A _ (C_of_conseq (propositional A _ (.reflexivity zero))))

theorem eqOneExt_admissible :
    D (ArithmeticNamedTranslation.translateFormula 0 ![] (Theory.Eq.funcExt .one)) := by
  have h := implication A (.verum : ArithmeticSemisentence 0)
    (“1 = 1” : ArithmeticSemisentence 0) 0 ![] Empty.elim
  exact equivalent A h (native A _ (C_of_conseq (propositional A _ (.reflexivity one))))
end CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison
