import CategoricalEssentialIncompleteness.V46NamedArithmeticClosedSubstitution

/-! PA itself proves closed-replacement admissibility for the independent
free-for algorithm, and existence of its actual typed option result. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticClosedSubstitution
open ConcreteNamedSubstitution
variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

 def closedReplacementSentence : ArithmeticSentence :=
  let Tm := Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let Fm := Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
  let FV := freeVariablesGraph V σ π d
  let A := substitutionFreeForGraph V σ π d
  let R := substitutionResultGraph V σ π d
  “∀ x replacement word, !Tm.val replacement → !FV.val 0 replacement → !Fm.val word →
    !A.val 1 x replacement word ∧ ∃ out res, !Fm.val out ∧ !pairDef.val res out 1 ∧ !R.val res x replacement word”

 theorem closedReplacementSentence_eval
    {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (closedReplacementSentence V σ π d).Evalb (M := M) ![] ↔
      ∀ x replacement word : M,
        (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![replacement] →
        freeVariables V σ π d replacement = 0 →
        (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] →
          substitutionFreeFor V σ π d x replacement word = 1 ∧
            ∃ out : M,(Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
              (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![out] ∧
                substitutionResult V σ π d x replacement word = ok out := by
  simp [closedReplacementSentence,ok,eq_comm]

 theorem closedReplacement_PA : 𝗣𝗔 ⊢ closedReplacementSentence V σ π d := by
  apply complete.{0} 𝗣𝗔
  intro M _ hM
  rw [models_iff,closedReplacementSentence_eval]
  intro x replacement word hrep hclosed hw
  exact ⟨substitutionFreeFor_closed V σ π d x replacement word hrep hclosed hw,
    substitutionResult_closed V σ π d x replacement word hrep hclosed hw⟩

end CategoricalEssentialIncompleteness.V46.NamedArithmeticClosedSubstitution
