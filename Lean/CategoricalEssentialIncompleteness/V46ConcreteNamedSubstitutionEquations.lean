import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionPA

/-! PA sentences for the literal numerical constructor equations. The
polynomial graph below keeps both substitution parameters free and applies
the actual paired traversal independently at each ordered child. -/
noncomputable section
local instance primitiveNamedEquationsDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

def parameterMapGraph (F G : 𝚺₁.Semisentence 4) : RawPolynomial → 𝚺₁.Semisentence 4
  | .term => F
  | .formula => G
  | .coefficient _ => .mkSigma “out x replacement value. out = value”
  | .unit => .mkSigma “out x replacement value. out = 0”
  | .product a b =>
    let A := parameterMapGraph F G a
    let B := parameterMapGraph F G b
    .mkSigma “out x replacement value. ∃ l r s t, !pi₁Def.val l value ∧ !pi₂Def.val r value ∧
      !A.val s x replacement l ∧ !B.val t x replacement r ∧ !pairDef.val out s t”
  | .sum a b =>
    let A := parameterMapGraph F G a
    let B := parameterMapGraph F G b
    .mkSigma “out x replacement value. ∃ tag payload mapped, !pi₁Def.val payload value ∧ !pi₂Def.val tag value ∧
      ((tag = 0 ∧ !A.val mapped x replacement payload) ∨
        (tag ≠ 0 ∧ !B.val mapped x replacement payload)) ∧ !pairDef.val out mapped tag”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance primitiveNamedEquationsModelDecidableEq : DecidableEq M := Classical.decEq M
variable (F G : 𝚺₁.Semisentence 4) (f g : M → M → M → M)
  [𝚺₁-Function₃ f via F] [𝚺₁-Function₃ g via G]

@[simp] theorem parameterMapGraph_eval (q : RawPolynomial) (out x replacement value : M) :
    (parameterMapGraph F G q).val.Evalb ![out,x,replacement,value] ↔
      out = mapChildren (f x replacement) (g x replacement) q value := by
  induction q generalizing out value with
  | term => exact (show 𝚺₁-Function₃ f via F from inferInstance).iff
  | formula => exact (show 𝚺₁-Function₃ g via G from inferInstance).iff
  | coefficient _ => simp [parameterMapGraph,mapChildren]
  | unit => simp [parameterMapGraph,mapChildren]
  | product a b ia ib => simp [parameterMapGraph,mapChildren,ia,ib]
  | sum a b ia ib =>
      by_cases h : π₂ value = 0 <;> simp [parameterMapGraph,mapChildren,ia,ib,h]

@[simp] theorem parameterMapGraph_eval_any (q : RawPolynomial) (v : Fin 4 → M) :
    (parameterMapGraph F G q).val.Evalb v ↔
      v 0 = mapChildren (f (v 1) (v 2)) (g (v 1) (v 2)) q (v 3) := by
  have hv : ![v 0,v 1,v 2,v 3] = v := (Matrix.fun_eq_vec_four v).symm
  simpa [hv] using parameterMapGraph_eval F G f g q (v 0) (v 1) (v 2) (v 3)

end Models

private theorem constructorEquation_iff {M : Type} (P : M → Prop) (c m f r : M → M) :
    (∀ u word mapped out : M,P u → word = c u → mapped = m u →
      (out = f word ↔ out = r mapped)) ↔
      ∀ u : M,P u → f (c u) = r (m u) := by
  constructor
  · intro h u hu
    exact (h u (c u) (m u) (f (c u)) hu rfl rfl).mp rfl
  · intro h u word mapped out hu hw hm
    subst word
    subst mapped
    rw [h u hu]

private theorem parameterConstructorEquation_iff {M : Type} (P : M → Prop)
    (c v : M → M) (k r : M → M → M) (m f : M → M → M → M) :
    (∀ x replacement u word mapped fv tail param out : M,
      P u → word = c u → mapped = m x replacement u → fv = v replacement →
      tail = k replacement fv → param = k x tail →
      (out = f x replacement word ↔ out = r param mapped)) ↔
      ∀ x replacement u : M,P u →
        f x replacement (c u) = r (k x (k replacement (v replacement))) (m x replacement u) := by
  constructor
  · intro h x replacement u hu
    exact (h x replacement u (c u) (m x replacement u) (v replacement)
      (k replacement (v replacement)) (k x (k replacement (v replacement)))
      (f x replacement (c u)) hu rfl rfl rfl rfl rfl).mp rfl
  · intro h x replacement u word mapped fv tail param out hu hw hm hv ht hp
    subst word
    subst mapped
    subst fv
    subst tail
    subst param
    rw [h x replacement u hu]

variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def freeVariablesConstructorSentence (formula : Bool) : ArithmeticSentence :=
  let A := SyntaxPolynomial.termExpression V σ d
  let B := SyntaxPolynomial.formulaExpression V π d
  let Tm := Postfix.carrier false A B
  let Fm := Postfix.carrier true A B
  let q := if formula then B else A
  let C := rawCarrier Tm Fm q
  let K := constructorGraph formula q
  let FV := freeVariablesGraph V σ π d
  let H := mapChildrenGraph FV FV q
  let R := if formula then freeVarsFormulaRootGraph π d else freeVarsTermRootGraph σ d
  “∀ u word mapped out, !C.val u → !K.val word u → !H.val mapped u →
    (!FV.val out word ↔ !R.val out 0 mapped)”

def substitutionConstructorSentence (formula : Bool) : ArithmeticSentence :=
  let A := SyntaxPolynomial.termExpression V σ d
  let B := SyntaxPolynomial.formulaExpression V π d
  let Tm := Postfix.carrier false A B
  let Fm := Postfix.carrier true A B
  let q := if formula then B else A
  let C := rawCarrier Tm Fm q
  let K := constructorGraph formula q
  let FV := freeVariablesGraph V σ π d
  let SP := substitutionPayloadGraph V σ π d
  let H := parameterMapGraph SP SP q
  let R := if formula then formulaRootGraph V π d else termRootGraph V σ d
  “∀ x replacement u word mapped fv tail param out,
    !C.val u → !K.val word u → !H.val mapped x replacement u →
    !FV.val fv replacement → !pairDef.val tail replacement fv → !pairDef.val param x tail →
    (!SP.val out x replacement word ↔ !R.val out param mapped)”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem freeVariablesConstructorSentence_eval (formula : Bool) :
    (freeVariablesConstructorSentence V σ π d formula).Evalb (M := M) ![] ↔
      ∀ u : M,
        (rawCarrier
          (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
          (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
          (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u] →
        freeVariables V σ π d (constructor formula
          (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d) u) =
        (if formula then freeVarsFormulaRoot π d else freeVarsTermRoot σ d) 0
          (mapChildren (freeVariables V σ π d) (freeVariables V σ π d)
            (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d) u) := by
  cases formula <;> simp [freeVariablesConstructorSentence,
    mapChildrenGraph_eval _ _ (freeVariables V σ π d) (freeVariables V σ π d)]
  all_goals exact constructorEquation_iff _ _ _ _ _

@[simp] theorem substitutionConstructorSentence_eval (formula : Bool) :
    (substitutionConstructorSentence V σ π d formula).Evalb (M := M) ![] ↔
      ∀ x replacement u : M,
        (rawCarrier
          (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
          (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
          (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u] →
        substitutionPayload V σ π d x replacement (constructor formula
          (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d) u) =
        (if formula then formulaRoot V π d else termRoot V σ d)
          ⟪x,⟪replacement,freeVariables V σ π d replacement⟫⟫
          (mapChildren (substitutionPayload V σ π d x replacement) (substitutionPayload V σ π d x replacement)
            (if formula then SyntaxPolynomial.formulaExpression V π d else SyntaxPolynomial.termExpression V σ d) u) := by
  cases formula <;> simp [substitutionConstructorSentence,
    parameterMapGraph_eval_any _ _ (substitutionPayload V σ π d) (substitutionPayload V σ π d)]
  all_goals exact parameterConstructorEquation_iff _ _ _ _ _ _ _
end ArithmeticModels

/-- PA proves all literal FV constructor equations on their actual raw
source predicates, for arbitrary fixed Sigma-one coefficient predicates. -/
theorem freeVariables_constructor_PA (formula : Bool) :
    𝗣𝗔 ⊢ freeVariablesConstructorSentence V σ π d formula := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,freeVariablesConstructorSentence_eval]
  intro u hu
  cases formula
  · exact freeVariables_term_constructor V σ π d u hu
  · exact freeVariables_formula_constructor V σ π d u hu

/-- This PA equation uses the actual paired traversal and has no recursive
child-success premise. Thus it includes the equal-binder original-body branch. -/
theorem substitution_constructor_PA (formula : Bool) :
    𝗣𝗔 ⊢ substitutionConstructorSentence V σ π d formula := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,substitutionConstructorSentence_eval]
  intro x replacement u hu
  cases formula
  · exact substitutionPayload_term_constructor V σ π d x replacement u hu
  · exact substitutionPayload_formula_constructor V σ π d x replacement u hu

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
