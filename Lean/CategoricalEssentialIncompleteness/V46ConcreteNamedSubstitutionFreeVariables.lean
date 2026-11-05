import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariablesRoots

/-! The actual total numerical free-variable traversal, with PA equations,
PA carrier preservation, and a separate standard primitive-recursion proof. -/
noncomputable section
local instance primitiveNamedFreeVariablesDecidableEqNat : DecidableEq ℕ := Classical.decEq ℕ
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
open SyntacticSyntax SyntacticSyntax.Coding

variable (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)

def freeVariablesGraph : 𝚺₁.Semisentence 2 :=
  let R := Traversal.outputGraph (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) (freeVarsTermRootGraph σ d) (freeVarsFormulaRootGraph π d)
  .mkSigma “out word. !R.val out 0 word”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def freeVariables (word : M) : M :=
  Traversal.output (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
    (freeVarsTermRootGraph σ d) (freeVarsFormulaRootGraph π d)
    (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d) 0 word

@[simp] theorem freeVariablesGraph_eval (out word : M) :
    (freeVariablesGraph V σ π d).val.Evalb ![out,word] ↔ out = freeVariables V σ π d word := by
  simp [freeVariablesGraph,freeVariables,Traversal.outputGraph_eval_any _ _ _ _
    (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d)]

instance freeVariables_defined :
    𝚺₁-Function₁ (freeVariables V σ π d : M → M) via freeVariablesGraph V σ π d := .mk fun v => by
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa [hv] using freeVariablesGraph_eval V σ π d (v 0) (v 1)
instance freeVariables_definable : 𝚺₁-Function₁ (freeVariables V σ π d : M → M) :=
  (freeVariables_defined V σ π d).to_definable
instance freeVariables_definable' (Γ m) : Γ-[m + 1]-Function₁ (freeVariables V σ π d : M → M) :=
  (freeVariables_definable V σ π d).of_sigmaOne

/-- This carrier theorem holds in every PA model for arbitrary fixed
Sigma-one coefficient predicates, without assuming that model satisfies T. -/
theorem freeVariables_carrier (formula : Bool) (word : M)
    (hw : (Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word]) :
    (SyntacticLists.listCarrier V).val.Evalb ![freeVariables V σ π d word] :=
  by
    simpa [freeVariables] using
      Traversal.output_typed (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) (freeVarsTermRootGraph σ d)
        (freeVarsFormulaRootGraph π d) (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d) 0
        (SyntacticLists.listCarrier V) (SyntacticLists.listCarrier V)
        (freeVarsTermRoot_carrier V σ d 0) (freeVarsFormulaRoot_carrier V π d 0) formula word hw

/-- Complete PA term-constructor equation on the actual raw chart. -/
theorem freeVariables_term_constructor (u : M)
    (hu : (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![u]) :
    freeVariables V σ π d (constructor false (SyntaxPolynomial.termExpression V σ d) u) =
      freeVarsTermRoot σ d 0 (mapChildren (freeVariables V σ π d) (freeVariables V σ π d)
        (SyntaxPolynomial.termExpression V σ d) u) :=
  Traversal.output_term_constructor _ _ _ _ (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d) 0 u hu

/-- Complete PA formula-constructor equation, including literal binders. -/
theorem freeVariables_formula_constructor (u : M)
    (hu : (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u]) :
    freeVariables V σ π d (constructor true (SyntaxPolynomial.formulaExpression V π d) u) =
      freeVarsFormulaRoot π d 0 (mapChildren (freeVariables V σ π d) (freeVariables V σ π d)
        (SyntaxPolynomial.formulaExpression V π d) u) :=
  Traversal.output_formula_constructor _ _ _ _ (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d) 0 u hu

@[simp] theorem freeVariables_variable (x : M) (hx : V.val.Evalb ![x]) :
    freeVariables V σ π d (constructor false (SyntaxPolynomial.termExpression V σ d) ⟪x,0⟫) =
      adjoin x 0 := by
  have hu : (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![⟪x,0⟫] := by
    simp [SyntaxPolynomial.termExpression,rawCarrier,hx]
  rw [freeVariables_term_constructor V σ π d _ hu]
  simp [SyntaxPolynomial.termExpression,mapChildren,freeVarsTermRoot]

@[simp] theorem freeVariables_quantifier (y body : M) (hy : V.val.Evalb ![y])
    (hb : (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![body]) :
    freeVariables V σ π d (constructor true (SyntaxPolynomial.formulaExpression V π d) ⟪⟪y,body⟫,1⟫) =
      delete y (freeVariables V σ π d body) := by
  have hu : (rawCarrier
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![⟪⟪y,body⟫,1⟫] := by
    have hprod := (rawCarrier_product_eval
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (.coefficient V) .formula ⟪y,body⟫).mpr ⟨y,body,rfl,hy,hb⟩
    exact (rawCarrier_sum_eval
      (Postfix.carrier false (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (Postfix.carrier true (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
      (formulaLeft π d) (.product (.coefficient V) .formula) ⟪⟪y,body⟫,1⟫).mpr
        (Or.inr ⟨⟪y,body⟫,rfl,hprod⟩)
  rw [freeVariables_formula_constructor V σ π d _ hu]
  simp [SyntaxPolynomial.formulaExpression,mapChildren,freeVarsFormulaRoot]

end Models

private theorem fixedZeroParameter_primrec {f : ℕ × ℕ → ℕ} (hf : Primrec f) :
    Primrec (fun word : ℕ => f (0,word)) :=
  hf.comp (Primrec.pair (Primrec.const 0) Primrec.id)

/-- This is the actual standard primitive-recursion certificate for the
numerical function whose all-model PA equations were proved above. -/
theorem freeVariables_primrec : Primrec (freeVariables V σ π d : ℕ → ℕ) := by
  exact Primrec.of_eq (fixedZeroParameter_primrec
    (Traversal.output_primrec _ _ _ _ (freeVarsTermRoot σ d) (freeVarsFormulaRoot π d)
      (freeVarsTermRoot_primrec σ d) (freeVarsFormulaRoot_primrec π d))) (fun _ => rfl)

theorem freeVariables_natPrimrec : Nat.Primrec (freeVariables V σ π d : ℕ → ℕ) :=
  Primrec.nat_iff.mp (freeVariables_primrec V σ π d)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
