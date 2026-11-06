import CategoricalEssentialIncompleteness.V46NamedArithmeticModelCoding
import CategoricalEssentialIncompleteness.V46NamedArithmeticClosedSubstitution
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonProjectionValues

/-! A fixed finite source formula may receive a nonstandard closed term.
The output below is an arithmetic constructor word in the selected model;
no external-finiteness assertion about its replacement word is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticModelSubstitution
open ConcreteNamedSubstitution NamedPostfixEncoding NamedArithmeticModelCoding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance namedArithmeticModelSubstitutionDecidableEq : DecidableEq M := Classical.decEq M
variable {σ π : ℕ → Carrier} {d : ℕ}

def termOutput (x replacement : M) : NamedFiniteSyntax.Term (Symbols σ) d → M
  | .var y => if (y : M) = x then replacement else termWord (.var y : NamedFiniteSyntax.Term (Symbols σ) d)
  | .app k s children => constructor false (termPolynomial σ d)
      ⟪NamedArithmeticModelCoding.arityInput d k
        ⟪(s.val : M),NamedArithmeticModelCoding.childTuple k.val
          (fun i => termOutput x replacement (children i))⟫,1⟫

def formulaOutput (x replacement : M) : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d → M
  | .equal s t => constructor true (formulaPolynomial π d)
      (NamedArithmeticModelCoding.equalInput (termOutput x replacement s) (termOutput x replacement t))
  | .relation k p children => constructor true (formulaPolynomial π d)
      (NamedArithmeticModelCoding.relationInput d k (p.val : M) (fun i => termOutput x replacement (children i)))
  | .neg body => constructor true (formulaPolynomial π d)
      (NamedArithmeticModelCoding.negInput (formulaOutput x replacement body))
  | .imp left right => constructor true (formulaPolynomial π d)
      (NamedArithmeticModelCoding.impInput (formulaOutput x replacement left) (formulaOutput x replacement right))
  | .all y body => if (y : M) = x then formulaWord (.all y body)
      else constructor true (formulaPolynomial π d)
        (NamedArithmeticModelCoding.allInput (y : M) (formulaOutput x replacement body))

private theorem payload_result_eq (x replacement word : M) :
    result (substitutionPayload variableCarrier σ π d x replacement word) =
      substitutionResult variableCarrier σ π d x replacement word := rfl

private theorem termRoot_result (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) (param value : M) :
    result (termRoot V σ d param value) =
      if π₂ value = 0 then
        if π₁ value = π₁ param then π₁ (π₂ param)
        else constructor false (SyntaxPolynomial.termExpression V σ d)
          (mapChildren original original (SyntaxPolynomial.termExpression V σ d) value)
      else constructor false (SyntaxPolynomial.termExpression V σ d)
        (mapChildren result successfulValue (SyntaxPolynomial.termExpression V σ d) value) := by
  simp only [termRoot,result_payload]

private theorem formulaRoot_result (V : Carrier) (π : ℕ → Carrier) (d : ℕ) (param value : M) :
    result (formulaRoot V π d param value) =
      if π₂ value = 0 then
        if allChildren (fun _ => 1) success (SyntaxPolynomial.formulaExpression V π d) value = 1 then
          ok (constructor true (SyntaxPolynomial.formulaExpression V π d)
            (mapChildren result successfulValue (SyntaxPolynomial.formulaExpression V π d) value)) else 0
      else if π₁ (π₁ value) = π₁ param then
        ok (constructor true (SyntaxPolynomial.formulaExpression V π d)
          (mapChildren original original (SyntaxPolynomial.formulaExpression V π d) value))
      else if capture param value = 1 ∧ success (π₂ (π₁ value)) = 1 then
        ok (constructor true (SyntaxPolynomial.formulaExpression V π d)
          (mapChildren result successfulValue (SyntaxPolynomial.formulaExpression V π d) value)) else 0 := by
  simp only [formulaRoot,result_payload]

/-- Constructor comparison for term inputs. Replacement typing is not
needed for this literal computational equation. -/
theorem termResult_eq (π : ℕ → Carrier) (x replacement : M)
    (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    substitutionResult variableCarrier σ π d x replacement (termWord s) = termOutput x replacement s := by
  induction s with
  | var y =>
    rw [termWord_root]
    unfold substitutionResult
    erw [substitutionPayload_term_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.termInput_member π (.var y : NamedFiniteSyntax.Term (Symbols σ) d)),termRoot_result]
    simp only [NamedArithmeticModelCoding.termInput,NamedPostfixEncoding.termPolynomial,SyntaxPolynomial.termExpression,
      mapChildren,pi₁_pair,pi₂_pair,ite_true,termOutput,termWord]
  | app k s children ih =>
    rw [termWord_root]
    unfold substitutionResult
    erw [substitutionPayload_term_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.termInput_member π (.app k s children)),termRoot_result]
    simp only [NamedArithmeticModelCoding.termInput,NamedPostfixEncoding.termPolynomial,SyntaxPolynomial.termExpression,
      mapChildren,pi₁_pair,pi₂_pair,Arithmetic.one_ne_zero,ite_false,
      NamedArithmeticModelCoding.mapChildren_arityInput,payload_result_eq,termOutput]
    rw [funext ih]

 theorem termOutput_member (π : ℕ → Carrier) (x replacement : M)
    (hrep : (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (s : NamedFiniteSyntax.Term (Symbols σ) d) :
    (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![termOutput x replacement s] := by
  rw [← termResult_eq π]
  exact substitutionResult_term _ _ _ _ _ _ _ hrep (termWord_member π s)

private theorem original_formulaWord (x replacement : M)
    (hrep : (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    original (substitutionPayload variableCarrier σ π d x replacement (formulaWord φ)) = formulaWord φ :=
  ConcreteNamedComparison.originalComputation_identity 𝗣𝗔 variableCarrier variableCarrier σ π d M true
    x replacement (formulaWord φ) (by simp [variableCarrier]) hrep (formulaWord_member φ)

/-- The equal-binder output is the original whole quantified word. All
other branches use the same literal binder and recursively rebuilt body. -/
theorem formulaResult_eq (x replacement : M)
    (hrep : (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (hclosed : freeVariables variableCarrier σ π d replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    substitutionResult variableCarrier σ π d x replacement (formulaWord φ) = ok (formulaOutput x replacement φ) := by
  induction φ with
  | equal s t =>
    rw [formulaWord_root]
    unfold substitutionResult
    erw [substitutionPayload_formula_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.formulaInput_member (.equal s t)),formulaRoot_result]
    simp only [NamedArithmeticModelCoding.formulaInput,NamedArithmeticModelCoding.equalInput,
      NamedPostfixEncoding.formulaPolynomial,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,mapChildren,
      allChildren,and_self,pi₁_pair,pi₂_pair,ite_true,
      payload_result_eq,termResult_eq π,formulaOutput]
  | relation k p children =>
    rw [formulaWord_root]
    unfold substitutionResult
    erw [substitutionPayload_formula_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.formulaInput_member (.relation k p children)),formulaRoot_result]
    simp only [NamedArithmeticModelCoding.formulaInput,NamedArithmeticModelCoding.relationInput,
      NamedPostfixEncoding.formulaPolynomial,SyntaxPolynomial.formulaExpression,mapChildren,
      allChildren,pi₁_pair,pi₂_pair,ite_true,Arithmetic.one_ne_zero,ite_false,
      NamedArithmeticModelCoding.mapChildren_arityInput,
      payload_result_eq,termResult_eq π,formulaOutput,constructors_allChildren]
  | neg body ih =>
    rw [formulaWord_root]
    unfold substitutionResult
    erw [substitutionPayload_formula_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.formulaInput_member (.neg body)),formulaRoot_result]
    simp only [NamedArithmeticModelCoding.formulaInput,NamedArithmeticModelCoding.negInput,
      NamedPostfixEncoding.formulaPolynomial,SyntaxPolynomial.formulaExpression,mapChildren,
      allChildren,pi₁_pair,pi₂_pair,ite_true,Arithmetic.one_ne_zero,ite_false,
      success,successfulValue,payload_result_eq,ih,ok,formulaOutput]
  | imp left right il ir =>
    rw [formulaWord_root]
    unfold substitutionResult
    erw [substitutionPayload_formula_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.formulaInput_member (.imp left right)),formulaRoot_result]
    simp only [NamedArithmeticModelCoding.formulaInput,NamedArithmeticModelCoding.impInput,
      NamedPostfixEncoding.formulaPolynomial,SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,mapChildren,
      allChildren,and_self,pi₁_pair,pi₂_pair,ite_true,Arithmetic.one_ne_zero,ite_false,
      success,successfulValue,payload_result_eq,il,ir,ok,formulaOutput]
  | all y body ih =>
    rw [formulaWord_root]
    unfold substitutionResult
    erw [substitutionPayload_formula_constructor variableCarrier σ π d x replacement _
      (NamedArithmeticModelCoding.formulaInput_member (.all y body)),formulaRoot_result]
    have hc : capture ⟪x,⟪replacement,freeVariables variableCarrier σ π d replacement⟫⟫
        ⟪⟪(y : M),substitutionPayload variableCarrier σ π d x replacement (formulaWord body)⟫,1⟫ = 1 := by
      simp [capture,hclosed]
    simp only [NamedArithmeticModelCoding.formulaInput,NamedArithmeticModelCoding.allInput,
      SyntaxPolynomial.formulaExpression,mapChildren,pi₁_pair,pi₂_pair,Arithmetic.one_ne_zero,ite_false]
    by_cases hy : (y : M) = x
    · simp only [hy,ite_true,original_formulaWord x replacement hrep body,formulaOutput,formulaWord]
      rfl
    · simp only [hy,ite_false,hc,success,successfulValue,payload_result_eq,ih,ok,
        pi₁_pair,pi₂_pair,ite_true,and_self,formulaOutput,
        NamedPostfixEncoding.formulaPolynomial,NamedArithmeticModelCoding.allInput]
      rfl

 theorem formulaOutput_member (x replacement : M)
    (hrep : (Postfix.carrier false (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![replacement])
    (hclosed : freeVariables variableCarrier σ π d replacement = 0)
    (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d) :
    (Postfix.carrier true (termPolynomial σ d) (formulaPolynomial π d)).val.Evalb ![formulaOutput x replacement φ] := by
  rcases substitutionResult_formula variableCarrier σ π d x replacement (formulaWord φ) hrep
    (formulaWord_member φ) with hz | ⟨out,ho,he⟩
  · have hh := congrArg (pi₂ : M → M) ((formulaResult_eq x replacement hrep hclosed φ).symm.trans hz)
    simp [ok,pi₂_zero] at hh
  · have hh := congrArg (pi₁ : M → M) (he.symm.trans (formulaResult_eq x replacement hrep hclosed φ))
    have heq : out = formulaOutput x replacement φ := by simpa only [ok,pi₁_pair] using hh
    exact heq ▸ ho

end CategoricalEssentialIncompleteness.V46.NamedArithmeticModelSubstitution
