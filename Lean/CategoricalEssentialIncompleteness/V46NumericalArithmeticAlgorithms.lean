/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPostfixSubstitution
public import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationParser

/-! # Literal arithmetic algorithms are independent of coefficient guards -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Algorithms
open SyntacticSyntax SyntacticSyntax.Coding ConcreteNamedSubstitution

variable (f : Carrier → Carrier)

theorem mapChildrenGraph_map (F G : 𝚺₁.Semisentence 2) (q : RawPolynomial) :
    mapChildrenGraph F G (q.mapCoefficients f) = mapChildrenGraph F G q := by
  induction q with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,mapChildrenGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,mapChildrenGraph,ip,iq]

theorem allChildrenGraph_map (F G : 𝚺₁.Semisentence 2) (q : RawPolynomial) :
    allChildrenGraph F G (q.mapCoefficients f) = allChildrenGraph F G q := by
  induction q with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,allChildrenGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,allChildrenGraph,ip,iq]

theorem gatherGraph_map (q : RawPolynomial) :
    gatherGraph (q.mapCoefficients f) = gatherGraph q := by
  induction q with
  | term => rfl
  | formula => rfl
  | coefficient C => rfl
  | unit => rfl
  | product p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,gatherGraph,ip,iq]
  | sum p q ip iq => simp only [SyntaxPolynomial.mapCoefficients,gatherGraph,ip,iq]

theorem constructorGraph_map (b : Bool) (q : RawPolynomial) :
    constructorGraph b (q.mapCoefficients f) = constructorGraph b q := by
  cases b <;> simp only [constructorGraph,
    NumericalDerivationInterpretation.Parser.shapeGraph_map,
    NumericalDerivationInterpretation.Parser.childrenWordGraph_map]

theorem traversal_stepGraph_map (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) :
    Traversal.stepGraph (a.mapCoefficients f) (b.mapCoefficients f) F G =
      Traversal.stepGraph a b F G := by
  simp only [Traversal.stepGraph,NumericalDerivationInterpretation.Parser.refillGraph_map]

theorem traversal_blueprint_map (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) :
    Traversal.blueprint (a.mapCoefficients f) (b.mapCoefficients f) F G =
      Traversal.blueprint a b F G := by
  simp only [Traversal.blueprint,traversal_stepGraph_map]

theorem traversal_prefixGraph_map (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) :
    Traversal.prefixGraph (a.mapCoefficients f) (b.mapCoefficients f) F G =
      Traversal.prefixGraph a b F G := by
  simp only [Traversal.prefixGraph,traversal_blueprint_map]

theorem traversal_runGraph_map (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) :
    Traversal.runGraph (a.mapCoefficients f) (b.mapCoefficients f) F G =
      Traversal.runGraph a b F G := by
  simp only [Traversal.runGraph,traversal_prefixGraph_map]

theorem traversal_outputGraph_map (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) :
    Traversal.outputGraph (a.mapCoefficients f) (b.mapCoefficients f) F G =
      Traversal.outputGraph a b F G := by
  simp only [Traversal.outputGraph,traversal_runGraph_map]

theorem formulaLeft_map (π : ℕ → Carrier) (d : ℕ) :
    (formulaLeft π d).mapCoefficients f = formulaLeft (fun k => f (π k)) d := by
  simp only [formulaLeft,SyntaxPolynomial.mapCoefficients,
    SyntaxOperationsTransport.mapCoefficients_power,
    SyntaxOperationsTransport.mapCoefficients_constructors]

theorem freeVarsTermRootGraph_map (σ : ℕ → Carrier) (d : ℕ) :
    freeVarsTermRootGraph (fun k => f (σ k)) d = freeVarsTermRootGraph σ d := by
  have h := gatherGraph_map f (SyntaxPolynomial.constructors σ d)
  rw [SyntaxOperationsTransport.mapCoefficients_constructors] at h
  simp only [freeVarsTermRootGraph,h]

theorem freeVarsFormulaRootGraph_map (π : ℕ → Carrier) (d : ℕ) :
    freeVarsFormulaRootGraph (fun k => f (π k)) d = freeVarsFormulaRootGraph π d := by
  have h := gatherGraph_map f (formulaLeft π d)
  rw [formulaLeft_map] at h
  simp only [freeVarsFormulaRootGraph,h]

theorem termRootGraph_map (V : Carrier) (σ : ℕ → Carrier) (d : ℕ) :
    termRootGraph (f V) (fun k => f (σ k)) d = termRootGraph V σ d := by
  have hq := (SyntaxOperationsTransport.mapCoefficients_termExpression f V σ d).symm
  simp only [termRootGraph,hq,mapChildrenGraph_map,constructorGraph_map,freeVarsTermRootGraph_map]

theorem formulaRootGraph_map (V : Carrier) (π : ℕ → Carrier) (d : ℕ) :
    formulaRootGraph (f V) (fun k => f (π k)) d = formulaRootGraph V π d := by
  have hq := (SyntaxOperationsTransport.mapCoefficients_formulaExpression f V π d).symm
  simp only [formulaRootGraph,hq,mapChildrenGraph_map,constructorGraph_map,allChildrenGraph_map,
    freeVarsFormulaRootGraph_map]

theorem freeVariablesGraph_map (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    freeVariablesGraph (f V) (fun k => f (σ k)) (fun k => f (π k)) d =
      freeVariablesGraph V σ π d := by
  have ht := (SyntaxOperationsTransport.mapCoefficients_termExpression f V σ d).symm
  have hf := (SyntaxOperationsTransport.mapCoefficients_formulaExpression f V π d).symm
  simp only [freeVariablesGraph,ht,hf,freeVarsTermRootGraph_map,
    freeVarsFormulaRootGraph_map,traversal_outputGraph_map]

theorem substitutionPayloadGraph_map (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    substitutionPayloadGraph (f V) (fun k => f (σ k)) (fun k => f (π k)) d =
      substitutionPayloadGraph V σ π d := by
  have ht := (SyntaxOperationsTransport.mapCoefficients_termExpression f V σ d).symm
  have hf := (SyntaxOperationsTransport.mapCoefficients_formulaExpression f V π d).symm
  simp only [substitutionPayloadGraph,ht,hf,freeVariablesGraph_map,termRootGraph_map,formulaRootGraph_map,
    traversal_outputGraph_map]

theorem substitutionResultGraph_map (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    substitutionResultGraph (f V) (fun k => f (σ k)) (fun k => f (π k)) d =
      substitutionResultGraph V σ π d := by
  simp only [substitutionResultGraph,substitutionPayloadGraph_map]

theorem substitutionFreeForGraph_map (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    substitutionFreeForGraph (f V) (fun k => f (σ k)) (fun k => f (π k)) d =
      substitutionFreeForGraph V σ π d := by
  simp only [substitutionFreeForGraph,substitutionPayloadGraph_map]

variable (V W : Carrier) (σ τ π ρ : ℕ → Carrier) (d : ℕ)

/-- The raw term-constructor graph keeps its numerical labels and children. -/
theorem termConstructorGraph_signature (b : Bool) :
    constructorGraph b (SyntaxPolynomial.termExpression V σ d) =
      constructorGraph b (SyntaxPolynomial.termExpression W τ d) := by
  have h : (SyntaxPolynomial.termExpression V σ d).mapCoefficients (fun _ => zeroCarrier) =
      (SyntaxPolynomial.termExpression W τ d).mapCoefficients (fun _ => zeroCarrier) := by
    simp only [SyntaxOperationsTransport.mapCoefficients_termExpression]
  exact (constructorGraph_map (fun _ => zeroCarrier) b _).symm.trans
    ((congrArg (constructorGraph b) h).trans (constructorGraph_map (fun _ => zeroCarrier) b _))

theorem formulaConstructorGraph_signature (b : Bool) :
    constructorGraph b (SyntaxPolynomial.formulaExpression V π d) =
      constructorGraph b (SyntaxPolynomial.formulaExpression W ρ d) := by
  have h : (SyntaxPolynomial.formulaExpression V π d).mapCoefficients (fun _ => zeroCarrier) =
      (SyntaxPolynomial.formulaExpression W ρ d).mapCoefficients (fun _ => zeroCarrier) := by
    simp only [SyntaxOperationsTransport.mapCoefficients_formulaExpression]
  exact (constructorGraph_map (fun _ => zeroCarrier) b _).symm.trans
    ((congrArg (constructorGraph b) h).trans (constructorGraph_map (fun _ => zeroCarrier) b _))

/-- Carrier predicates guard labels, but are absent from the computation graph. -/
theorem freeVariablesGraph_signature :
    freeVariablesGraph V σ π d = freeVariablesGraph W τ ρ d :=
  (freeVariablesGraph_map (fun _ => zeroCarrier) V σ π d).symm.trans
    (freeVariablesGraph_map (fun _ => zeroCarrier) W τ ρ d)

theorem substitutionPayloadGraph_signature :
    substitutionPayloadGraph V σ π d = substitutionPayloadGraph W τ ρ d :=
  (substitutionPayloadGraph_map (fun _ => zeroCarrier) V σ π d).symm.trans
    (substitutionPayloadGraph_map (fun _ => zeroCarrier) W τ ρ d)

theorem substitutionResultGraph_signature :
    substitutionResultGraph V σ π d = substitutionResultGraph W τ ρ d :=
  (substitutionResultGraph_map (fun _ => zeroCarrier) V σ π d).symm.trans
    (substitutionResultGraph_map (fun _ => zeroCarrier) W τ ρ d)

theorem substitutionFreeForGraph_signature :
    substitutionFreeForGraph V σ π d = substitutionFreeForGraph W τ ρ d :=
  (substitutionFreeForGraph_map (fun _ => zeroCarrier) V σ π d).symm.trans
    (substitutionFreeForGraph_map (fun _ => zeroCarrier) W τ ρ d)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem termConstructor_signature (b : Bool) (u : M) :
    constructor b (SyntaxPolynomial.termExpression V σ d) u =
      constructor b (SyntaxPolynomial.termExpression W τ d) u := by
  have h := (constructorGraph_eval b (SyntaxPolynomial.termExpression V σ d)
    (constructor b (SyntaxPolynomial.termExpression V σ d) u) u).mpr rfl
  rw [termConstructorGraph_signature V W σ τ d b] at h
  exact (constructorGraph_eval b (SyntaxPolynomial.termExpression W τ d) _ u).mp h

theorem formulaConstructor_signature (b : Bool) (u : M) :
    constructor b (SyntaxPolynomial.formulaExpression V π d) u =
      constructor b (SyntaxPolynomial.formulaExpression W ρ d) u := by
  have h := (constructorGraph_eval b (SyntaxPolynomial.formulaExpression V π d)
    (constructor b (SyntaxPolynomial.formulaExpression V π d) u) u).mpr rfl
  rw [formulaConstructorGraph_signature V W π ρ d b] at h
  exact (constructorGraph_eval b (SyntaxPolynomial.formulaExpression W ρ d) _ u).mp h

theorem freeVariables_signature (word : M) :
    freeVariables V σ π d word = freeVariables W τ ρ d word := by
  have h := (freeVariablesGraph_eval V σ π d (freeVariables V σ π d word) word).mpr rfl
  rw [freeVariablesGraph_signature V W σ τ π ρ d] at h
  exact (freeVariablesGraph_eval W τ ρ d _ word).mp h

theorem substitutionPayload_signature (x replacement word : M) :
    substitutionPayload V σ π d x replacement word = substitutionPayload W τ ρ d x replacement word := by
  have h := (substitutionPayloadGraph_eval V σ π d
    (substitutionPayload V σ π d x replacement word) x replacement word).mpr rfl
  rw [substitutionPayloadGraph_signature V W σ τ π ρ d] at h
  exact (substitutionPayloadGraph_eval W τ ρ d _ x replacement word).mp h

theorem substitutionResult_signature (x replacement word : M) :
    substitutionResult V σ π d x replacement word = substitutionResult W τ ρ d x replacement word := by
  have h := (substitutionResultGraph_eval V σ π d
    (substitutionResult V σ π d x replacement word) x replacement word).mpr rfl
  rw [substitutionResultGraph_signature V W σ τ π ρ d] at h
  exact (substitutionResultGraph_eval W τ ρ d _ x replacement word).mp h

theorem substitutionFreeFor_signature (x replacement word : M) :
    substitutionFreeFor V σ π d x replacement word = substitutionFreeFor W τ ρ d x replacement word := by
  have h := (substitutionFreeForGraph_eval V σ π d
    (substitutionFreeFor V σ π d x replacement word) x replacement word).mpr rfl
  rw [substitutionFreeForGraph_signature V W σ τ π ρ d] at h
  exact (substitutionFreeForGraph_eval W τ ρ d _ x replacement word).mp h

end Models
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Algorithms
