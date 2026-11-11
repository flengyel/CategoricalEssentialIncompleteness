/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFoldHom
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxHomGraphs
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxEvaluationLaws

/-! # Uniqueness of actual parameter-slice algebra morphisms -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P : PredicateCategory T} (a b : SyntaxPolynomial (PredicateCategory T))
variable (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
  (a.withParameters P) (b.withParameters P)))
variable (H : SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P ⟶ B)

/-- These recursion equations are extracted from the actual categorical
hom equation, rather than required as separate candidate data. -/
theorem hom_root_equations (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    (decode T P a b B).RootEquations (M := M) (rawArrow T H.f.1) (rawArrow T H.f.2) := by
  constructor
  · intro p u x hp hu
    exact candidateTermEquation T a b B H.f.1 H.f.2 M
      (congrArg Prod.fst H.h) p u x hp hu
  · intro p u x hp hu
    exact candidateFormulaEquation T a b B H.f.1 H.f.2 M
      (congrArg Prod.snd H.h) p u x hp hu

/-- Internal finite-word uniqueness proves equality of every actual
algebra morphism with the constructed fold, in every parameter slice. -/
theorem foldHom_unique : H = foldHom T a b B := by
  apply Endofunctor.Algebra.Hom.ext
  apply Prod.ext
  · apply Over.OverMorphism.ext
    apply PredicateInterpretation.jointly_faithful T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    apply ConcreteCategory.hom_ext
    intro q
    let p := (F T M).map (prod.fst : P ⨯ termCarrier a b ⟶ P) q
    let w := (F T M).map (prod.snd : P ⨯ termCarrier a b ⟶ termCarrier a b) q
    let x := (F T M).map H.f.1.left q
    let y := (F T M).map (termFold T a b B).left q
    have hq := (constantLeaf_model T M P (termCarrier a b) p w q).mpr ⟨rfl, rfl⟩
    have hx := (rawArrow_model T M H.f.1 p w q x hq).mpr rfl
    have hy := (termFoldMap_eval T a b B M q y).mp rfl
    have he := (decode T P a b B).evaluation_unique (rawArrow T H.f.1)
      (rawArrow T H.f.2) (hom_root_equations T a b B H M) false
        p.val w.val x.val y.val hx hy
    exact Subtype.ext he
  · apply Over.OverMorphism.ext
    apply PredicateInterpretation.jointly_faithful T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    apply ConcreteCategory.hom_ext
    intro q
    let p := (F T M).map (prod.fst : P ⨯ formulaCarrier a b ⟶ P) q
    let w := (F T M).map (prod.snd : P ⨯ formulaCarrier a b ⟶ formulaCarrier a b) q
    let x := (F T M).map H.f.2.left q
    let y := (F T M).map (formulaFold T a b B).left q
    have hq := (constantLeaf_model T M P (formulaCarrier a b) p w q).mpr ⟨rfl, rfl⟩
    have hx := (rawArrow_model T M H.f.2 p w q x hq).mpr rfl
    have hy := (formulaFoldMap_eval T a b B M q y).mp rfl
    have he := (decode T P a b B).evaluation_unique (rawArrow T H.f.1)
      (rawArrow T H.f.2) (hom_root_equations T a b B H M) true
        p.val w.val x.val y.val hx hy
    exact Subtype.ext he

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
