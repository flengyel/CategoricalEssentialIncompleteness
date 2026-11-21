/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonConstantMap
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonProjectionLaws
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # The original payload field is identified by stable initiality -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (U V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

def projectionParameters : PredicateCategory T := U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)

def projectionSourceAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V σ d).withParameters (projectionParameters T U V σ π d))
    ((SyntaxPolynomial.formulaExpression V π d).withParameters (projectionParameters T U V σ π d))) :=
  SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) (categoricalSyntax T V σ π d).algebra
    (projectionParameters T U V σ π d)

def originalProjectionPair : (projectionSourceAlgebra T U V σ π d).a ⟶
    (projectionSourceAlgebra T U V σ π d).a :=
  (payloadProjectionFamily T U V σ π d .original false,
    payloadProjectionFamily T U V σ π d .original true)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Full model-point equality is proved by the product projections. Neither the parameter
nor the whole product point is identified with a numerical pair. -/
theorem original_term_commutes_model
    (q : Obj T M (((SyntaxPolynomial.termExpression V σ d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionSourceAlgebra T U V σ π d).a).left) :
    (F T M).map (projectionSourceAlgebra T U V σ π d).str.1.left
      ((F T M).map (((SyntaxPolynomial.termExpression V σ d).withParameters
        (projectionParameters T U V σ π d)).eval.map (originalProjectionPair T U V σ π d)).left q) =
      (F T M).map (payloadProjectionFamily T U V σ π d .original false).left
        ((F T M).map (projectionSourceAlgebra T U V σ π d).str.1.left q) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let P := projectionParameters T U V σ π d
  let a := SyntaxPolynomial.termExpression V σ d
  let b := SyntaxPolynomial.formulaExpression V π d
  let p := (F T M).map ((a.withParameters P).eval.obj (projectionSourceAlgebra T U V σ π d).a).hom q
  obtain ⟨u,hu⟩ := constantRepresentation_cover T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) a p q rfl
  have hguard := (constantRepresentation_support T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) a p.val u q.val hu).2.1
  let x := ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) p).val
  let t := ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) p).val
  let φ := originalComputation V σ π d x t
  let f := payloadProjectionFamily T U V σ π d .original false
  let g := payloadProjectionFamily T U V σ π d .original true
  have hf : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map f.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .original false p z hz
  have hg : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d true : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map g.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .original true p z hz
  let v := ConcreteNamedSubstitution.mapChildren φ φ a u
  let z := (F T M).map ((a.withParameters P).eval.map (originalProjectionPair T U V σ π d)).left q
  have hz := constantRepresentation_map T M f g p φ φ hf hg a u q hu
  let left := (F T M).map (projectionSourceAlgebra T U V σ π d).str.1.left z
  let source := (F T M).map (projectionSourceAlgebra T U V σ π d).str.1.left q
  have hl := (constantLeaf_model T M P (syntaxCarrier V σ π d false) p
    (Coding.constructor false a v) left).mp (parameterTerm_coordinate T M P a b p v z hz)
  have hs := (constantLeaf_model T M P (syntaxCarrier V σ π d false) p
    (Coding.constructor false a u) source).mp (parameterTerm_coordinate T M P a b p u q hu)
  have hr := payloadProjectionFamily_value T U V σ π d M .original false p source hs.1
  have hrvalue : ((F T M).map prod.snd ((F T M).map f.left source)).val = Coding.constructor false a v :=
    hr.trans ((congrArg φ hs.2).trans (originalComputation_term_constructor V σ π d x t u hguard))
  apply modelProduct_ext T M
  · exact hl.1.trans ((over_value T M f source).trans hs.1).symm
  · exact Subtype.ext (hl.2.trans hrvalue.symm)

theorem original_formula_commutes_model
    (q : Obj T M (((SyntaxPolynomial.formulaExpression V π d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionSourceAlgebra T U V σ π d).a).left) :
    (F T M).map (projectionSourceAlgebra T U V σ π d).str.2.left
      ((F T M).map (((SyntaxPolynomial.formulaExpression V π d).withParameters
        (projectionParameters T U V σ π d)).eval.map (originalProjectionPair T U V σ π d)).left q) =
      (F T M).map (payloadProjectionFamily T U V σ π d .original true).left
        ((F T M).map (projectionSourceAlgebra T U V σ π d).str.2.left q) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let P := projectionParameters T U V σ π d
  let a := SyntaxPolynomial.termExpression V σ d
  let b := SyntaxPolynomial.formulaExpression V π d
  let p := (F T M).map ((b.withParameters P).eval.obj (projectionSourceAlgebra T U V σ π d).a).hom q
  obtain ⟨u,hu⟩ := constantRepresentation_cover T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) b p q rfl
  have hguard := (constantRepresentation_support T M P (syntaxCarrier V σ π d false)
    (syntaxCarrier V σ π d true) b p.val u q.val hu).2.1
  let x := ((F T M).map (prod.fst : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ U) p).val
  let t := ((F T M).map (prod.snd : U ⨯ (syntaxCarrier V σ π d false : PredicateCategory T) ⟶ _) p).val
  let φ := originalComputation V σ π d x t
  let f := payloadProjectionFamily T U V σ π d .original false
  let g := payloadProjectionFamily T U V σ π d .original true
  have hf : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map f.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .original false p z hz
  have hg : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d true : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map g.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .original true p z hz
  let v := ConcreteNamedSubstitution.mapChildren φ φ b u
  let z := (F T M).map ((b.withParameters P).eval.map (originalProjectionPair T U V σ π d)).left q
  have hz := constantRepresentation_map T M f g p φ φ hf hg b u q hu
  let left := (F T M).map (projectionSourceAlgebra T U V σ π d).str.2.left z
  let source := (F T M).map (projectionSourceAlgebra T U V σ π d).str.2.left q
  have hl := (constantLeaf_model T M P (syntaxCarrier V σ π d true) p
    (Coding.constructor true b v) left).mp (parameterFormula_coordinate T M P a b p v z hz)
  have hs := (constantLeaf_model T M P (syntaxCarrier V σ π d true) p
    (Coding.constructor true b u) source).mp (parameterFormula_coordinate T M P a b p u q hu)
  have hr := payloadProjectionFamily_value T U V σ π d M .original true p source hs.1
  have hrvalue : ((F T M).map prod.snd ((F T M).map g.left source)).val = Coding.constructor true b v :=
    hr.trans ((congrArg φ hs.2).trans (originalComputation_formula_constructor V σ π d x t u hguard))
  apply modelProduct_ext T M
  · exact hl.1.trans ((over_value T M g source).trans hs.1).symm
  · exact Subtype.ext (hl.2.trans hrvalue.symm)

end Models

/-- This is an algebra endomorphism, obtained before invoking initiality or identifying
the field with the input word. -/
def originalProjectionHom : (projectionSourceAlgebra T U V σ π d) ⟶
    (projectionSourceAlgebra T U V σ π d) where
  f := originalProjectionPair T U V σ π d
  h := by
    apply Prod.ext
    · apply Over.OverMorphism.ext
      change (((SyntaxPolynomial.termExpression V σ d).withParameters (projectionParameters T U V σ π d)).eval.map
        (originalProjectionPair T U V σ π d)).left ≫ (projectionSourceAlgebra T U V σ π d).str.1.left =
          (projectionSourceAlgebra T U V σ π d).str.1.left ≫ (originalProjectionPair T U V σ π d).1.left
      apply PredicateInterpretation.jointly_faithful T
      intro M _ _
      rw [Functor.map_comp,Functor.map_comp]
      apply ConcreteCategory.hom_ext
      intro q
      exact original_term_commutes_model T U V σ π d M q
    · apply Over.OverMorphism.ext
      change (((SyntaxPolynomial.formulaExpression V π d).withParameters (projectionParameters T U V σ π d)).eval.map
        (originalProjectionPair T U V σ π d)).left ≫ (projectionSourceAlgebra T U V σ π d).str.2.left =
          (projectionSourceAlgebra T U V σ π d).str.2.left ≫ (originalProjectionPair T U V σ π d).2.left
      apply PredicateInterpretation.jointly_faithful T
      intro M _ _
      rw [Functor.map_comp,Functor.map_comp]
      apply ConcreteCategory.hom_ext
      intro q
      exact original_formula_commutes_model T U V σ π d M q

/-- Stable initiality supplies the original-field identity as a theorem. -/
theorem originalProjectionPair_eq_id : originalProjectionPair T U V σ π d = 𝟙 _ := by
  have h := (categoricalSyntax T V σ π d).stable (projectionParameters T U V σ π d)
  exact congrArg Endofunctor.Algebra.Hom.f
    (h.hom_ext (originalProjectionHom T U V σ π d) (𝟙 (projectionSourceAlgebra T U V σ π d)))

theorem originalProjectionFamily_eq_id (formula : Bool) :
    payloadProjectionFamily T U V σ π d .original formula = 𝟙 _ := by
  cases formula
  · exact congrArg Prod.fst (originalProjectionPair_eq_id T U V σ π d)
  · exact congrArg Prod.snd (originalProjectionPair_eq_id T U V σ π d)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
