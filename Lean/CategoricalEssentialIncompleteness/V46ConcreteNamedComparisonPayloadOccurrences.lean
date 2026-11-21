/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOriginal
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOccurrences
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # The payload's FV field is identified by stable initiality -/

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

def projectionOccurrenceAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V σ d).withParameters (projectionParameters T U V σ π d))
    ((SyntaxPolynomial.formulaExpression V π d).withParameters (projectionParameters T U V σ π d))) :=
  SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d) (categoricalSyntax T V σ π d).occurrenceAlgebra
    (projectionParameters T U V σ π d)

def payloadOccurrenceProjectionPair : (projectionSourceAlgebra T U V σ π d).a ⟶
    (projectionOccurrenceAlgebra T U V σ π d).a :=
  (payloadProjectionFamily T U V σ π d .occurrences false,
    payloadProjectionFamily T U V σ π d .occurrences true)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem parameterOccurrenceTerm_value (p : Obj T M (projectionParameters T U V σ π d)) (u : M)
    (q : Obj T M (((SyntaxPolynomial.termExpression V σ d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionOccurrenceAlgebra T U V σ π d).a).left)
    (hq : (constantRepresentation T (projectionParameters T U V σ π d)
      (listObject T V) (listObject T V) (SyntaxPolynomial.termExpression V σ d)).val.Evalb ![p.val,u,q.val]) :
    ((F T M).map prod.snd
      ((F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.1.left q)).val =
        ConcreteNamedSubstitution.freeVarsTermRoot σ d 0 u := by
  let P := projectionParameters T U V σ π d
  let a := SyntaxPolynomial.termExpression V σ d
  let f := (categoricalSyntax T V σ π d).occurrenceAlgebra.str.1
  have hp := parameterOperation_value T M P (listObject T V) (listObject T V) (listObject T V) a f q
  have hr := parameterValueMap_representation T M P (listObject T V) (listObject T V) a p u q hq
  exact (congrArg Subtype.val hp).trans (occurrenceTerm_operation_value T V M σ d u
    ((F T M).map (parameterValueMap T P (listObject T V) (listObject T V) a) q) hr)

theorem parameterOccurrenceFormula_value (p : Obj T M (projectionParameters T U V σ π d)) (u : M)
    (q : Obj T M (((SyntaxPolynomial.formulaExpression V π d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionOccurrenceAlgebra T U V σ π d).a).left)
    (hq : (constantRepresentation T (projectionParameters T U V σ π d)
      (listObject T V) (listObject T V) (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![p.val,u,q.val]) :
    ((F T M).map prod.snd
      ((F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.2.left q)).val =
        ConcreteNamedSubstitution.freeVarsFormulaRoot π d 0 u := by
  let P := projectionParameters T U V σ π d
  let b := SyntaxPolynomial.formulaExpression V π d
  let f := (categoricalSyntax T V σ π d).occurrenceAlgebra.str.2
  have hp := parameterOperation_value T M P (listObject T V) (listObject T V) (listObject T V) b f q
  have hr := parameterValueMap_representation T M P (listObject T V) (listObject T V) b p u q hq
  exact (congrArg Subtype.val hp).trans (occurrenceFormula_operation_value T V M π d u
    ((F T M).map (parameterValueMap T P (listObject T V) (listObject T V) b) q) hr)

end Models

section Commutation
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem payloadOccurrence_term_commutes_model
    (q : Obj T M (((SyntaxPolynomial.termExpression V σ d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionSourceAlgebra T U V σ π d).a).left) :
    (F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.1.left
      ((F T M).map (((SyntaxPolynomial.termExpression V σ d).withParameters
        (projectionParameters T U V σ π d)).eval.map (payloadOccurrenceProjectionPair T U V σ π d)).left q) =
      (F T M).map (payloadProjectionFamily T U V σ π d .occurrences false).left
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
  let φ := occurrenceComputation V σ π d x t
  let f := payloadProjectionFamily T U V σ π d .occurrences false
  let g := payloadProjectionFamily T U V σ π d .occurrences true
  have hf : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map f.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .occurrences false p z hz
  have hg : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d true : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map g.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .occurrences true p z hz
  let v := ConcreteNamedSubstitution.mapChildren φ φ a u
  let k := (a.withParameters P).eval.map (payloadOccurrenceProjectionPair T U V σ π d)
  let z := (F T M).map k.left q
  have hz := constantRepresentation_map T M f g p φ φ hf hg a u q hu
  let left := (F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.1.left z
  let source := (F T M).map (projectionSourceAlgebra T U V σ π d).str.1.left q
  have hs := (constantLeaf_model T M P (syntaxCarrier V σ π d false) p
    (Coding.constructor false a u) source).mp (parameterTerm_coordinate T M P a b p u q hu)
  have hlp : (F T M).map prod.fst left = p :=
    (over_value T M (projectionOccurrenceAlgebra T U V σ π d).str.1 z).trans
      ((over_value T M k q).trans rfl)
  have hl := parameterOccurrenceTerm_value T U V σ π d M p v z hz
  have hr := payloadProjectionFamily_value T U V σ π d M .occurrences false p source hs.1
  have hrvalue := hr.trans ((congrArg φ hs.2).trans
    (occurrenceComputation_term_constructor V σ π d x t u hguard))
  apply modelProduct_ext T M
  · exact hlp.trans ((over_value T M f source).trans hs.1).symm
  · exact Subtype.ext (hl.trans hrvalue.symm)

theorem payloadOccurrence_formula_commutes_model
    (q : Obj T M (((SyntaxPolynomial.formulaExpression V π d).withParameters
      (projectionParameters T U V σ π d)).eval.obj (projectionSourceAlgebra T U V σ π d).a).left) :
    (F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.2.left
      ((F T M).map (((SyntaxPolynomial.formulaExpression V π d).withParameters
        (projectionParameters T U V σ π d)).eval.map (payloadOccurrenceProjectionPair T U V σ π d)).left q) =
      (F T M).map (payloadProjectionFamily T U V σ π d .occurrences true).left
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
  let φ := occurrenceComputation V σ π d x t
  let f := payloadProjectionFamily T U V σ π d .occurrences false
  let g := payloadProjectionFamily T U V σ π d .occurrences true
  have hf : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d false : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map f.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .occurrences false p z hz
  have hg : ∀ z : Obj T M (P ⨯ (syntaxCarrier V σ π d true : PredicateCategory T)),
      (F T M).map prod.fst z = p → ((F T M).map prod.snd ((F T M).map g.left z)).val =
        φ ((F T M).map prod.snd z).val := by
    intro z hz
    exact payloadProjectionFamily_value T U V σ π d M .occurrences true p z hz
  let v := ConcreteNamedSubstitution.mapChildren φ φ b u
  let k := (b.withParameters P).eval.map (payloadOccurrenceProjectionPair T U V σ π d)
  let z := (F T M).map k.left q
  have hz := constantRepresentation_map T M f g p φ φ hf hg b u q hu
  let left := (F T M).map (projectionOccurrenceAlgebra T U V σ π d).str.2.left z
  let source := (F T M).map (projectionSourceAlgebra T U V σ π d).str.2.left q
  have hs := (constantLeaf_model T M P (syntaxCarrier V σ π d true) p
    (Coding.constructor true b u) source).mp (parameterFormula_coordinate T M P a b p u q hu)
  have hlp : (F T M).map prod.fst left = p :=
    (over_value T M (projectionOccurrenceAlgebra T U V σ π d).str.2 z).trans
      ((over_value T M k q).trans rfl)
  have hl := parameterOccurrenceFormula_value T U V σ π d M p v z hz
  have hr := payloadProjectionFamily_value T U V σ π d M .occurrences true p source hs.1
  have hrvalue := hr.trans ((congrArg φ hs.2).trans
    (occurrenceComputation_formula_constructor V σ π d x t u hguard))
  apply modelProduct_ext T M
  · exact hlp.trans ((over_value T M g source).trans hs.1).symm
  · exact Subtype.ext (hl.trans hrvalue.symm)

end Commutation

def payloadOccurrenceProjectionHom : (projectionSourceAlgebra T U V σ π d) ⟶
    (projectionOccurrenceAlgebra T U V σ π d) where
  f := payloadOccurrenceProjectionPair T U V σ π d
  h := by
    apply Prod.ext
    · apply Over.OverMorphism.ext
      change (((SyntaxPolynomial.termExpression V σ d).withParameters (projectionParameters T U V σ π d)).eval.map
        (payloadOccurrenceProjectionPair T U V σ π d)).left ≫ (projectionOccurrenceAlgebra T U V σ π d).str.1.left =
          (projectionSourceAlgebra T U V σ π d).str.1.left ≫ (payloadOccurrenceProjectionPair T U V σ π d).1.left
      apply PredicateInterpretation.jointly_faithful T
      intro M _ _
      rw [Functor.map_comp,Functor.map_comp]
      apply ConcreteCategory.hom_ext
      intro q
      exact payloadOccurrence_term_commutes_model T U V σ π d M q
    · apply Over.OverMorphism.ext
      change (((SyntaxPolynomial.formulaExpression V π d).withParameters (projectionParameters T U V σ π d)).eval.map
        (payloadOccurrenceProjectionPair T U V σ π d)).left ≫ (projectionOccurrenceAlgebra T U V σ π d).str.2.left =
          (projectionSourceAlgebra T U V σ π d).str.2.left ≫ (payloadOccurrenceProjectionPair T U V σ π d).2.left
      apply PredicateInterpretation.jointly_faithful T
      intro M _ _
      rw [Functor.map_comp,Functor.map_comp]
      apply ConcreteCategory.hom_ext
      intro q
      exact payloadOccurrence_formula_commutes_model T U V σ π d M q

/-- The comparison morphism is the parameterization of the already proved occurrence Hom,
not an assumed payload-field equation. -/
def knownOccurrenceProjectionHom : (projectionSourceAlgebra T U V σ π d) ⟶
    (projectionOccurrenceAlgebra T U V σ π d) :=
  parameterAlgebraHom (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
    (projectionParameters T U V σ π d) (occurrenceHom T V σ π d)

theorem payloadOccurrenceProjectionPair_eq : payloadOccurrenceProjectionPair T U V σ π d =
    (knownOccurrenceProjectionHom T U V σ π d).f := by
  have h := (categoricalSyntax T V σ π d).stable (projectionParameters T U V σ π d)
  exact congrArg Endofunctor.Algebra.Hom.f
    (h.hom_ext (payloadOccurrenceProjectionHom T U V σ π d) (knownOccurrenceProjectionHom T U V σ π d))

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
