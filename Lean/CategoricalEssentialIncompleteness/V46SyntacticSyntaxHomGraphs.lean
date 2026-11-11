/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxCandidateValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality

/-! # Actual algebra-hom equations give the guarded scalar constructor laws -/

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
variable (f : constantFamily P (termCarrier a b) ⟶ B.a.1)
variable (g : constantFamily P (formulaCarrier a b) ⟶ B.a.2)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The candidate term equation follows from the actual term component
of an algebra-hom equation. Candidate values are not assumed in advance. -/
theorem candidateTermEquation
    (hcomm : (a.withParameters P).eval.map
      ((f, g) : (constantFamily P (termCarrier a b),
        constantFamily P (formulaCarrier a b)) ⟶ B.a) ≫ B.str.1 =
          (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1 ≫ f)
    (p u x : M) (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (termCarrier a b) (formulaCarrier a b) a).val.Evalb ![u]) :
    (rawArrow T f).val.Evalb ![p, Coding.constructor false a u, x] ↔
      ∃ v : M, (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p, u, v] ∧
        (decode T P a b B).termOp.val.Evalb ![p, v, x] := by
  let pp : Obj T M P := ⟨p, hp⟩
  obtain ⟨q, hq, _⟩ := constantRepresentation_exists T M P
    (termCarrier a b) (formulaCarrier a b) a pp u hu
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1
  let k := (a.withParameters P).eval.map
    ((f, g) : (constantFamily P (termCarrier a b),
      constantFamily P (formulaCarrier a b)) ⟶ B.a)
  let w := (F T M).map c.left q
  let z := (F T M).map k.left q
  have hw := parameterTerm_coordinate T M P a b pp u q hq
  have he : (F T M).map B.str.1.left z = (F T M).map f.left w := by
    have hl := congrArg Over.Hom.left hcomm
    simp only [Over.comp_left] at hl
    have hm := congrArg (F T M).map hl
    rw [Functor.map_comp, Functor.map_comp] at hm
    exact ConcreteCategory.congr_hom hm q
  constructor
  · intro hx
    have hxv := (rawArrow_value_iff T M f pp (Coding.constructor false a u) x w hw).mp hx
    obtain ⟨v, hv⟩ := mapRaw_arrow_exists T M f g a pp u hu
    have hz := representation_arrow_map T M f g a pp u v q hq hv
    refine ⟨v, hv, ?_⟩
    apply (decodedOperation_value_iff T M B.a a B.str.1 pp v x z hz).mpr
    exact hxv.trans (congrArg Subtype.val he).symm
  · rintro ⟨v, hv, hop⟩
    have hz := representation_arrow_map T M f g a pp u v q hq hv
    have hxv := (decodedOperation_value_iff T M B.a a B.str.1 pp v x z hz).mp hop
    exact (rawArrow_value_iff T M f pp (Coding.constructor false a u) x w hw).mpr
      (hxv.trans (congrArg Subtype.val he))

theorem candidateFormulaEquation
    (hcomm : (b.withParameters P).eval.map
      ((f, g) : (constantFamily P (termCarrier a b),
        constantFamily P (formulaCarrier a b)) ⟶ B.a) ≫ B.str.2 =
          (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2 ≫ g)
    (p u x : M) (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (termCarrier a b) (formulaCarrier a b) b).val.Evalb ![u]) :
    (rawArrow T g).val.Evalb ![p, Coding.constructor true b u, x] ↔
      ∃ v : M, (mapRaw P (rawArrow T f) (rawArrow T g) b).val.Evalb ![p, u, v] ∧
        (decode T P a b B).formulaOp.val.Evalb ![p, v, x] := by
  let pp : Obj T M P := ⟨p, hp⟩
  obtain ⟨q, hq, _⟩ := constantRepresentation_exists T M P
    (termCarrier a b) (formulaCarrier a b) b pp u hu
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2
  let k := (b.withParameters P).eval.map
    ((f, g) : (constantFamily P (termCarrier a b),
      constantFamily P (formulaCarrier a b)) ⟶ B.a)
  let w := (F T M).map c.left q
  let z := (F T M).map k.left q
  have hw := parameterFormula_coordinate T M P a b pp u q hq
  have he : (F T M).map B.str.2.left z = (F T M).map g.left w := by
    have hl := congrArg Over.Hom.left hcomm
    simp only [Over.comp_left] at hl
    have hm := congrArg (F T M).map hl
    rw [Functor.map_comp, Functor.map_comp] at hm
    exact ConcreteCategory.congr_hom hm q
  constructor
  · intro hx
    have hxv := (rawArrow_value_iff T M g pp (Coding.constructor true b u) x w hw).mp hx
    obtain ⟨v, hv⟩ := mapRaw_arrow_exists T M f g b pp u hu
    have hz := representation_arrow_map T M f g b pp u v q hq hv
    refine ⟨v, hv, ?_⟩
    apply (decodedOperation_value_iff T M B.a b B.str.2 pp v x z hz).mpr
    exact hxv.trans (congrArg Subtype.val he).symm
  · rintro ⟨v, hv, hop⟩
    have hz := representation_arrow_map T M f g b pp u v q hq hv
    have hxv := (decodedOperation_value_iff T M B.a b B.str.2 pp v x z hz).mp hop
    exact (rawArrow_value_iff T M g pp (Coding.constructor true b u) x w hw).mpr
      (hxv.trans (congrArg Subtype.val he))

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
