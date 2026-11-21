/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFoldValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorValues
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorLaws

/-! # The evaluator morphisms form a two-sorted algebra morphism -/

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

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem termFold_commutes_model
    (q : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left) :
    (F T M).map B.str.1.left
      ((F T M).map ((a.withParameters P).eval.map (fold T a b B)).left q) =
        (F T M).map (termFold T a b B).left
          ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
            (postfixAlgebra T a b) P).str.1.left q) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let A := decode T P a b B
  let p := (F T M).map ((a.withParameters P).eval.obj
    (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).hom q
  obtain ⟨u, hq⟩ := constantRepresentation_cover T M P
    (termCarrier a b) (formulaCarrier a b) a p q rfl
  have hu := (constantRepresentation_support T M P (termCarrier a b)
    (formulaCarrier a b) a p.val u q.val hq).2.1
  obtain ⟨v, hv⟩ := mapRaw_arrow_exists T M (termFold T a b B)
    (formulaFold T a b B) a p u hu
  let k := (a.withParameters P).eval.map (fold T a b B)
  let z := (F T M).map k.left q
  let y := (F T M).map B.str.1.left z
  have hz := representation_arrow_map T M (termFold T a b B) (formulaFold T a b B)
    a p u v q hq hv
  have hop : A.termOp.val.Evalb ![p.val, v, y.val] :=
    (decodedOperation_value_iff T M B.a a B.str.1 p v y.val z hz).mpr rfl
  have heval : (A.evaluationFormula false).val.Evalb
      ![p.val, Coding.constructor false a u, y.val] :=
    (A.evaluation_constructor false p.val u y.val p.property hu).mpr
      ⟨v, (fold_mapRaw T a b B M a p.val u v).mp hv, hop⟩
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1
  let w := (F T M).map c.left q
  have hw := parameterTerm_coordinate T M P a b p u q hq
  have hf := (termFold_rawArrow T a b B M p.val (Coding.constructor false a u) y.val).mpr
    heval
  have hy := (rawArrow_value_iff T M (termFold T a b B) p
    (Coding.constructor false a u) y.val w hw).mp hf
  exact Subtype.ext hy

theorem formulaFold_commutes_model
    (q : Obj T M ((b.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left) :
    (F T M).map B.str.2.left
      ((F T M).map ((b.withParameters P).eval.map (fold T a b B)).left q) =
        (F T M).map (formulaFold T a b B).left
          ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
            (postfixAlgebra T a b) P).str.2.left q) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let A := decode T P a b B
  let p := (F T M).map ((b.withParameters P).eval.obj
    (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).hom q
  obtain ⟨u, hq⟩ := constantRepresentation_cover T M P
    (termCarrier a b) (formulaCarrier a b) b p q rfl
  have hu := (constantRepresentation_support T M P (termCarrier a b)
    (formulaCarrier a b) b p.val u q.val hq).2.1
  obtain ⟨v, hv⟩ := mapRaw_arrow_exists T M (termFold T a b B)
    (formulaFold T a b B) b p u hu
  let k := (b.withParameters P).eval.map (fold T a b B)
  let z := (F T M).map k.left q
  let y := (F T M).map B.str.2.left z
  have hz := representation_arrow_map T M (termFold T a b B) (formulaFold T a b B)
    b p u v q hq hv
  have hop : A.formulaOp.val.Evalb ![p.val, v, y.val] :=
    (decodedOperation_value_iff T M B.a b B.str.2 p v y.val z hz).mpr rfl
  have heval : (A.evaluationFormula true).val.Evalb
      ![p.val, Coding.constructor true b u, y.val] :=
    (A.evaluation_constructor true p.val u y.val p.property hu).mpr
      ⟨v, (fold_mapRaw T a b B M b p.val u v).mp hv, hop⟩
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2
  let w := (F T M).map c.left q
  have hw := parameterFormula_coordinate T M P a b p u q hq
  have hf := (formulaFold_rawArrow T a b B M p.val (Coding.constructor true b u) y.val).mpr
    heval
  have hy := (rawArrow_value_iff T M (formulaFold T a b B) p
    (Coding.constructor true b u) y.val w hw).mp hf
  exact Subtype.ext hy

end Models

/-- Constructor commutation is proved for quotient morphisms, by joint faithfulness over
all T-models after the finite-record root laws. -/
theorem termFold_commutes :
    (a.withParameters P).eval.map (fold T a b B) ≫ B.str.1 =
      (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1 ≫
        termFold T a b B := by
  apply Over.OverMorphism.ext
  change ((a.withParameters P).eval.map (fold T a b B)).left ≫ B.str.1.left =
    (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1.left ≫
      (termFold T a b B).left
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp, Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  exact termFold_commutes_model T a b B M q

theorem formulaFold_commutes :
    (b.withParameters P).eval.map (fold T a b B) ≫ B.str.2 =
      (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2 ≫
        formulaFold T a b B := by
  apply Over.OverMorphism.ext
  change ((b.withParameters P).eval.map (fold T a b B)).left ≫ B.str.2.left =
    (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2.left ≫
      (formulaFold T a b B).left
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  rw [Functor.map_comp, Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  exact formulaFold_commutes_model T a b B M q

/-- The finite-record evaluator is now an algebra morphism into every algebra in the
supplied parameter slice. -/
def foldHom : (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P) ⟶ B where
  f := fold T a b B
  h := Prod.ext (termFold_commutes T a b B) (formulaFold_commutes T a b B)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
