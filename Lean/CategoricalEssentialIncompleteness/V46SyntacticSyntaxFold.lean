/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAlgebra
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecode
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInterpretation

/-! # The concrete two-sorted fold in an arbitrary parameter slice -/

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

/-- The evaluator graph supplies an actual arrow from the constant term
family, with its finite record hidden only as an existential witness. -/
def termFoldMap : P ⨯ termCarrier a b ⟶ B.a.1.left :=
  toRawProduct T P (termCarrier a b) ≫
    representedArrow T ((decode T P a b B).evaluationMorphism false)

def formulaFoldMap : P ⨯ formulaCarrier a b ⟶ B.a.2.left :=
  toRawProduct T P (formulaCarrier a b) ≫
    representedArrow T ((decode T P a b B).evaluationMorphism true)

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

theorem termFoldMap_eval (q : Obj T M (P ⨯ termCarrier a b)) (x : Obj T M B.a.1.left) :
    (F T M).map (termFoldMap T a b B) q = x ↔
      ((decode T P a b B).evaluationFormula false).val.Evalb
        ![((F T M).map (prod.fst : P ⨯ termCarrier a b ⟶ P) q).val,
          ((F T M).map (prod.snd : P ⨯ termCarrier a b ⟶ termCarrier a b) q).val, x.val] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (F T M).map (toRawProduct T P (termCarrier a b) ≫
    representedArrow T ((decode T P a b B).evaluationMorphism false)) q = x ↔ _
  rw [Functor.map_comp]
  change (F T M).map (representedArrow T ((decode T P a b B).evaluationMorphism false))
    ((F T M).map (toRawProduct T P (termCarrier a b)) q) = x ↔ _
  refine (PredicateInterpretation.map_class_eq_iff T M
    ((decode T P a b B).evaluationMorphism false)
    ((F T M).map (toRawProduct T P (termCarrier a b)) q) x).trans ?_
  change ((decode T P a b B).evaluationGraph false).val.Evalb
    ![((F T M).map (toRawProduct T P (termCarrier a b)) q).val, x.val] ↔ _
  rw [toRawProduct_value]
  simp [SliceAlgebra.evaluationGraph]

theorem formulaFoldMap_eval (q : Obj T M (P ⨯ formulaCarrier a b))
    (x : Obj T M B.a.2.left) :
    (F T M).map (formulaFoldMap T a b B) q = x ↔
      ((decode T P a b B).evaluationFormula true).val.Evalb
        ![((F T M).map (prod.fst : P ⨯ formulaCarrier a b ⟶ P) q).val,
          ((F T M).map (prod.snd : P ⨯ formulaCarrier a b ⟶ formulaCarrier a b) q).val,
            x.val] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  change (F T M).map (toRawProduct T P (formulaCarrier a b) ≫
    representedArrow T ((decode T P a b B).evaluationMorphism true)) q = x ↔ _
  rw [Functor.map_comp]
  change (F T M).map (representedArrow T ((decode T P a b B).evaluationMorphism true))
    ((F T M).map (toRawProduct T P (formulaCarrier a b)) q) = x ↔ _
  refine (PredicateInterpretation.map_class_eq_iff T M
    ((decode T P a b B).evaluationMorphism true)
    ((F T M).map (toRawProduct T P (formulaCarrier a b)) q) x).trans ?_
  change ((decode T P a b B).evaluationGraph true).val.Evalb
    ![((F T M).map (toRawProduct T P (formulaCarrier a b)) q).val, x.val] ↔ _
  rw [toRawProduct_value]
  simp [SliceAlgebra.evaluationGraph]

end Models

theorem termFoldMap_over : termFoldMap T a b B ≫ B.a.1.hom =
    (prod.fst : P ⨯ termCarrier a b ⟶ P) := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  have he := (termFoldMap_eval T a b B M q
    ((F T M).map (termFoldMap T a b B) q)).mp rfl
  have hf := ((decode T P a b B).evaluation_fiber false _ _ _ he).2.2.2
  exact (chosenGraph_map_iff T M B.a.1.hom
    ((F T M).map (termFoldMap T a b B) q) ((F T M).map prod.fst q)).mp hf

theorem formulaFoldMap_over : formulaFoldMap T a b B ≫ B.a.2.hom =
    (prod.fst : P ⨯ formulaCarrier a b ⟶ P) := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [Functor.map_comp]
  apply ConcreteCategory.hom_ext
  intro q
  have he := (formulaFoldMap_eval T a b B M q
    ((F T M).map (formulaFoldMap T a b B) q)).mp rfl
  have hf := ((decode T P a b B).evaluation_fiber true _ _ _ he).2.2.2
  exact (chosenGraph_map_iff T M B.a.2.hom
    ((F T M).map (formulaFoldMap T a b B) q) ((F T M).map prod.fst q)).mp hf

/-- Both components are actual morphisms in the supplied parameter slice. -/
def termFold : constantFamily P (termCarrier a b) ⟶ B.a.1 :=
  Over.homMk (termFoldMap T a b B) (termFoldMap_over T a b B)

def formulaFold : constantFamily P (formulaCarrier a b) ⟶ B.a.2 :=
  Over.homMk (formulaFoldMap T a b B) (formulaFoldMap_over T a b B)

def fold : (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).a ⟶ B.a :=
  (termFold T a b B, formulaFold T a b B)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
