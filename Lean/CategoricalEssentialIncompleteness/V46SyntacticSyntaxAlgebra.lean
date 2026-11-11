/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRepresentation
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParserLaws

/-! # The actual two-sorted algebra on literal postfix words -/

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

/-- Membership witnesses belong to the formula, outside the literal word. -/
def termCarrier (a b : RawPolynomial) : Carrier := Postfix.carrier false a b

def formulaCarrier (a b : RawPolynomial) : Carrier := Postfix.carrier true a b

/-- The guard is essential: the total numerical constructor extension is
used as an algebra constructor only on valid raw polynomial inputs. -/
def termConstructorGraph (a b : RawPolynomial) : Graph :=
  let C := rawCarrier (termCarrier a b) (formulaCarrier a b) a
  let g := Coding.constructorGraph false a
  .mkSigma “u w. !C.val u ∧ !g.val w u”

def formulaConstructorGraph (a b : RawPolynomial) : Graph :=
  let C := rawCarrier (termCarrier a b) (formulaCarrier a b) b
  let g := Coding.constructorGraph true b
  .mkSigma “u w. !C.val u ∧ !g.val w u”

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem termConstructorGraph_eval (a b : RawPolynomial) (u w : M) :
    (termConstructorGraph a b).val.Evalb ![u, w] ↔
      (rawCarrier (termCarrier a b) (formulaCarrier a b) a).val.Evalb ![u] ∧
        w = Coding.constructor false a u := by
  simp [termConstructorGraph]

@[simp] theorem formulaConstructorGraph_eval (a b : RawPolynomial) (u w : M) :
    (formulaConstructorGraph a b).val.Evalb ![u, w] ↔
      (rawCarrier (termCarrier a b) (formulaCarrier a b) b).val.Evalb ![u] ∧
        w = Coding.constructor true b u := by
  simp [formulaConstructorGraph]

end Models

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def termConstructorMorphism (a b : RawPolynomial) :
    GraphMorphism T (rawCarrier (termCarrier a b) (formulaCarrier a b) a)
      (termCarrier a b) where
  graph := termConstructorGraph a b
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro u w h
    obtain ⟨hu, rfl⟩ := (termConstructorGraph_eval a b u w).mp h
    exact ⟨hu, Postfix.term_constructor_carrier a b u hu⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro u hu
    refine ⟨Coding.constructor false a u, (termConstructorGraph_eval a b u _).mpr
      ⟨hu, rfl⟩, ?_⟩
    intro w hw
    exact ((termConstructorGraph_eval a b u w).mp hw).2

def formulaConstructorMorphism (a b : RawPolynomial) :
    GraphMorphism T (rawCarrier (termCarrier a b) (formulaCarrier a b) b)
      (formulaCarrier a b) where
  graph := formulaConstructorGraph a b
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro u w h
    obtain ⟨hu, rfl⟩ := (formulaConstructorGraph_eval a b u w).mp h
    exact ⟨hu, Postfix.formula_constructor_carrier a b u hu⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro u hu
    refine ⟨Coding.constructor true b u, (formulaConstructorGraph_eval a b u _).mpr
      ⟨hu, rfl⟩, ?_⟩
    intro w hw
    exact ((formulaConstructorGraph_eval a b u w).mp hw).2

/-- The categorical polynomial is its actual chosen product/coproduct
object; the numerical encoder and guarded constructor give its structure. -/
def postfixAlgebra (a b : SyntaxPolynomial (PredicateCategory T)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b) where
  a := (termCarrier a b, formulaCarrier a b)
  str := (representedArrow T (encodePolynomial T (termCarrier a b) (formulaCarrier a b) a) ≫
    representedArrow T (termConstructorMorphism T a b),
    representedArrow T (encodePolynomial T (termCarrier a b) (formulaCarrier a b) b) ≫
      representedArrow T (formulaConstructorMorphism T a b))


section AlgebraModels
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The actual raw-input arrow appends exactly the literal root record. -/
theorem termConstructor_value (a b : RawPolynomial)
    (u : Obj T M (rawCarrier (termCarrier a b) (formulaCarrier a b) a)) :
    ((F T M).map (representedArrow T (termConstructorMorphism T a b)) u).val =
      Coding.constructor false a u.val := by
  have h := (PredicateInterpretation.map_class_eq_iff T M (termConstructorMorphism T a b)
    u ((F T M).map (representedArrow T (termConstructorMorphism T a b)) u)).mp rfl
  exact ((termConstructorGraph_eval a b u.val _).mp h).2

theorem formulaConstructor_value (a b : RawPolynomial)
    (u : Obj T M (rawCarrier (termCarrier a b) (formulaCarrier a b) b)) :
    ((F T M).map (representedArrow T (formulaConstructorMorphism T a b)) u).val =
      Coding.constructor true b u.val := by
  have h := (PredicateInterpretation.map_class_eq_iff T M (formulaConstructorMorphism T a b)
    u ((F T M).map (representedArrow T (formulaConstructorMorphism T a b)) u)).mp rfl
  exact ((formulaConstructorGraph_eval a b u.val _).mp h).2

/-- The categorical term structure map is the printed postfix constructor
on the coordinate of its actual chosen polynomial input. -/
theorem postfixTerm_value (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (a.eval.obj ((postfixAlgebra T a b).a)))
    (h : (baseRepresentation T (termCarrier a b) (formulaCarrier a b) a).val.Evalb
      ![u, z.val]) :
    ((F T M).map (postfixAlgebra T a b).str.1 z).val = Coding.constructor false a u := by
  let U : PredicateCategory T := rawCarrier (termCarrier a b) (formulaCarrier a b) a
  let uu : Obj T M U := ⟨u, (baseRepresentation_support T M
    (termCarrier a b) (formulaCarrier a b) a u z.val h).1⟩
  have he : (F T M).map (representedArrow T
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) a)) z = uu := by
    apply (PredicateInterpretation.map_class_eq_iff T M
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) a) z uu).mpr
    simpa [encodePolynomial] using h
  change ((F T M).map (representedArrow T
    (encodePolynomial T (termCarrier a b) (formulaCarrier a b) a) ≫
      representedArrow T (termConstructorMorphism T a b)) z).val = _
  rw [Functor.map_comp]
  change ((F T M).map (representedArrow T (termConstructorMorphism T a b))
    ((F T M).map (representedArrow T
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) a)) z)).val = _
  rw [he]
  exact termConstructor_value T M a b uu

theorem postfixFormula_value (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (b.eval.obj ((postfixAlgebra T a b).a)))
    (h : (baseRepresentation T (termCarrier a b) (formulaCarrier a b) b).val.Evalb
      ![u, z.val]) :
    ((F T M).map (postfixAlgebra T a b).str.2 z).val = Coding.constructor true b u := by
  let U : PredicateCategory T := rawCarrier (termCarrier a b) (formulaCarrier a b) b
  let uu : Obj T M U := ⟨u, (baseRepresentation_support T M
    (termCarrier a b) (formulaCarrier a b) b u z.val h).1⟩
  have he : (F T M).map (representedArrow T
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) b)) z = uu := by
    apply (PredicateInterpretation.map_class_eq_iff T M
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) b) z uu).mpr
    simpa [encodePolynomial] using h
  change ((F T M).map (representedArrow T
    (encodePolynomial T (termCarrier a b) (formulaCarrier a b) b) ≫
      representedArrow T (formulaConstructorMorphism T a b)) z).val = _
  rw [Functor.map_comp]
  change ((F T M).map (representedArrow T (formulaConstructorMorphism T a b))
    ((F T M).map (representedArrow T
      (encodePolynomial T (termCarrier a b) (formulaCarrier a b) b)) z)).val = _
  rw [he]
  exact formulaConstructor_value T M a b uu

end AlgebraModels

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
