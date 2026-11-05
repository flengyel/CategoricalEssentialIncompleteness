/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAlgebra
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter

/-! # Actual parameterized constructors retain the literal postfix coordinates -/

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

/-- Parameterization changes only the parameter coordinate; its value
projection is the actual original operation on the base polynomial. -/
theorem parameterOperation_snd (P X Y Z : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (f : a.eval.obj (X, Y) ⟶ Z) :
    (SyntaxPolynomial.parameterComparison P (X, Y) a ≫
      (constantFamilyFunctor P).map f).left ≫ prod.snd =
        parameterValueMap T P X Y a ≫ f := by
  unfold parameterValueMap
  change ((SyntaxPolynomial.parameterComparison P (X, Y) a).left ≫
    prod.map (𝟙 P) f) ≫ prod.snd =
      ((SyntaxPolynomial.parameterComparison P (X, Y) a).left ≫ prod.snd) ≫ f
  simp only [Category.assoc, prod.map_snd]

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
/-- The operation comparison is read at every interpreted source point. -/
theorem parameterOperation_value (P X Y Z : PredicateCategory T)
    (a : SyntaxPolynomial (PredicateCategory T)) (f : a.eval.obj (X, Y) ⟶ Z)
    (q : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P X, constantFamily P Y)).left) :
    (F T M).map (prod.snd : P ⨯ Z ⟶ Z)
      ((F T M).map (SyntaxPolynomial.parameterComparison P (X, Y) a ≫
        (constantFamilyFunctor P).map f).left q) =
          (F T M).map f ((F T M).map (parameterValueMap T P X Y a) q) := by
  have h := congrArg (F T M).map (parameterOperation_snd T P X Y Z a f)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h q

/-- The term constructor in the actual parameter slice appends the
same record as the base constructor, on the same child-word input. -/
theorem parameterTerm_value (P : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (q : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left)
    (hq : (constantRepresentation T P (termCarrier a b) (formulaCarrier a b) a).val.Evalb
      ![p.val, u, q.val]) :
    ((F T M).map (prod.snd : P ⨯ termCarrier a b ⟶ termCarrier a b)
      ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
        (postfixAlgebra T a b) P).str.1.left q)).val = Coding.constructor false a u := by
  have hv := parameterOperation_value T M P (termCarrier a b) (formulaCarrier a b)
    (termCarrier a b) a (postfixAlgebra T a b).str.1 q
  have hr := parameterValueMap_representation T M P (termCarrier a b)
    (formulaCarrier a b) a p u q hq
  exact (congrArg Subtype.val hv).trans
    (postfixTerm_value T M a b u
      ((F T M).map (parameterValueMap T P (termCarrier a b) (formulaCarrier a b) a) q) hr)

theorem parameterFormula_value (P : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (q : Obj T M ((b.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left)
    (hq : (constantRepresentation T P (termCarrier a b) (formulaCarrier a b) b).val.Evalb
      ![p.val, u, q.val]) :
    ((F T M).map (prod.snd : P ⨯ formulaCarrier a b ⟶ formulaCarrier a b)
      ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
        (postfixAlgebra T a b) P).str.2.left q)).val = Coding.constructor true b u := by
  have hv := parameterOperation_value T M P (termCarrier a b) (formulaCarrier a b)
    (formulaCarrier a b) b (postfixAlgebra T a b).str.2 q
  have hr := parameterValueMap_representation T M P (termCarrier a b)
    (formulaCarrier a b) b p u q hq
  exact (congrArg Subtype.val hv).trans
    (postfixFormula_value T M a b u
      ((F T M).map (parameterValueMap T P (termCarrier a b) (formulaCarrier a b) b) q) hr)

/-- The full constant-family coordinate of the source constructor is
therefore fixed, including the unchanged parameter. -/
theorem parameterTerm_coordinate (P : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (q : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left)
    (hq : (constantRepresentation T P (termCarrier a b) (formulaCarrier a b) a).val.Evalb
      ![p.val, u, q.val]) :
    (constantLeaf T P (termCarrier a b)).val.Evalb
      ![p.val, Coding.constructor false a u,
        ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
          (postfixAlgebra T a b) P).str.1.left q).val] := by
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.1
  let w := (F T M).map c.left q
  have hsrc := (constantRepresentation_support T M P (termCarrier a b)
    (formulaCarrier a b) a p.val u q.val hq).2.2.2
  have hp : (F T M).map (prod.fst : P ⨯ termCarrier a b ⟶ P) w = p :=
    (over_value T M c q).trans
      ((chosenGraph_map_iff T M
        ((a.withParameters P).eval.obj
          (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).hom
            q p).mp hsrc)
  have hv := parameterTerm_value T M P a b p u q hq
  have hs := (chosenGraph_map_iff T M (prod.snd : P ⨯ termCarrier a b ⟶ termCarrier a b)
    w ((F T M).map prod.snd w)).mpr rfl
  erw [hv] at hs
  have hfst := (chosenGraph_map_iff T M (prod.fst : P ⨯ termCarrier a b ⟶ P) w p).mpr hp
  simpa [constantLeaf] using And.intro hfst hs

theorem parameterFormula_coordinate (P : PredicateCategory T)
    (a b : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u : M)
    (q : Obj T M ((b.withParameters P).eval.obj
      (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).left)
    (hq : (constantRepresentation T P (termCarrier a b) (formulaCarrier a b) b).val.Evalb
      ![p.val, u, q.val]) :
    (constantLeaf T P (formulaCarrier a b)).val.Evalb
      ![p.val, Coding.constructor true b u,
        ((F T M).map (SyntaxPolynomial.algebraWithParameters a b
          (postfixAlgebra T a b) P).str.2.left q).val] := by
  let c := (SyntaxPolynomial.algebraWithParameters a b (postfixAlgebra T a b) P).str.2
  let w := (F T M).map c.left q
  have hsrc := (constantRepresentation_support T M P (termCarrier a b)
    (formulaCarrier a b) b p.val u q.val hq).2.2.2
  have hp : (F T M).map (prod.fst : P ⨯ formulaCarrier a b ⟶ P) w = p :=
    (over_value T M c q).trans
      ((chosenGraph_map_iff T M
        ((b.withParameters P).eval.obj
          (constantFamily P (termCarrier a b), constantFamily P (formulaCarrier a b))).hom
            q p).mp hsrc)
  have hv := parameterFormula_value T M P a b p u q hq
  have hs := (chosenGraph_map_iff T M
    (prod.snd : P ⨯ formulaCarrier a b ⟶ formulaCarrier a b)
      w ((F T M).map prod.snd w)).mpr rfl
  erw [hv] at hs
  have hfst := (chosenGraph_map_iff T M (prod.fst : P ⨯ formulaCarrier a b ⟶ P) w p).mpr hp
  simpa [constantLeaf] using And.intro hfst hs

end Models

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax
