/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence

/-! # Literal values of the plain postfix constructor

The structure map appends the root record to its ordered polynomial input. Membership
witnesses remain outside the syntax word.
-/

@[expose] public section
noncomputable section
universe v u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart

theorem maps_comp_apply {C : Type u} [Category.{v} C] (G : C ⥤ Type)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (x : G.obj X) :
    G.map (f ≫ g) x = G.map g (G.map f x) :=
  ConcreteCategory.congr_hom (G.map_comp f g) x

section PlainValues
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  (a b : SyntaxPolynomial (PredicateCategory T))

/-- The raw input is encoded from the ordered polynomial input; the inverse plain
comparison fixes every child word. -/
def plainRawInput :
    @Quiver.Hom (PredicateCategory T) inferInstance
      (a.eval.obj (SyntacticSyntax.plainPostfixAlgebra T a b).a)
      (SyntacticSyntax.rawCarrier (SyntacticSyntax.termCarrier a b)
        (SyntacticSyntax.formulaCarrier a b) a) :=
  a.eval.map (SyntacticSyntax.plainPairIso T a b).inv ≫
    representedArrow T (SyntacticSyntax.encodePolynomial T
      (SyntacticSyntax.termCarrier a b) (SyntacticSyntax.formulaCarrier a b) a)

theorem plainTerm_constructor_value (M : Type) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : Obj T M (a.eval.obj (SyntacticSyntax.plainPostfixAlgebra T a b).a)) :
    ((SyntacticLists.F T M).map (SyntacticSyntax.plainPostfixAlgebra T a b).str.1 z).val =
      SyntacticSyntax.Coding.constructor false a
        (((SyntacticLists.F T M).map (plainRawInput T a b) z).val) := by
  let w := (SyntacticLists.F T M).map
    (representedArrow T (SyntacticSyntax.termConstructorMorphism T a b))
      ((SyntacticLists.F T M).map (plainRawInput T a b) z)
  have hplain : (((SyntacticLists.F T M).map
      (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom) w).val = w.val := by
    have h := (PredicateInterpretation.map_class_eq_iff T M
      (SyntacticSyntax.Postfix.toPlainMorphism T false a b) w
      ((SyntacticLists.F T M).map
        (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom w)).mp rfl
    exact ((GraphMorphism.identityGraph_eval _ _ _).mp h).2
  have ha : (SyntacticSyntax.plainPostfixAlgebra T a b).str.1 =
      (plainRawInput T a b ≫ representedArrow T
        (SyntacticSyntax.termConstructorMorphism T a b)) ≫
          (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom := by
    let f := a.eval.map (SyntacticSyntax.plainPairIso T a b).inv
    let g := representedArrow T (SyntacticSyntax.encodePolynomial T
      (SyntacticSyntax.termCarrier a b) (SyntacticSyntax.formulaCarrier a b) a)
    let h := representedArrow T (SyntacticSyntax.termConstructorMorphism T a b)
    let k := (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom
    change f ≫ ((g ≫ h) ≫ k) = ((f ≫ g) ≫ h) ≫ k
    exact (Category.assoc f (g ≫ h) k).symm.trans
      (congrArg (fun q => q ≫ k) (Category.assoc f g h).symm)

  have h0 := congrArg (fun k => (((SyntacticLists.F T M).map k) z).val) ha
  have h1 := congrArg Subtype.val (@maps_comp_apply (PredicateCategory T) inferInstance
    (SyntacticLists.F T M) _ _ _
    (plainRawInput T a b ≫ representedArrow T (SyntacticSyntax.termConstructorMorphism T a b))
    (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom z)
  have h2 := congrArg (fun y => (((SyntacticLists.F T M).map
    (SyntacticSyntax.Postfix.plainCarrierIso T false a b).hom) y).val)
    (@maps_comp_apply (PredicateCategory T) inferInstance (SyntacticLists.F T M) _ _ _
      (plainRawInput T a b) (representedArrow T (SyntacticSyntax.termConstructorMorphism T a b)) z)
  exact h0.trans (h1.trans (h2.trans (hplain.trans
    (SyntacticSyntax.termConstructor_value T M a b
      ((SyntacticLists.F T M).map (plainRawInput T a b) z)))))

end PlainValues

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
