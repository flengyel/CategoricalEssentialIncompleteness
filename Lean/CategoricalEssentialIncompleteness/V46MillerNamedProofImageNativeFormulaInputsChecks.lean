/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaInputs

/-! # Native formula substitution and the actual full option output

Every branch is evaluated on the existing standard PA state and then
transported by its proved morphism square. The actual slice fold is
compared by native induction. Failure remains part of the formula state.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionInputChecks
open NamedFiniteSyntax NamedPostfixEncoding
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P := P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "Tm" => Term (Symbols σ) d
local notation "Fm" => Formula (Symbols σ) (Symbols π) d
local notation "R₀" => CategoricalSyntax.substitutionParameters
  (NamedSyntaxComparison.sourceSyntax (variableCarrier : PredicateCategory 𝗣𝗔) σ π d)
local notation "R" => CategoricalSyntax.substitutionParameters (NamedProofImage.syntaxData P σ π d)
local notation "b" => SyntaxPolynomial.formulaExpression (variableCarrier : PredicateCategory 𝗣𝗔) π d
local notation "q" => SyntaxPolynomial.formulaExpression
  (Functor.obj (Syntax.predicateFunctor P) (variableCarrier : PredicateCategory 𝗣𝗔))
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d
local notation "c" => NamedSyntaxComparison.substitutionStateIso P (V) σ π d
local notation "e" => NamedSyntaxComparison.substitutionParameterIso P (V) σ π d
local notation "j" => NamedSyntaxComparison.substitutionFormulaStateIso P (V) σ π d

open CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitution

example (r : (U).obj (R)) (z : Standard.Data (S₀).substitutionCarriers (b)) :
    PointFrame.Data (R) r (S).substitutionAlgebra.a (q) := formulaStateInputData P σ π d r z

example :
    NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers (S).substitutionCarriers (c)
      .formula .formula rfl=(j) := formula_leaf_chart P σ π d

example :
    NamedSyntaxComparison.constructorInput P (S₀).substitutionCarriers (S).substitutionCarriers (c)
      (.product (.coefficient (V)) .formula) (.product (.coefficient ((F).obj (V))) .formula) rfl=
      NamedSyntaxComparison.Options.productIso (F) (Iso.refl ((F).obj (V))) (j) := quantifier_input_chart P σ π d

example {C : Type} [Category.{0} C] [HasFiniteCoproducts C]
    (G : C ⥤ Type) {Q : C} {A0 A1 A2 A3 A4 Z : Over Q}
    (f0 : A0 ⟶ Z) (f1 : A1 ⟶ Z) (f2 : A2 ⟶ Z) (f3 : A3 ⟶ Z) (f4 : A4 ⟶ Z)
    (z : (((G.obj A0.left ⊕ G.obj A1.left) ⊕ G.obj A2.left) ⊕ G.obj A3.left) ⊕ G.obj A4.left) :
    G.map (coprod.desc (coprod.desc (coprod.desc (coprod.desc f0 f1) f2) f3) f4).left
      (fivePoint G A0 A1 A2 A3 A4 z) =
        match z with
        | .inl (.inl (.inl (.inl x))) => G.map f0.left x
        | .inl (.inl (.inl (.inr x))) => G.map f1.left x
        | .inl (.inl (.inr x)) => G.map f2.left x
        | .inl (.inr x) => G.map f3.left x
        | .inr x => G.map f4.left x := over_five_value G f0 f1 f2 f3 f4 z

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionInputChecks
