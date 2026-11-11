/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeFormulaTransport

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

namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionTransportChecks
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

example (r₀ : (N).obj (R₀))
    (z : Standard.Data (S₀).substitutionCarriers (b)) :
    (U).map (prod.snd : (R) ⨯ (S).substitutionCarriers.2 ⟶ _)
      ((U).map (S).substitutionAlgebra.str.2.left
        ((U).map (PointFrame.realize (R) ((U).map (e).hom (sourcePoint P (R₀) r₀))
          (S).substitutionAlgebra.a (q)
          (formulaStateInputData P σ π d ((U).map (e).hom (sourcePoint P (R₀) r₀)) z)).left ⟨0,rfl⟩))=
      (U).map (j).hom (sourcePoint P (S₀).substitutionCarriers.2
        ((N).map (prod.snd : (R₀) ⨯ (S₀).substitutionCarriers.2 ⟶ _)
          ((N).map (S₀).substitutionAlgebra.str.2.left
            (Standard.liftData (R₀) r₀ (S₀).substitutionCarriers (b) z).val))) := formula_step_transport P σ π d r₀ z

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage.NativeSubstitutionTransportChecks
