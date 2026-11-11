/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteNamedDerivations


/-! # Statement checks in `V46SyntacticFiniteNamedDerivationsChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedDerivations
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedDerivations.Checks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) (Γ : Carrier)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
local notation "S" => plainCategoricalSyntax T V σ π d

example (p : Obj T M (S).instantiationParameters) :
    Derives T V σ π d Γ M ((F T M).map (S).hilbertInstantiation p) :=
  logical_scheme T V σ π d Γ M 3 p

example (p : Obj T M (S).equalitySchemeParameters) :
    Derives T V σ π d Γ M ((F T M).map (S).hilbertEquality p) :=
  logical_scheme T V σ π d Γ M 6 p

example (p : Obj T M ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : Derives T V σ π d Γ M ((F T M).map prod.fst p))
    (himp : Derives T V σ π d Γ M ((F T M).map (S).implicationConstructor p)) :
    Derives T V σ π d Γ M ((F T M).map prod.snd p) :=
  modus_ponens T V σ π d Γ M p hφ himp

example (φ : Obj T M (S).algebra.a.2) (h : Derives T V σ π d Γ M φ) :
    ∃ p : Obj T M (SyntacticGeneratedTheory.proofAlgebra T V σ π d
      (SyntacticAxiomPredicates.axioms T V σ π d Γ)).a.left,
      (F T M).map (SyntacticGeneratedTheory.conclusion T V σ π d
        (SyntacticAxiomPredicates.axioms T V σ π d Γ)) p = φ :=
  realizes T V σ π d Γ M h
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedDerivations.Checks
