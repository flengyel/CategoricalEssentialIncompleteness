/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageNativeClosure


/-! # Finite Gamma support under Gen and ordered MP -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "V" => CategoryTheory.Functor.obj (Syntax.predicateFunctor P)
  (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
example (z : Total.underlying.obj ((V) ⨯ (S).algebra.a.2))
    (h : FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.snd z))) :
    FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d
      (Total.underlying.map (S).quantifierConstructor z)) :=
  NamedProofImage.generalization_finite P σ π d Γ z h
example (z : Total.underlying.obj ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.fst z)))
    (hi : FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d
      (Total.underlying.map (S).implicationConstructor z))) :
    FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d (Total.underlying.map prod.snd z)) :=
  NamedProofImage.modusPonens_finite P σ π d Γ z hφ hi
