/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSchemeReflection


/-! # All seven-scheme parameters yield finite Hilbert proofs from Γ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedProofImage
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "U" => Total.underlying (P:=P)
local notation "S" => syntaxData P σ π d

example (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertOne p)) :=
  SchemeReflection.one P σ π d Γ p

example (p : (U).obj (((S).algebra.a.2 ⨯ (S).algebra.a.2) ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertTwo p)) :=
  SchemeReflection.two P σ π d Γ p

example (p : (U).obj ((S).algebra.a.2 ⨯ (S).algebra.a.2)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertThree p)) :=
  SchemeReflection.three P σ π d Γ p

example (p : (U).obj (S).instantiationParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertInstantiation p)) :=
  SchemeReflection.instantiation P σ π d Γ p

omit Γ in
example (p : (U).obj (S).distributionParameters) :
    let base := (U).map (S).distributionInclusion p
    ((U).map prod.fst base).val ∉
      (decodeFormula P σ π d ((U).map prod.fst ((U).map prod.snd base))).freeVariables :=
  SchemeReflection.distribution_absent P σ π d p

example (p : (U).obj (S).distributionParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertDistribution p)) :=
  SchemeReflection.distribution P σ π d Γ p

example (p : (U).obj (S).algebra.a.1) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertReflexivity p)) :=
  SchemeReflection.reflexivity P σ π d Γ p

example (p : (U).obj (S).equalitySchemeParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertEquality p)) :=
  SchemeReflection.equality P σ π d Γ p

example (l : (U).obj (S).logicalParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).logicalAxioms l)) :=
  logical_parameter_finite P σ π d Γ l

example (i : Fin 7) (p : (U).obj (SyntacticFiniteNamedSchemes.schemeParameters (S) i)) :
    FiniteAxiomProof σ π d Γ
      (decodeFormula P σ π d ((U).map (SyntacticFiniteNamedSchemes.schemeMorphism (S) i) p)) :=
  logical_scheme_finite P σ π d Γ i p
