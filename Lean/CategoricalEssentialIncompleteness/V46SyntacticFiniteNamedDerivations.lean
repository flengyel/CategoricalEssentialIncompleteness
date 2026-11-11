/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivationsStandard
public import CategoricalEssentialIncompleteness.V46SyntacticAxiomPredicates
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheory
public import CategoricalEssentialIncompleteness.V46SyntacticFiniteNamedSchemes

/-! # Seven named schemes, enumerated axioms and the two finite proof rules

Scheme instances retain the genuine parameter objects, including the two
admissibility pullbacks and the distribution-absence fiber. These rules
are interpreted in the constructed proof object, with ordered MP premises.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedDerivations
open SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d

/-- The actual parameter objects of the constructed plain syntax. -/
def schemeParameters : Fin 7 → PredicateCategory T :=
  SyntacticFiniteNamedSchemes.schemeParameters (S)

def schemeMorphism (i : Fin 7) : @Quiver.Hom (PredicateCategory T) inferInstance
    (schemeParameters T V σ π d i) (S).algebra.a.2 :=
  SyntacticFiniteNamedSchemes.schemeMorphism (S) i

def schemeInjection (i : Fin 7) : @Quiver.Hom (PredicateCategory T) inferInstance
    (schemeParameters T V σ π d i) (S).logicalParameters :=
  SyntacticFiniteNamedSchemes.schemeInjection (S) i

theorem schemeInjection_formula (i : Fin 7) :
    schemeInjection T V σ π d i ≫ (S).logicalAxioms = schemeMorphism T V σ π d i :=
  SyntacticFiniteNamedSchemes.schemeInjection_formula (S) i

variable (Γ : Carrier)
local notation "A" => SyntacticAxiomPredicates.axiomCarrier T V σ π d Γ
local notation "aΓ" => SyntacticAxiomPredicates.axioms T V σ π d Γ
local notation "R" => CategoricalSyntax.logicalRules (plainCategoricalSyntax T V σ π d)
  (SyntacticAxiomPredicates.axioms T V σ π d Γ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

abbrev Derives (φ : Obj T M (S).algebra.a.2) : Prop :=
  SyntacticFiniteDerivations.Derives T M R φ

theorem logical_parameter (p : Obj T M (S).logicalParameters) :
    Derives T V σ π d Γ M ((F T M).map (S).logicalAxioms p) := by
  let label := (F T M).map
    (coprod.inl (C := PredicateCategory T) («X» := (S).logicalParameters) («Y» := A)) p
  have h : Derives T V σ π d Γ M ((F T M).map ((R).conclusion 0) label) :=
    SyntacticFiniteDerivations.Derives.node (T := T) (M := M) («R» := R) 0 label (fun k => k.elim0)
  change Derives T V σ π d Γ M
    ((F T M).map (coprod.desc (S).logicalAxioms (aΓ ≫ (S).sentenceInclusion)) label) at h
  dsimp only [label] at h
  erw [← Functor.map_comp_apply,coprod.inl_desc] at h
  exact h

/-- All seven schemes enter by their actual parameter injections. -/
theorem logical_scheme (i : Fin 7) (p : Obj T M (schemeParameters T V σ π d i)) :
    Derives T V σ π d Γ M ((F T M).map (schemeMorphism T V σ π d i) p) := by
  have h := logical_parameter T V σ π d Γ M
    ((F T M).map (schemeInjection T V σ π d i) p)
  erw [← Functor.map_comp_apply,schemeInjection_formula] at h
  exact h

/-- Every enumerated sentence enters through the constructed axiom
subobject, with no supplied closure or derivability certificate. -/
theorem nonlogical_axiom (p : Obj T M A) :
    Derives T V σ π d Γ M ((F T M).map (aΓ ≫ (S).sentenceInclusion) p) := by
  let label := (F T M).map
    (coprod.inr (C := PredicateCategory T) («X» := (S).logicalParameters) («Y» := A)) p
  have h : Derives T V σ π d Γ M ((F T M).map ((R).conclusion 0) label) :=
    SyntacticFiniteDerivations.Derives.node (T := T) (M := M) («R» := R) 0 label (fun k => k.elim0)
  change Derives T V σ π d Γ M
    ((F T M).map (coprod.desc (S).logicalAxioms (aΓ ≫ (S).sentenceInclusion)) label) at h
  dsimp only [label] at h
  erw [← Functor.map_comp_apply,coprod.inr_desc] at h
  exact h

theorem generalization (p : Obj T M (V ⨯ (S).algebra.a.2))
    (h : Derives T V σ π d Γ M ((F T M).map prod.snd p)) :
    Derives T V σ π d Γ M ((F T M).map (S).quantifierConstructor p) := by
  have children : ∀ k : Fin 1,
      Derives T V σ π d Γ M
        ((F T M).map ((R).premises 1 ≫ finiteChild T (S).algebra.a.2 1 k) p) := by
    intro k
    change Derives T V σ π d Γ M
      ((F T M).map (prod.snd ≫ finiteChild T (S).algebra.a.2 1 k) p)
    erw [finiteChild_one,Category.comp_id]
    exact h
  exact SyntacticFiniteDerivations.Derives.node (T := T) (M := M) («R» := R) 1 p children

/-- The second child proves exactly φ⇒ψ, and the first child proves φ.
The shared label fixes ψ without identifying the two premise fibers. -/
theorem modus_ponens (p : Obj T M ((S).algebra.a.2 ⨯ (S).algebra.a.2))
    (hφ : Derives T V σ π d Γ M ((F T M).map prod.fst p))
    (himp : Derives T V σ π d Γ M ((F T M).map (S).implicationConstructor p)) :
    Derives T V σ π d Γ M ((F T M).map prod.snd p) := by
  have children : ∀ k : Fin 2,
      Derives T V σ π d Γ M
        ((F T M).map ((R).premises 2 ≫ finiteChild T (S).algebra.a.2 2 k) p) := by
    intro k
    fin_cases k
    · change Derives T V σ π d Γ M
        ((F T M).map (prod.lift prod.fst (S).implicationConstructor ≫
          finiteChild T (S).algebra.a.2 2 0) p)
      erw [finiteChild_two_zero,prod.lift_fst]
      exact hφ
    · change Derives T V σ π d Γ M
        ((F T M).map (prod.lift prod.fst (S).implicationConstructor ≫
          finiteChild T (S).algebra.a.2 2 1) p)
      erw [finiteChild_two_one,prod.lift_snd]
      exact himp
  exact SyntacticFiniteDerivations.Derives.node (T := T) (M := M) («R» := R) 2 p children

/-- Finite named-rule derivability gives an actual generated-proof point. -/
theorem realizes {φ : Obj T M (S).algebra.a.2} (h : Derives T V σ π d Γ M φ) :
    ∃ p : Obj T M (SyntacticGeneratedTheory.proofAlgebra T V σ π d aΓ).a.left,
      (F T M).map (SyntacticGeneratedTheory.conclusion T V σ π d aΓ) p = φ :=
  SyntacticFiniteDerivations.realizes T M R h

end CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedDerivations
