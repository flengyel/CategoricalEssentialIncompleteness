/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPlainUltrapowerSoundness
import CategoricalEssentialIncompleteness.V46SyntacticAxiomPredicates

/-! # The actual Gamma axiom filter satisfies the soundness hypothesis

Gamma enumerates literal named formula words. The actual axiom object filters
it by the constructed sentence image. Its chosen sentence code is not assumed
to be the formula word.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedGammaSoundness
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (Γ : Carrier)
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ

/-- Satisfaction is required only of enumerated literal sentences, in
semantic K. The arithmetic code model remains N. -/
def Models (ρ : ℕ → K) : Prop :=
  ∀ φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d,
    Γ.val.Evalb ![formulaCode φ] → φ.freeVariables = [] →
      φ.Holds functions relations ρ

/-- The literal Gamma model hypothesis implies validity of the actual
axiom morphism, through its proved formula-coordinate chart. -/
theorem axioms_valid (ρ : ℕ → K) (hΓ : Models σ π d Γ functions relations ρ) :
    FirstOrderModelSoundness.AxiomsProperty 𝗣𝗔
      (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S)
      (A := (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ : PredicateCategory 𝗣𝗔))
      (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ) ℕ
      (Valid σ π d functions relations) := by
  intro a
  let s := (G).map (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ) a
  let word := (G).map (S).sentenceInclusion s
  have hw : word.val = a.val := by
    have he := SyntacticAxiomPredicates.axioms_formula_value
      𝗣𝗔 variableCarrier σ π d ℕ Γ a
    simpa only [Functor.map_comp_apply] using he
  have ha := ((SyntacticAxiomPredicates.axiomCarrier_eval
    𝗣𝗔 variableCarrier σ π d ℕ Γ a.val).mp a.property).1
  have hg : Γ.val.Evalb ![formulaCode (decodeFormula σ π d word)] := by
    rw [decodeFormula_code,hw]
    exact ha
  have hc := decode_sentence_closed σ π d s
  have hh := hΓ (decodeFormula σ π d word) hg hc
  have hv := (sentence_valid_iff σ π d functions relations s ρ).mpr hh
  change Valid σ π d functions relations
    ((G).map (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ ≫
      (S).sentenceInclusion) a)
  simpa only [Functor.map_comp_apply] using hv

/-- The actual Gamma-filtered sentence conclusion has the unique
standard validity factor, from literal satisfaction of Gamma. -/
theorem exists_unique_factor (ρ : ℕ → K) (hΓ : Models σ π d Γ functions relations ρ) :
    ∃! e : Obj 𝗣𝗔 ℕ
        (FirstOrderModelSoundness.sentenceProofObject 𝗣𝗔
          (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S)
          (A := (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ : PredicateCategory 𝗣𝗔))
          (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ)) ⟶
      (sentenceValiditySet σ π d functions relations : Type),
      e ≫ sentenceValidityInclusion σ π d functions relations = (G).map
        (FirstOrderModelSoundness.sentenceConclusion 𝗣𝗔
          (V := (variableCarrier : PredicateCategory 𝗣𝗔)) (σ := σ) (π := π) (d := d) (S)
          (A := (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ : PredicateCategory 𝗣𝗔))
          (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ)) :=
  exists_unique_soundnessFactor σ π d functions relations
    (A := (SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔 variableCarrier σ π d Γ : PredicateCategory 𝗣𝗔))
    (SyntacticAxiomPredicates.axioms 𝗣𝗔 variableCarrier σ π d Γ)
    (axioms_valid σ π d Γ functions relations ρ hΓ)

end CategoricalEssentialIncompleteness.V46.NamedGammaSoundness
