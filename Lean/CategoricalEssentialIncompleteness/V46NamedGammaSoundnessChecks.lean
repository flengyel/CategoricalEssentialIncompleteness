import CategoricalEssentialIncompleteness.V46NamedGammaSoundness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedGammaSoundnessChecks
open NamedGammaSoundness
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) (Γ : Carrier)
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 (variableCarrier : PredicateCategory 𝗣𝗔) σ π d
local notation "G" => F 𝗣𝗔 ℕ

example (ρ : ℕ → K) (hΓ : Models σ π d Γ functions relations ρ) :
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
  exists_unique_factor σ π d Γ functions relations ρ hΓ

end CategoricalEssentialIncompleteness.V46.NamedGammaSoundnessChecks
