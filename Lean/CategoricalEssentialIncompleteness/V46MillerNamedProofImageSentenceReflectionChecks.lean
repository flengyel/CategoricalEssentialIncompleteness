import CategoricalEssentialIncompleteness.V46MillerNamedProofImageSentenceReflection
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => NamedProofImage.syntaxData P σ π d
example (s : Total.underlying.obj (S).sentenceObject) :
    (NamedProofImage.decodeFormula P σ π d (Total.underlying.map (S).sentenceInclusion s)).freeVariables=[] :=
  NamedProofImage.sentence_inclusion_closed P σ π d s
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
example (a : Total.underlying.obj (NamedProofImage.axiomCarrier P σ π d Γ hΓ)) :
    NamedPostfixEncoding.formulaCode (NamedProofImage.decodeFormula P σ π d
      (Total.underlying.map (NamedProofImage.axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion) a))∈Γ :=
  NamedProofImage.axiom_word_member P σ π d Γ hΓ a
example (a : Total.underlying.obj (NamedProofImage.axiomCarrier P σ π d Γ hΓ)) :
    FiniteAxiomProof σ π d Γ (NamedProofImage.decodeFormula P σ π d
      (Total.underlying.map (NamedProofImage.axioms P σ π d Γ hΓ ≫ (S).sentenceInclusion) a)) :=
  NamedProofImage.axiom_finite_proof P σ π d Γ hΓ a
