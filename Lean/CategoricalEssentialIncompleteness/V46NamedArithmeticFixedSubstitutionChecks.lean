import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSubstitution
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticSignature NamedArithmeticFixedSubstitution
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).val.Evalb
      ![value φ n] := value_sentence (M := M) φ hφ n
example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    GraphMorphism 𝗣𝗔 variableSymbols
      (ConcreteNamedComparison.literalSentenceCarrier 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound) := morphism φ hφ
example (φ : Formula) : Primrec (value φ : ℕ → ℕ) := value_primrec φ
