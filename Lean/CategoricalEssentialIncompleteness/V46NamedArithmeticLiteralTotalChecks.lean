import CategoricalEssentialIncompleteness.V46NamedArithmeticLiteralTotal
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates NamedArithmeticSignature NamedArithmeticLiteralTotal

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ literalSentence := theta φ hφ

example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (n : M) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) (omegaPoint 𝗣𝗔 M n)).val.val =
      NamedArithmeticFixedSubstitution.value φ n := canonical_value_at φ hφ M n


example (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (x : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M (ArithmeticOmegaComparison.identityOmega 𝗣𝗔))
    (y : PredicateInterpretation.CanonicalDomain 𝗣𝗔 M literalSentence) :
    (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (theta φ hφ) x = y ↔
      (NamedArithmeticFixedSubstitution.morphism φ hφ).graph.val.Evalb ![x.val.val,y.val.val] :=
  canonical_graph φ hφ M x y
