import CategoricalEssentialIncompleteness.V46NamedPostfixData

namespace CategoricalEssentialIncompleteness.V46.NamedPostfixDataChecks
open NamedPostfixEncoding
example (n : ℕ) (f g : Fin n → ℕ) (h : childTuple n f = childTuple n g) : f = g :=
  childTuple_injective n f g h
example (d : ℕ) (i j : Fin (d + 1)) (u v : ℕ)
    (h : arityInput d i u = arityInput d j v) : i = j ∧ u = v :=
  arityInput_injective d i j u v h
example (X Y : ℕ → Prop) (n payload : ℕ)
    (h : RawData X Y (SyntaxPolynomial.power .term n) payload) :
    ∃ f : Fin n → ℕ, payload = childTuple n f ∧ ∀ i, X (f i) :=
  childTuple_decomposition n payload h
end CategoricalEssentialIncompleteness.V46.NamedPostfixDataChecks
