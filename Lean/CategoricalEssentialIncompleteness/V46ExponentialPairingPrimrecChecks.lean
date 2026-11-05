import CategoricalEssentialIncompleteness.V46ExponentialPairingPrimrec

/-! The standard function is explicitly identified and primitive recursive. -/
open CategoricalEssentialIncompleteness.V46.ExponentialPairing

example (a b : ℕ) : code a b = Nat.pred (2 ^ a * (2 * b + 1)) := code_nat a b
example : Primrec₂ (code (M := ℕ)) := code_primrec
