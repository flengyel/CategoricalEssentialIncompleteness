import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.NatVectors

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.PrimitiveParserChecks
example (a b : RawPolynomial) :
    Nat.Primrec (Nat.unpaired (Postfix.run a b : ℕ → ℕ → ℕ)) := run_natPrimrec a b

example (q : RawPolynomial) : Primrec₂ (Coding.refill q : ℕ → ℕ → ℕ) := refill_primrec q

example (q : RawPolynomial) (formula : Bool) :
    Primrec (Coding.constructor formula q : ℕ → ℕ) := constructor_primrec formula q

example (a b : RawPolynomial) :
    Primrec (fun p : (ℕ × ℕ) × ℕ => Postfix.runPrefix a b p.1.1 p.2 p.1.2) :=
  runPrefix_primrec a b
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.PrimitiveParserChecks
