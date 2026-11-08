import CategoricalEssentialIncompleteness.V46MillerSyntaxState

noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)

example : Uniform.Enumerable P (Raw.fiberStack R X Y) := Raw.fiberStack_enumerable R X Y
example : Uniform.Enumerable P (Raw.status R X Y) := Raw.status_enumerable R X Y
example (p : SyntaxPolynomial (Total.TotalCategory P)) : Primrec₂ (Raw.refill p) := Raw.refill_primrec p

example (p : SyntaxPolynomial (Total.TotalCategory P)) (r s stack u rest : ℕ)
    (hr : r ∈ R.obj.support)
    (hs : s ∈ (Raw.carrier (Total.terminalCarrier (P := P)) (Total.terminalCarrier (P := P)) p).support)
    (hst : Raw.fiberStack R X Y (r,stack))
    (he : Raw.refill p s stack = adjoin u rest) :
    Raw.fiber R X Y p (r,u) ∧ Raw.fiberStack R X Y (r,rest) :=
  Raw.refill_fiber R X Y p r s stack u rest hr hs hst he

example (Q : SyntacticSyntax.RawPolynomial)
    (F : SyntacticPredicates.Carrier → Total.TotalCategory P) (s stack : ℕ) :
    Raw.refill (Q.mapCoefficients F) s stack = SyntacticSyntax.Coding.refill Q s stack :=
  Raw.refill_mapped Q F s stack
