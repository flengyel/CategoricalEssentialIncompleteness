import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors

noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

example (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) {u : ℕ}
    (hu : u ∈ (Raw.carrier (Raw.uniformWords false p q) (Raw.uniformWords true p q)
      (if formula then q else p)).support) :
    SyntacticSyntax.Coding.constructor formula (Raw.skeleton (if formula then q else p)) u ∈
      (Raw.uniformWords formula p q).support := Raw.uniformWords_constructor p q formula hu

example (p q Q : SyntaxPolynomial (Total.TotalCategory P)) {u : ℕ}
    (hu : u ∈ (Raw.carrier (Raw.uniformWords false p q) (Raw.uniformWords true p q) Q).support) :
    Raw.wordGuard p q (SyntacticSyntax.Coding.childrenWord (Raw.skeleton Q) u) :=
  Raw.wordGuard_children p q Q hu
