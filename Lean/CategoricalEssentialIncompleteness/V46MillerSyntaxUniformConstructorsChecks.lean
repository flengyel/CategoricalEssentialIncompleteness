import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformConstructors

noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)

example (formula : Bool) (r u value : ℕ) (hr : r ∈ R.obj.support)
    (hu : u ∈ (Raw.carrier (Raw.uniformWords false p q) (Raw.uniformWords true p q)
      (if formula then q else p)).support) :
    (value ∈ Total.val (Raw.uniformFold hT hF formula).left.hom
      (Nat.pair r (SyntacticSyntax.Coding.constructor formula (Raw.skeleton (if formula then q else p)) u)) ↔
      ∃ v,Raw.UniformMapValues hT hF (if formula then q else p) r u v ∧
        value ∈ (if formula then Raw.operation hF else Raw.operation hT) (r,v)) :=
  Raw.uniformFold_constructor hT hF formula r u value hr hu
