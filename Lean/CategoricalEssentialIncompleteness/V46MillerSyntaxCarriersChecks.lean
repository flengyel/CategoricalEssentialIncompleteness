import CategoricalEssentialIncompleteness.V46MillerSyntaxCarriers

noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

example (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    Uniform.Enumerable P (fun n => n ∈ (Raw.uniformWords formula p q).support) :=
  (Raw.uniformWords formula p q).enumerable

example (a b : SyntacticSyntax.RawPolynomial) (formula : Bool) :
    (Raw.uniformWords formula (a.mapCoefficients (predicateFunctor P).obj)
      (b.mapCoefficients (predicateFunctor P).obj)).support=(words P formula a b).support :=
  Raw.uniformWords_mapped_support a b formula

example {R : Total.TotalCategory P} {X Y : Over R} {p q : SyntaxPolynomial (Total.TotalCategory P)}
    (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)
    (formula : Bool) {r word new : ℕ}
    (hw : word ∈ (Raw.uniformWords formula p q).support)
    (hn : new ∈ Raw.evaluation hT hF (Nat.pair r word)) :
    ∃ value,new=Adjoin.adjoin (Nat.pair value (if formula then 1 else 0)) 0+1 :=
  Raw.uniformWords_singleton hT hF formula hw hn
