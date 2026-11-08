import CategoricalEssentialIncompleteness.V46MillerSyntaxRawSums
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P:Uniform.Family} (R:Total.TotalCategory P) (X Y:Over R)
variable (a b:SyntaxPolynomial (Total.TotalCategory P))

example {Z:Over R} (f:Raw.object R X Y a⟶Z) (g:Raw.object R X Y b⟶Z) (n m:ℕ) :
    m∈Total.val (Raw.sumCopair R X Y a b f g).left.hom n ↔
      ((Nat.unpair (Nat.unpair n).2).2=0 ∧
        m∈Total.val f.left.hom (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)) ∨
      ((Nat.unpair (Nat.unpair n).2).2=1 ∧
        m∈Total.val g.left.hom (Nat.pair (Nat.unpair n).1 (Nat.unpair (Nat.unpair n).2).1)) :=
  Raw.sumCopair_graph R X Y a b f g n m

example {Z:Over R} (f:Raw.object R X Y a⟶Z) (g:Raw.object R X Y b⟶Z) (n:ℕ) :
    (Total.val (Raw.sumCopair R X Y a b f g).left.hom n).Dom ↔
      Raw.fiber R X Y (.sum a b) (Nat.unpair n) := Raw.sumCopair_domain R X Y a b f g n

example {Z:Over R} (f:Raw.object R X Y a⟶Z) (g:Raw.object R X Y b⟶Z) :
    (Raw.sumCopair R X Y a b f g).left ≫ Z.hom=Raw.projection R X Y (.sum a b) :=
  Raw.sumCopair_parameter R X Y a b f g

example {Z:Over R} (f:Raw.object R X Y a⟶Z) (g:Raw.object R X Y b⟶Z) :
    Raw.sumInl R X Y a b ≫ Raw.sumCopair R X Y a b f g=f := Raw.sumInl_copair R X Y a b f g

example {Z:Over R} (f:Raw.object R X Y a⟶Z) (g:Raw.object R X Y b⟶Z) :
    Raw.sumInr R X Y a b ≫ Raw.sumCopair R X Y a b f g=g := Raw.sumInr_copair R X Y a b f g

example {Z:Over R} {f g:Raw.object R X Y (.sum a b)⟶Z}
    (h0:Raw.sumInl R X Y a b ≫ f=Raw.sumInl R X Y a b ≫ g)
    (h1:Raw.sumInr R X Y a b ≫ f=Raw.sumInr R X Y a b ≫ g) : f=g :=
  Raw.sum_hom_ext R X Y a b h0 h1

example : IsColimit (BinaryCofan.mk (Raw.sumInl R X Y a b) (Raw.sumInr R X Y a b)) :=
  Raw.sumIsColimit R X Y a b

example : Raw.object R X Y (.sum a b) ≅ (Raw.object R X Y a ⨿ Raw.object R X Y b) :=
  Raw.sumIso R X Y a b

example : Raw.sumInl R X Y a b ≫ (Raw.sumIso R X Y a b).hom=coprod.inl := Raw.sumIso_inl R X Y a b
example : Raw.sumInr R X Y a b ≫ (Raw.sumIso R X Y a b).hom=coprod.inr := Raw.sumIso_inr R X Y a b
