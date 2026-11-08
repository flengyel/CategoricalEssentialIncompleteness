import CategoricalEssentialIncompleteness.V46MillerListsFold
noncomputable section
open CategoryTheory FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)
example : Lists.family R V ⟶ X := Lists.fold V h0 hc
example : (Lists.fold V h0 hc).left ≫ X.hom=(Lists.family R V).hom := Lists.fold_parameter V h0 hc
example (r value : ℕ) :
    value ∈ Total.val (Lists.fold V h0 hc).left.hom (Nat.pair r 0) ↔ value ∈ Syntax.Raw.operation h0 (r,0) :=
  Lists.fold_nil V h0 hc r value
example (r a list value : ℕ) :
    value ∈ Total.val (Lists.fold V h0 hc).left.hom (Nat.pair r (adjoin a list)) ↔
      ∃ w,w ∈ Total.val (Lists.fold V h0 hc).left.hom (Nat.pair r list) ∧
        value ∈ Syntax.Raw.operation hc (r,Nat.pair a w) := Lists.fold_adjoin V h0 hc r a list value
