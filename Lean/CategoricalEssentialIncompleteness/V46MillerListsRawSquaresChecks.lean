import CategoricalEssentialIncompleteness.V46MillerListsRawSquares
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X : Over R} (V : Total.Carrier P)
variable (h0 : Syntax.Raw.object R X X .unit ⟶ X)
variable (hc : Syntax.Raw.object R X X (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ⟶ X)
example : Lists.rawNil R V ≫ Lists.fold V h0 hc=h0 := Lists.fold_rawNil V h0 hc
example : Lists.rawCons R V ≫ Lists.fold V h0 hc=
    Syntax.Raw.rawAction R (Lists.family R V) (Lists.family R V) X X (Lists.fold V h0 hc) (Lists.fold V h0 hc)
      (.product (.coefficient (⟨V⟩ : Total.TotalCategory P)) .term) ≫ hc := Lists.fold_rawCons V h0 hc
