import CategoricalEssentialIncompleteness.V46MillerTotalCoproducts
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : CoprodStruct (Carrier P) := inferInstance
example : CategoryTheory.HasCoproducts (Carrier P) := inferInstance
example : RestrictionCoproducts (Carrier P) := inferInstance
example (X Y : Carrier P) (n : ℕ) : 2*n ∈ (coproduct X Y).support ↔ n ∈ X.support := mem_coproduct_even X Y n
example (X Y : Carrier P) (n : ℕ) : 2*n+1 ∈ (coproduct X Y).support ↔ n ∈ Y.support := mem_coproduct_odd X Y n
example {X Y Z : Carrier P} (f : X ⟶ Z) (g : Y ⟶ Z) : inl X Y ≫ copairRaw f g = f := inl_copairRaw f g
example {X Y Z : Carrier P} (f : X ⟶ Z) (g : Y ⟶ Z) : inr X Y ≫ copairRaw f g = g := inr_copairRaw f g
end CategoricalEssentialIncompleteness.V46.Miller.Total
