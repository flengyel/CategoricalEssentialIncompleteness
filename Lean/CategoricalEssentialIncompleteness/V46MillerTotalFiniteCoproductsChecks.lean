import CategoricalEssentialIncompleteness.V46MillerTotalFiniteCoproducts
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : HasFiniteCoproducts (TotalCategory P) := inferInstance
example : (emptyCarrier (P := P)).support = (∅ : Set ℕ) := rfl
example : IsInitial (⟨emptyCarrier⟩ : TotalCategory P) := initialIsInitial
example (X Y : TotalCategory P) : IsColimit (BinaryCofan.mk (totalInl X Y) (totalInr X Y)) := coproductIsColimit X Y
end CategoricalEssentialIncompleteness.V46.Miller.Total
