import CategoricalEssentialIncompleteness.V46MillerTotalLimits
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example : HasFiniteLimits (TotalCategory P) := inferInstance
example : HasFiniteProducts (TotalCategory P) := inferInstance
example (X Y : TotalCategory P) : IsLimit (BinaryFan.mk (totalFst X Y) (totalSnd X Y)) := productIsLimit X Y
example : IsTerminal (⟨terminalCarrier⟩ : TotalCategory P) := terminalIsTerminal
example {X Y : TotalCategory P} (f g : X ⟶ Y) : IsLimit (Limits.Fork.ofι (equalizerι f g) (equalizer_condition f g)) := equalizerIsLimit f g
end CategoricalEssentialIncompleteness.V46.Miller.Total
