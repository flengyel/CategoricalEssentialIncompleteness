import CategoricalEssentialIncompleteness.V46MillerTotalRealization
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
example (z : Point) : HasFiniteLimits (WideSubcategory (isTotal (C := SplitObject (Uniform.PointObject z)))) := inferInstance
example (z : Point) : HasFiniteCoproducts (CanonicalTotal z) := inferInstance
example (z : Point) : Regular (CanonicalTotal z) := inferInstance
example (z : Point) : FinitaryExtensive (CanonicalTotal z) := inferInstance
end CategoricalEssentialIncompleteness.V46.Miller.Total
