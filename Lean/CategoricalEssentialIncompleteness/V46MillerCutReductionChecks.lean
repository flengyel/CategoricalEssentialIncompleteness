import CategoricalEssentialIncompleteness.V46MillerCutReduction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Checks
example (a : Point) (ha : IsMiller a) :
    ∃ h : ℕ → ℕ,Computable h ∧
      h ⁻¹' CutDigits.lowerCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=0} ∧
      h ⁻¹' CutDigits.upperCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=1} :=
  printed_cut_reduction a ha
example :
    ∃ h : ℕ → ℕ,Computable h ∧ ∀ a : Point,IsMiller a →
      h ⁻¹' CutDigits.lowerCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=0} ∧
      h ⁻¹' CutDigits.upperCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=1} :=
  uniform_cut_reduction
end CategoricalEssentialIncompleteness.V46.Miller.Cut.Checks
