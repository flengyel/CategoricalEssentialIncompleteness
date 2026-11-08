import CategoricalEssentialIncompleteness.V46MillerRealComputation
import CategoricalEssentialIncompleteness.V46MillerCutSeparatingProgram
import CategoricalEssentialIncompleteness.V46MillerCutDigits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The ordinary recursive cut reduction

The actual finite-box/series program is selected before the Miller sequence.
The only sequence hypothesis in the final theorem is the printed Miller
property. No numerical approximation or axiom-comparison premise remains.
-/
noncomputable section
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut
open OracleProgram

private def approximationIndex : ℕ := Classical.choose separatingReal_program

private theorem approximationIndex_spec (p : Bits) (e k : ℕ) :
    ∃ i : ℕ,i ∈ numberedEval approximationIndex p (Nat.pair e k) ∧
      |(Rationals.q i : ℝ)-separatingReal e (rho p)| < ((2:ℝ)^k)⁻¹ :=
  Classical.choose_spec separatingReal_program p e k

/-- A real in [1/4,3/4] is in the range of the Miller property. -/
def separatingPoint (e : ℕ) (z : Point) : Set.Icc (0:ℝ) 1 :=
  ⟨separatingReal e z,by
    have h := separatingReal_bounds e z
    constructor <;> linarith⟩

/-- Ordinary specialization of the single constructed approximation program. -/
def reduction (e : ℕ) : ℕ := specializationIndex approximationIndex e

theorem reduction_computable : Computable reduction :=
  specializedIndex_computable approximationIndex

theorem reduction_value (a : Point) (ha : IsMiller a) (e : ℕ) :
    a (reduction e)=separatingPoint e a := by
  change a (specializationIndex approximationIndex e)=separatingPoint e a
  apply miller_coordinate_of_approximation a ha approximationIndex separatingPoint ?_ e
  intro p x k
  exact approximationIndex_spec p x k

theorem reduction_lower (a : Point) (ha : IsMiller a) (e : ℕ) :
    reduction e ∈ CutDigits.lowerCut a ↔
      ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=0 := by
  change (a (reduction e) : ℝ)<1/2 ↔ _
  rw [reduction_value a ha e]
  change separatingReal e a<1/2 ↔ _
  have h := separatingReal_lt_half e a
  change separatingReal e a<1/2 ↔ ∃ m,m%2=0 ∧ m ∈ Unanimity.tau a e e at h
  simpa only [and_comm] using h

theorem reduction_upper (a : Point) (ha : IsMiller a) (e : ℕ) :
    reduction e ∈ CutDigits.upperCut a ↔
      ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=1 := by
  change 1/2<(a (reduction e) : ℝ) ↔ _
  rw [reduction_value a ha e]
  change 1/2<separatingReal e a ↔ _
  have h := separatingReal_gt_half e a
  change 1/2<separatingReal e a ↔ ∃ m,m%2=1 ∧ m ∈ Unanimity.tau a e e at h
  simpa only [and_comm] using h

/-- One ordinary recursive reduction works for every sequence having the
printed property for the fixed acceptable enumerations. -/
theorem uniform_cut_reduction :
    ∃ h : ℕ → ℕ,Computable h ∧ ∀ a : Point,IsMiller a →
      h ⁻¹' CutDigits.lowerCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=0} ∧
      h ⁻¹' CutDigits.upperCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=1} :=
  ⟨reduction,reduction_computable,fun a ha =>
    ⟨Set.ext (reduction_lower a ha),Set.ext (reduction_upper a ha)⟩⟩

/-- Lemma 8.3 at its printed hypotheses and both exact inverse-image equations. -/
theorem printed_cut_reduction (a : Point) (ha : IsMiller a) :
    ∃ h : ℕ → ℕ,Computable h ∧
      h ⁻¹' CutDigits.lowerCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=0} ∧
      h ⁻¹' CutDigits.upperCut a = {e | ∃ m,m ∈ Unanimity.tau a e e ∧ m%2=1} :=
  ⟨reduction,reduction_computable,Set.ext (reduction_lower a ha),Set.ext (reduction_upper a ha)⟩

end CategoricalEssentialIncompleteness.V46.Miller.Cut
