import CategoricalEssentialIncompleteness.V46MillerCutReduction
import CategoricalEssentialIncompleteness.V46MillerCutInseparabilityRelative
import CategoricalEssentialIncompleteness.V46MillerCutInseparabilitySplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The printed cut contrast and failure of Turing preservation

The reduction hypotheses of the reusable categorical arguments are
discharged by the concrete ordinary recursive construction of Lemma 8.3.
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut
attribute [instance 2000] Uniform.nativeRestriction

private theorem reduction_support0 (a : Point) (ha : IsMiller a) :
    reduction ⁻¹' CutDigits.lowerCut a = Uniform.support (CutInseparability.diagonal0 a) := by
  apply Set.ext
  intro e
  exact (reduction_lower a ha e).trans (CutInseparability.diagonal0_support a e).symm

private theorem reduction_support1 (a : Point) (ha : IsMiller a) :
    reduction ⁻¹' CutDigits.upperCut a = Uniform.support (CutInseparability.diagonal1 a) := by
  apply Set.ext
  intro e
  exact (reduction_upper a ha e).trans (CutInseparability.diagonal1_support a e).symm

/-- Corollary 8.4's internal inseparability for the actual cut idempotents. -/
theorem printed_cut_inseparability (a : Point) (ha : IsMiller a) :
    Inseparable (CutDigits.lowerIdem a) (CutDigits.upperIdem a) :=
  CutInseparability.cuts_inseparable_of_recursive_reduction a reduction reduction_computable
    (reduction_support0 a ha) (reduction_support1 a ha)

/-- For each fixed representation, its first coordinate digit decides an
actual separator. This statement does not identify those sets across p. -/
theorem fixed_representation_separator (a : Point) (p : Bits) (hp : p ∈ representations a) :
    CutDigits.lowerCut a ⊆ CutDigits.separator p ∧
      Disjoint (CutDigits.separator p) (CutDigits.upperCut a) ∧
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (fun n => Part.some (CutDigits.decision p n)) :=
  CutDigits.fixed_representation_separator a p hp

/-- The two conclusions of the printed corollary, retaining the full
all-representation source category and the fixed-p numerical contrast. -/
theorem printed_cut_contrast (a : Point) (ha : IsMiller a) :
    Inseparable (CutDigits.lowerIdem a) (CutDigits.upperIdem a) ∧
      ∀ p ∈ representations a,
        CutDigits.lowerCut a ⊆ CutDigits.separator p ∧
          Disjoint (CutDigits.separator p) (CutDigits.upperCut a) ∧
          Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
            (fun n => Part.some (CutDigits.decision p n)) :=
  ⟨printed_cut_inseparability a ha,fixed_representation_separator a⟩

/-- The faithful range interpretation into the FULL fixed-oracle category
fails to preserve this particular Turing morphism. The target has its own
separate universal oracle interpreter. -/
theorem mapped_tau_notTuring (a : Point) (ha : IsMiller a)
    (p : Bits) (hp : p ∈ representations a) :
    ¬RecursionCategory.IsTuringMorphism ((Uniform.J a p hp).toFunctor.map (Uniform.tau a)) :=
  CutInseparability.mapped_tau_notTuring_of_recursive_reduction a reduction reduction_computable
    (reduction_support0 a ha) (reduction_support1 a ha) p hp

end CategoricalEssentialIncompleteness.V46.Miller.Cut
