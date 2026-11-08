/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCutDistanceApproximation

/-! # One actual all-oracle rational program for each finite bad-set distance

The ordinary finite-word algorithm and its use bound are constructed in
DistanceApproximation. The finite-use compiler produces one index before
any oracle or numerical parameter; no realizer or output uniformity across
representations is assumed.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Encodable Denumerable
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance

private def encodedUse (n : ℕ) : ℕ :=
  let a := ofNat Params n
  use a.1.1 a.1.2 a.2.1 a.2.2

private def encodedAlgorithm (a : List ℕ × ℕ) : ℕ :=
  finiteIndex (normalizeWord a.1) (ofNat Params a.2)

private theorem encodedUse_computable : Computable encodedUse :=
  (use_primrec.to_comp.comp (Computable.ofNat Params)).of_eq (fun _ => rfl)

private theorem encodedAlgorithm_computable : Computable encodedAlgorithm :=
  (finiteIndex_primrec.to_comp.comp (normalizeWord_primrec.to_comp.comp Computable.fst)
    ((Computable.ofNat Params).comp Computable.snd)).of_eq (fun _ => rfl)

theorem finiteIndex_error (p : Bits) (N e m t k : ℕ) (hN : use e m t k≤N) :
    |(Rationals.q (finiteIndex (bitPrefix p N) ((e,m),(t,k))):ℝ)-delta e m t (rho p)|≤
      ((2:ℝ)^(k+2))⁻¹ := by
  rw [finiteIndex,Dyadic.outputIndex_value]
  exact approxCode_precision_error p N e m t k hN

/-- The required finite-distance program is CONSTRUCTED from its ordinary
algorithm. Its rational output can depend on the chosen binary expansion. -/
theorem exists_distance_program :
    ∃ d : ℕ,∀ p : Bits,∀ e m t k : ℕ,∃ i : ℕ,
      i ∈ OracleProgram.numberedEval d p (encode ((e,m),(t,k))) ∧
      |(Rationals.q i:ℝ)-delta e m t (rho p)|<((2:ℝ)^k)⁻¹ := by
  obtain ⟨d,hd⟩ := FiniteUse.exists_program encodedUse encodedAlgorithm
    encodedUse_computable encodedAlgorithm_computable
  refine ⟨d,?_⟩
  intro p e m t k
  let a : Params := ((e,m),(t,k))
  let N := use e m t k
  let i := finiteIndex (bitPrefix p N) a
  have hv : OracleProgram.numberedEval d p (encode a)=Part.some i := by
    simpa only [encodedUse,encodedAlgorithm,ofNat_encode,OracleProgram.numericalPrefix,normalizeWord_numericalPrefix] using
      hd p (encode a)
  have herr := finiteIndex_error p N e m t k (le_refl N)
  have hstrict : ((2:ℝ)^(k+2))⁻¹<((2:ℝ)^k)⁻¹ := by
    apply (inv_lt_inv₀ (by positivity) (by positivity)).mpr
    rw [pow_add]
    norm_num
  refine ⟨i,?_,herr.trans_lt hstrict⟩
  rw [hv]
  exact Part.mem_some _

end CategoricalEssentialIncompleteness.V46.Miller.Cut.Distance
