/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCutBoxDistance

/-! # The actual separating real for the diagonal parity regions

Each term is the constructed distance to the computed finite bad-set image.
The positivity comparisons are proved from the halting-stage comparison;
they are not fields of a supplied cozero presentation.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CategoricalEssentialIncompleteness.V46.Miller.Cut

def termOutput (i j : ℕ) : ℕ := 2*(Nat.unpair j).1+i
def termStage (j : ℕ) : ℕ := (Nat.unpair j).2

def deltaTerm (e : ℕ) (i : Fin 2) (j : ℕ) (z : Point) : ℝ :=
  Distance.delta e (termOutput i.val j) (termStage j) z

theorem deltaTerm_bounds (e : ℕ) (i : Fin 2) (j : ℕ) (z : Point) :
    0≤deltaTerm e i j z ∧ deltaTerm e i j z≤1 := Distance.delta_bounds _ _ _ _

theorem deltaTerm_continuous (e : ℕ) (i : Fin 2) (j : ℕ) :
    Continuous (deltaTerm e i j) := Distance.continuous_delta _ _ _

/-- Pairing enumerates all stages for all outputs of the specified parity. -/
theorem deltaTerm_pos_iff (e : ℕ) (i : Fin 2) (z : Point) :
    (∃ j,0<deltaTerm e i j z) ↔ z∈side e i.val := by
  constructor
  · rintro ⟨j,hj⟩
    have hstage : z∈openStage e (termOutput i.val j) (termStage j) :=
      (Distance.delta_pos_iff _ _ _ z).mp hj
    refine ⟨termOutput i.val j,?_,(openStage_iff_tau _ _ z).mp ⟨termStage j,hstage⟩⟩
    have hi := i.isLt
    unfold termOutput
    omega
  · rintro ⟨m,hm,hhalt⟩
    obtain ⟨t,ht⟩ := (openStage_iff_tau e m z).mpr hhalt
    have he : termOutput i.val (Nat.pair (m/2) t)=m := by
      simp only [termOutput,Nat.unpair_pair]
      omega
    refine ⟨Nat.pair (m/2) t,?_⟩
    change 0<Distance.delta e (termOutput i.val (Nat.pair (m/2) t))
      (termStage (Nat.pair (m/2) t)) z
    rw [he]
    simp only [termStage,Nat.unpair_pair]
    exact (Distance.delta_pos_iff e m t z).mpr (by
      simpa only [openStage,Set.mem_compl_iff] using ht)

def separatingReal (e : ℕ) (z : Point) : ℝ :=
  Series.separating (deltaTerm e 0) (deltaTerm e 1) z

theorem deltaSeries_pos_iff (e : ℕ) (i : Fin 2) (z : Point) :
    0<Series.value (deltaTerm e i) z ↔ z∈side e i.val :=
  (Series.value_pos_iff _ (deltaTerm_bounds e i) z).trans (deltaTerm_pos_iff e i z)

theorem deltaSeries_disjoint (e : ℕ) (z : Point) :
    ¬(0<Series.value (deltaTerm e 0) z ∧ 0<Series.value (deltaTerm e 1) z) := by
  rintro ⟨h0,h1⟩
  exact Set.disjoint_left.mp (side_disjoint e)
    ((deltaSeries_pos_iff e 0 z).mp h0) ((deltaSeries_pos_iff e 1 z).mp h1)

theorem separatingReal_bounds (e : ℕ) (z : Point) :
    1/4≤separatingReal e z ∧ separatingReal e z≤3/4 :=
  Series.separating_bounds _ _ (deltaTerm_bounds e 0) (deltaTerm_bounds e 1) z

theorem separatingReal_continuous (e : ℕ) : Continuous (separatingReal e) := by
  have h0 := Series.value_continuous (deltaTerm e 0) (deltaTerm_bounds e 0)
    (deltaTerm_continuous e 0)
  have h1 := Series.value_continuous (deltaTerm e 1) (deltaTerm_bounds e 1)
    (deltaTerm_continuous e 1)
  exact continuous_const.add ((h1.sub h0).div_const 4)

theorem separatingReal_lt_half (e : ℕ) (z : Point) :
    separatingReal e z<1/2 ↔ z∈side e 0 :=
  (Series.separating_lt_half _ _ (deltaTerm_bounds e 0) (deltaTerm_bounds e 1)
    (deltaSeries_disjoint e) z).trans (deltaTerm_pos_iff e 0 z)

theorem separatingReal_gt_half (e : ℕ) (z : Point) :
    1/2<separatingReal e z ↔ z∈side e 1 :=
  (Series.separating_gt_half _ _ (deltaTerm_bounds e 0) (deltaTerm_bounds e 1)
    (deltaSeries_disjoint e) z).trans (deltaTerm_pos_iff e 1 z)

theorem termOutput_primrec : Primrec₂ termOutput :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)))
    Primrec.fst

theorem termStage_primrec : Primrec termStage := Primrec.snd.comp Primrec.unpair

end CategoricalEssentialIncompleteness.V46.Miller.Cut
