/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuringParameters
public import CategoricalEssentialIncompleteness.V46ForkTupleTuringPoints

/-! # Tuple coordinates of the parameter of Theorem B.7 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open NumericalTuples (Point Tuple code)
open EnumerableCarriers (val)

/-- Specialization for parameters in any finite power, including the empty tuple. -/
theorem specialize_tuples (m n : ℕ) (G : Tuple m × Tuple n → Part ℕ) (hG : Partrec G) :
    ∃ s : Tuple m → ℕ, Computable s ∧ ∀ y x, eval (s y) (code n x) = G (y,x) := by
  let H : ℕ → Part ℕ := fun k => (NumericalTuples.decodeTuple m (Nat.unpair k).1).bind
    fun y => (NumericalTuples.decodeTuple n (Nat.unpair k).2).bind fun x => G (y,x)
  have hr : Partrec H := by
    have hm := (NumericalTuples.decodeTuple_partrec m).comp (Computable.fst.comp Computable.unpair)
    have hn := (NumericalTuples.decodeTuple_partrec n).comp (Computable.snd.comp Computable.unpair)
    exact hm.bind ((hn.comp Computable.fst).bind
      (hG.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd)).to₂).to₂
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hr)
  refine ⟨fun y => EffectiveFork.specialize c (code m y),
    (EffectiveFork.specialize_computable c).comp Computable.encode, ?_⟩
  intro y x
  rw [EffectiveFork.eval_specialize, hc]
  simp only [H, Nat.unpair_pair, NumericalTuples.decodeTuple_code, Part.bind_some]

def componentIndex {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) :
    WalkingSpan → ℕ → ℕ
  | .zero => EffectiveFork.specialize (EffectiveFork.program (forkProgram f).center)
  | .left => EffectiveFork.specialize (EffectiveFork.program (forkProgram f).left)
  | .right => EffectiveFork.specialize (EffectiveFork.program (forkProgram f).right)

theorem componentIndex_computable {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal)
    (j : WalkingSpan) : Computable (fun z : Tuple (Y.obj.obj j).dimension => componentIndex f j (code _ z)) := by
  rcases j with _ | (_ | _) <;> exact (EffectiveFork.specialize_computable _).comp Computable.encode

private theorem endpoint_encoding {Z : TupleSpans} (g : ℕ → ℕ) (hg : Computable g)
    (z : Point Z.obj) (q : Point endpoint.obj) :
    code 2 q.val ∈ val (EffectiveFork.endpointEncoding (X := tupleCode.obj Z) g hg ≫ endpointIso.inv)
        (code _ z.val) ↔ q.val = (0,g (code _ z.val)) := by
  rw [EnumerableCarriers.mem_val_comp]
  simp only [labelCode_inv, exists_eq_right', EffectiveFork.mem_endpointEncoding]
  have h := (NumericalTuples.code_mem_codedSupport Z.obj z.val).mpr z.property
  change _ ∈ NumericalTuples.codedSupport Z.obj ∧ _ = _ ↔ _
  rw [and_iff_right h]
  change code 2 q.val = code 2 (0,g (code _ z.val)) ↔ _
  exact (NumericalTuples.code_injective 2).eq_iff

theorem forkParameter_left {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal)
    (z : Point (Y.obj.obj .left)) (q : Point endpoint.obj) :
    Graph ((evaluation .left).map (forkParameter f)) z q ↔
      q.val = (0,componentIndex f .left (code _ z.val)) := by
  unfold Graph forkParameter
  rw [evaluation_value, forkCode.map_preimage]
  exact endpoint_encoding (Z := (evaluation .left).obj Y) _ (EffectiveFork.specialize_computable _) z q

theorem forkParameter_right {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal)
    (z : Point (Y.obj.obj .right)) (q : Point endpoint.obj) :
    Graph ((evaluation .right).map (forkParameter f)) z q ↔
      q.val = (0,componentIndex f .right (code _ z.val)) := by
  unfold Graph forkParameter
  rw [evaluation_value, forkCode.map_preimage]
  exact endpoint_encoding (Z := (evaluation .right).obj Y) _ (EffectiveFork.specialize_computable _) z q

private theorem transition_code {A B : NumericalTuples.Object} (g : A ⟶ B) (z : Point A) (n : ℕ) :
    n ∈ val (NumericalTuples.comparison.map g).hom (code _ z.val) ↔ n = code _ (g.toFun z).val := by
  rw [show NumericalTuples.comparison.map g = NumericalTuples.comparisonMap g from rfl,
    NumericalTuples.comparisonMap_graph]
  constructor
  · rintro ⟨w, hw, hn⟩
    have he : w = z := Subtype.ext (NumericalTuples.code_injective _ hw)
    exact he ▸ hn.symm
  · rintro rfl
    exact ⟨z, rfl, rfl⟩

theorem forkParameter_center {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal)
    (z : Point (Y.obj.obj .zero)) (q : Point (ForkDiagonalObstruction.tupleSpace 4)) :
    Graph ((evaluation .zero).map (forkParameter f)) z q ↔
      q.val = (0, componentIndex f .zero (code _ z.val),
        componentIndex f .left (code _ ((Y.obj.map WalkingSpan.Hom.fst).toFun z).val),
        componentIndex f .right (code _ ((Y.obj.map WalkingSpan.Hom.snd).toFun z).val)) := by
  unfold Graph forkParameter
  rw [evaluation_value, forkCode.map_preimage]
  change code 4 q.val ∈ val ((EffectiveFork.parameter (forkProgram f)).center ≫ centerCode.inv) (code _ z.val) ↔ _
  rw [EnumerableCarriers.mem_val_comp]
  have hi (a b : ℕ) : b ∈ val centerCode.inv a ↔ b = a :=
    (val_eqToHom codedCenterEq.symm a b).trans (and_iff_right (Set.mem_univ a))
  simp only [hi, exists_eq_right']
  change _ ∈ EffectiveFork.centerEncoding (forkCode.obj Y) _ _ _ _ ↔ _
  rw [EffectiveFork.mem_centerEncoding]
  have hl := transition_code (Y.obj.map WalkingSpan.Hom.fst) z
  have hr := transition_code (Y.obj.map WalkingSpan.Hom.snd) z
  change (∃ a, a ∈ val (NumericalTuples.comparison.map (Y.obj.map WalkingSpan.Hom.fst)).hom _ ∧
    ∃ b, b ∈ val (NumericalTuples.comparison.map (Y.obj.map WalkingSpan.Hom.snd)).hom _ ∧ _) ↔ _
  simp only [hl, hr, exists_eq_left]
  exact ⟨fun h => NumericalTuples.code_injective 4 h.symm, fun h => congrArg (code 4) h.symm⟩

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
