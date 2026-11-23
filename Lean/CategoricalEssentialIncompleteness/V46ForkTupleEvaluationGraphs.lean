/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluation
public import CategoricalEssentialIncompleteness.V46ForkTupleFormulaAlgebraCoordinates

/-! # Tuple points of a monic partial span -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

open NumericalTuples (Point code)
open EnumerableCarriers (val)
open ForkDiagonalObstruction (tupleDiagram tupleSpace)

def Graph {X Y : TupleSpans} (f : X ⟶ Y) (x : Point X.obj) (y : Point Y.obj) : Prop :=
  code Y.obj.dimension y.val ∈ val (tupleCode.map f) (code X.obj.dimension x.val)

theorem inverse_graph {X Y : EnumerableCarriers.Total} (m : X ⟶ Y) [Mono m] (y x : ℕ) :
    x ∈ val (PartialSpans.inverse m) y ↔ y ∈ val m.hom x := by
  constructor
  · intro hx
    have hs := EnumerableCarriers.val_target _ _ _ hx
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp ((EnumerableCarriers.total_iff m.hom).mp m.property x hs)
    have hc := (EnumerableCarriers.mem_val_comp (PartialSpans.inverse m) m.hom y z).mpr ⟨x, hx, hz⟩
    rw [PartialSpans.inverse_hom] at hc
    exact ((EnumerableCarriers.mem_restrict _ _ _).mp hc).2 ▸ hz
  · intro hy
    have hid : x ∈ val (𝟙 X.obj) x := (mem_supportIdentity _ _ _).mpr
      ⟨EnumerableCarriers.val_source _ _ _ hy, rfl⟩
    rw [← PartialSpans.hom_inverse m] at hid
    obtain ⟨z, hz, hx⟩ := (EnumerableCarriers.mem_val_comp _ _ _ _).mp hid
    exact Part.mem_unique hz hy ▸ hx

/-- A pair of tuple points is in the graph precisely when one point of the apex
maps to the input and the output under the two legs. -/
theorem span_graph {X Y : TupleSpans} (s : PartialMaps.Raw X Y) (x : Point X.obj) (y : Point Y.obj) :
    Graph (PartialMaps.ofSpan s) x y ↔ ∃ z : Point s.apex, s.l.toFun z = x ∧ s.r.toFun z = y := by
  let : Mono (NumericalTuples.comparisonMap s.l) :=
    (inferInstance : Mono (NumericalTuples.comparison.map s.l))
  change _ ∈ val (PartialSpans.inverse (NumericalTuples.comparisonMap s.l) ≫
    (NumericalTuples.comparisonMap s.r).hom) _ ↔ _
  rw [EnumerableCarriers.mem_val_comp]
  simp only [inverse_graph, NumericalTuples.comparisonMap_graph]
  constructor
  · rintro ⟨n, ⟨z, hz, hx⟩, w, hw, hy⟩
    have ew : z = w := Subtype.ext (NumericalTuples.code_injective _ (hz.trans hw.symm))
    subst w
    exact ⟨z, Subtype.ext (NumericalTuples.code_injective _ hx),
      Subtype.ext (NumericalTuples.code_injective _ hy)⟩
  · rintro ⟨z, hx, hy⟩
    exact ⟨_, ⟨z, rfl, hx ▸ rfl⟩, z, rfl, hy ▸ rfl⟩

theorem total_graph {X Y : TupleSpans} (f : X.obj ⟶ Y.obj) (x : Point X.obj) (y : Point Y.obj) :
    Graph (PartialMaps.ofTotal f) x y ↔ f.toFun x = y := by
  rw [PartialMaps.ofTotal, span_graph]
  change (∃ z : Point X.obj, z = x ∧ f.toFun z = y) ↔ _
  simp

theorem codedSpaceEq (n : ℕ) (h : Function.Surjective (code n)) :
    NumericalTuples.codedObject (tupleSpace n) = (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) := by
  apply WideSubcategory.ext
  change (⟨_, _⟩ : EnumerableCarriers.Carrier) = ⟨Set.univ, _⟩
  congr 1
  apply Set.eq_univ_of_forall
  intro m
  obtain ⟨x, rfl⟩ := h m
  exact ⟨x, Set.mem_univ _, rfl⟩

theorem codedCenterEq : NumericalTuples.codedObject (tupleSpace 4) =
    (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) := codedSpaceEq 4 EffectiveFork.quadCode.surjective
theorem codedEndpointEq : NumericalTuples.codedObject (tupleSpace 2) =
    (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) := codedSpaceEq 2 Nat.pairEquiv.surjective

private theorem label_naturality (g : tupleSpace 4 ⟶ tupleSpace 2)
    (t : (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) ⟶ ⟨EffectiveFork.natCarrier⟩)
    (d : ℕ → ℕ) (ht : ∀ x, (EnumerableCarriers.totalFunction t x).val = d x.val)
    (hg : ∀ x, code 2 (g.toFun x).val = d (code 4 x.val)) :
    NumericalTuples.comparison.map g ≫ eqToHom codedEndpointEq = eqToHom codedCenterEq ≫ t := by
  apply ForkDerivation.Naturality.totalMap_ext
  intro x
  obtain ⟨z, rfl⟩ := (NumericalTuples.pointEquiv (tupleSpace 4)).surjective x
  apply Subtype.ext
  rw [ForkDerivation.Naturality.totalFunction_comp, ForkDerivation.Naturality.totalFunction_comp,
    ForkDerivation.Naturality.totalFunction_eqToHom, ht,
    ForkDerivation.Naturality.totalFunction_eqToHom]
  change (EnumerableCarriers.totalFunction (NumericalTuples.comparisonMap g) _).val = _
  rw [NumericalTuples.comparisonMap_function]
  exact hg z

def labelIso : forkCode.obj (⟨tupleDiagram⟩ : ForkSpans) ≅ EffectiveFork.V :=
  (PreservesRestriction.totalInclusion EffectiveFork.Object).mapIso (EffectiveFork.fromFunctor.mapIso
    (spanIsoMk (F := tupleDiagram ⋙ NumericalTuples.comparison)
      (G := EffectiveFork.totalFunctor.obj (⟨EffectiveFork.V⟩ : EffectiveFork.Total))
      (eqToIso codedCenterEq) (eqToIso codedEndpointEq) (eqToIso codedEndpointEq) (by
        apply label_naturality ForkDiagonalObstruction.leftTransition _ EffectiveFork.leftCoordinate
        · intro x
          exact (EffectiveFork.mem_V_left _ _).mp (EnumerableCarriers.totalFunction_mem
            ((EffectiveFork.totalFunctor.obj (⟨EffectiveFork.V⟩ : EffectiveFork.Total)).map WalkingSpan.Hom.fst) x)
        · rintro ⟨⟨k,z,a,b⟩, _⟩
          exact (EffectiveFork.left_quad k z a b).symm) (by
        apply label_naturality ForkDiagonalObstruction.rightTransition _ EffectiveFork.rightCoordinate
        · intro x
          exact (EffectiveFork.mem_V_right _ _).mp (EnumerableCarriers.totalFunction_mem
            ((EffectiveFork.totalFunctor.obj (⟨EffectiveFork.V⟩ : EffectiveFork.Total)).map WalkingSpan.Hom.snd) x)
        · rintro ⟨⟨k,z,a,b⟩, _⟩
          exact (EffectiveFork.right_quad k z a b).symm)))

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
