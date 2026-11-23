/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDiagonalObstruction

/-! # The four-dimensional centre and two-dimensional endpoints of the universal fork -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction

/-- The full numerical tuple space in dimension `n`. -/
def tupleSpace (n : ℕ) : NumericalTuples.Object := ⟨n, Set.univ, REPred.const True⟩

/-- The left transition sends `(k,z,a,b)` to `(k,a)`. -/
def leftTransition : tupleSpace 4 ⟶ tupleSpace 2 where
  toFun x := ⟨(x.val.1, x.val.2.2.1), Set.mem_univ _⟩
  represented := ⟨fun x => Part.some (x.1, x.2.2.1), Computable.pair Computable.fst
    (Computable.fst.comp (Computable.snd.comp Computable.snd)), fun _ => rfl⟩

/-- The right transition sends `(k,z,a,b)` to `(k,b)`. -/
def rightTransition : tupleSpace 4 ⟶ tupleSpace 2 where
  toFun x := ⟨(x.val.1, x.val.2.2.2), Set.mem_univ _⟩
  represented := ⟨fun x => Part.some (x.1, x.2.2.2), Computable.pair Computable.fst
    (Computable.snd.comp (Computable.snd.comp Computable.snd)), fun _ => rfl⟩

/-- The diagram `ℕ² ← ℕ⁴ → ℕ²` of Proposition B.10 in the numerical tuple category. -/
def tupleDiagram : NumericalForkPartialMaps.Diagram := span leftTransition rightTransition

/-- The diagonal of the displayed numerical tuple diagram has no Boolean classifier. -/
theorem no_decidableVariables_tuples : ¬ Nonempty (DecidableVariables tupleDiagram) := by
  rintro ⟨E⟩
  let e := NumericalTuples.forkEquivalence
  let _ : e.inverse.IsEquivalence := e.symm.isEquivalence_functor
  let X := e.inverse.obj tupleDiagram
  let T : DecidableVariables X := DiagramDecidableVariables.mapped e.inverse E _ (Iso.refl X)
  let x (z : ℕ) : NumericalTuples.Tuple 4 := ((0,z,0,0) : ℕ × ℕ × ℕ × ℕ)
  let u : NumericalTuples.Tuple 2 := ((0,0) : ℕ × ℕ)
  have h (z : ℕ) : NumericalTuples.code 2 u ∈ EnumerableCarriers.val X.obj.leftMap
      (NumericalTuples.code 4 (x z)) := by
    change _ ∈ EnumerableCarriers.val (NumericalTuples.comparisonMap leftTransition).hom _
    exact (NumericalTuples.comparisonMap_graph leftTransition _ _).mpr
      ⟨⟨x z, Set.mem_univ _⟩, rfl, rfl⟩
  have he := leftMap_injective_of_decidableVariables T (h 0) (h 1)
  exact Nat.zero_ne_one (congrArg (fun a : NumericalTuples.Tuple 4 => a.2.1)
    (NumericalTuples.code_injective 4 he))

/-- No morphism on the product of the literal tuple diagram with itself has
its diagonal as the pullback of the second Boolean injection. -/
theorem no_diagonal_pullback (d : tupleDiagram ⨯ tupleDiagram ⟶ Two NumericalForkPartialMaps.Diagram) :
    ¬ IsPullback (prod.lift (𝟙 tupleDiagram) (𝟙 tupleDiagram)) (terminal.from tupleDiagram)
      d (coprod.inr : ⊤_ NumericalForkPartialMaps.Diagram ⟶ Two NumericalForkPartialMaps.Diagram) :=
  fun h => no_decidableVariables_tuples ⟨⟨d, h⟩⟩

end CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction
