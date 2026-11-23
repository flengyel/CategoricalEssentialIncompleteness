/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkPropositionalFolds
public import CategoricalEssentialIncompleteness.V46ForkDiagonalObstructionTuples

/-! # The atom labels of the tuple formula diagram

The four coordinates at the centre and the two at either endpoint give the
atom diagram of §10. Coding these tuples commutes with both transitions.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra

open ForkDerivation ForkDerivation.Diagram ForkDiagonalObstruction

def tupleCodingIso (n : ℕ) (e : NumericalTuples.Tuple n ≃ ℕ)
    (he : Computable e) (hd : Computable e.symm) : tupleSpace n ≅ tupleSpace 1 where
  hom := ⟨fun x => ⟨e x.val, Set.mem_univ _⟩, fun v => Part.some (e v), he, fun _ => rfl⟩
  inv := ⟨fun x => ⟨e.symm x.val, Set.mem_univ _⟩,
    fun v => Part.some (e.symm v), hd, fun _ => rfl⟩
  hom_inv_id := NumericalTuples.Map.ext (funext fun x => Subtype.ext (e.symm_apply_apply x.val))
  inv_hom_id := NumericalTuples.Map.ext (funext fun x => Subtype.ext (e.apply_symm_apply x.val))

def centerCoding : tupleSpace 4 ≅ tupleSpace 1 :=
  tupleCodingIso 4 EffectiveFork.quadCode EffectiveFork.quadCode_computable
    EffectiveFork.quadDecode_computable

def endpointCoding : tupleSpace 2 ≅ tupleSpace 1 :=
  tupleCodingIso 2 Nat.pairEquiv (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)
    Computable.unpair

/-- Coding the labels at the centre and both endpoints gives an isomorphism of
the displayed tuple diagram with the atom diagram used by the numerical tree parser. -/
def labelCoding : tupleDiagram ≅ realization.obj variableObject :=
  spanIsoMk centerCoding endpointCoding endpointCoding (by
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    obtain ⟨⟨k, z, a, b⟩, hx⟩ := x
    let q := EffectiveFork.quadCode (k, z, a, b)
    let x : {n // n ∈ EffectiveFork.natCarrier.support} := ⟨q, Set.mem_univ _⟩
    let f : (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) ⟶
        ⟨EffectiveFork.natCarrier⟩ := ⟨EffectiveFork.V.leftMap, EffectiveFork.V.left_total⟩
    change Nat.pair k a = (EnumerableCarriers.totalFunction f x).val
    exact (EffectiveFork.left_quad k z a b).symm.trans
      ((EffectiveFork.mem_V_left _ _).mp (EnumerableCarriers.totalFunction_mem f x)).symm) (by
    apply NumericalTuples.Map.ext
    funext x
    apply Subtype.ext
    obtain ⟨⟨k, z, a, b⟩, hx⟩ := x
    let q := EffectiveFork.quadCode (k, z, a, b)
    let x : {n // n ∈ EffectiveFork.natCarrier.support} := ⟨q, Set.mem_univ _⟩
    let f : (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total) ⟶
        ⟨EffectiveFork.natCarrier⟩ := ⟨EffectiveFork.V.rightMap, EffectiveFork.V.right_total⟩
    change Nat.pair k b = (EnumerableCarriers.totalFunction f x).val
    exact (EffectiveFork.right_quad k z a b).symm.trans
      ((EffectiveFork.mem_V_right _ _).mp (EnumerableCarriers.totalFunction_mem f x)).symm)

theorem labelCoding_center (k z a b : ℕ) :
    ((labelCoding.hom.app .zero).toFun ⟨(k, z, a, b), Set.mem_univ _⟩).val =
      Nat.pair k (Nat.pair z (Nat.pair a b)) := rfl

theorem labelCoding_left (k a : ℕ) :
    ((labelCoding.hom.app .left).toFun ⟨(k, a), Set.mem_univ _⟩).val = Nat.pair k a := rfl

theorem labelCoding_right (k b : ℕ) :
    ((labelCoding.hom.app .right).toFun ⟨(k, b), Set.mem_univ _⟩).val = Nat.pair k b := rfl

end CategoricalEssentialIncompleteness.V46.ForkTupleFormulaAlgebra
