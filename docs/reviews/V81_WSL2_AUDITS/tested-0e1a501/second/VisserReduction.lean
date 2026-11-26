module

import CategoricalEssentialIncompleteness.NumericalInseparability
import Foundation.FirstOrder.LK.Basic
import Mathlib.Computability.Reduce

set_option autoImplicit false
open FFL FFL.FirstOrder CategoricalEssentialIncompleteness
namespace SecondReading.Tested

open FFL.Entailment in
theorem undecidable_extensions_of_reduction {L : FFL.FirstOrder.Language} [Encodable (Sentence L)]
    (T : Theory L) (P N : Set ℕ) (hs : Numerical.RecursivelyInseparable P N)
    (f : ℕ → Sentence L) (hf : Computable fun n => Encodable.encode (f n))
    (hp : ∀ n ∈ P, T ⊢ f n) (hn : ∀ n ∈ N, T ⊢ ∼(f n)) :
    ∀ U : Theory L, T ⊆ U → Entailment.Consistent U →
      ¬ ComputablePred (fun w : ℕ => ∃ φ : Sentence L, Encodable.encode φ = w ∧ U ⊢ φ) := by
  intro U inc hc dec
  let D : Set ℕ := {n | U ⊢ f n}
  have decidableD : ComputablePred (· ∈ D) := by
    apply ComputablePred.computable_of_manyOneReducible _ dec
    refine ⟨_,hf,?_⟩
    intro n
    constructor
    · exact fun h => ⟨f n,rfl,h⟩
    · rintro ⟨φ,e,h⟩
      change U ⊢ f n
      exact Encodable.encode_inj.mp e ▸ h
  have grows := Theory.Proof.weakerThan_of_le inc
  exact hs.2 ⟨D,decidableD,(fun n h => grows.wk (hp n h)),Set.disjoint_left.mpr
    (fun n hd he => (consistent_iff_unprovable_bot.mp hc)
      (neg_mdp (grows.wk (hn n he)) (show U ⊢ f n from hd)))⟩

end SecondReading.Tested

#check @SecondReading.Tested.undecidable_extensions_of_reduction
#print axioms SecondReading.Tested.undecidable_extensions_of_reduction
