/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalPCategory
import Mathlib.Computability.PartrecCode

/-!
# A Turing morphism for the numerical category

The evaluator applies a coded partial recursive function to its numerical
argument. The parameter theorem gives a total numerical arrow assigning a
program to each parameter, with equality of the resulting partial maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Encodable Denumerable
open Nat.Partrec (Code)
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Universal partial recursive evaluation on a coded program and an input. -/
def turingEvaluator : product nat nat ⟶ nat where
  val n := Code.eval (ofNat Code (Nat.unpair n).1) (Nat.unpair n).2
  computable := Code.eval_part.comp
    ((Computable.ofNat Code).comp (Computable.fst.comp Computable.unpair))
    (Computable.snd.comp Computable.unpair)
  source := fun _ ↦ ⟨Set.mem_univ _, Set.mem_univ _⟩
  target := fun _ ↦ Set.mem_univ _

/-- A total numerical parameter map obtained by partial application of a program. -/
def codeParameter (V : Numerical) (c : Code) : totalObject V ⟶ totalObject nat :=
  totalFromFunction (fun n ↦ encode (Code.curry c n))
    (Computable.encode.comp (Code.primrec₂_curry.to_comp.comp (Computable.const c) Computable.id))
    (fun _ _ ↦ Set.mem_univ _)

@[simp] theorem mem_codeParameter (V : Numerical) (c : Code) (n m : ℕ) :
    m ∈ (codeParameter V c).hom.val n ↔ n ∈ V.carrier ∧ encode (Code.curry c n) = m := by
  change m ∈ (supportIdentity V.carrier n).bind
    (fun k ↦ Part.some (encode (Code.curry c k))) ↔ _
  simp [Part.mem_bind_iff, eq_comm]

/-- A code for a partial numerical map gives its factorization through the evaluator. -/
theorem turingEvaluator_parameterization (V : Numerical) (φ : product V nat ⟶ nat)
    (c : Code) (hc : Code.eval c = φ.val) :
    partialProdMap (codeParameter V c).hom (𝟙 nat) ≫ turingEvaluator = φ := by
  apply Hom.ext
  funext n
  apply Part.ext
  intro m
  simp only [comp_val, Part.mem_bind_iff, mem_partialProdMap_iff, mem_codeParameter,
    id_val, mem_supportIdentity]
  constructor
  · rintro ⟨k, ⟨⟨_, hk₁⟩, _, hk₂⟩, hm⟩
    change m ∈ Code.eval (ofNat Code (Nat.unpair k).1) (Nat.unpair k).2 at hm
    rw [← hk₁, hk₂, ofNat_encode, Code.eval_curry, hc, Nat.pair_unpair] at hm
    exact hm
  · intro hm
    have hn := φ.source hm
    refine ⟨Nat.pair (encode (Code.curry c (Nat.unpair n).1)) (Nat.unpair n).2,
      ⟨⟨hn.1, by simp⟩, Set.mem_univ _, by simp⟩, ?_⟩
    change m ∈ Code.eval (ofNat Code (Nat.unpair
      (Nat.pair (encode (Code.curry c (Nat.unpair n).1)) (Nat.unpair n).2)).1)
      (Nat.unpair (Nat.pair (encode (Code.curry c (Nat.unpair n).1)) (Nat.unpair n).2)).2
    simpa only [Nat.unpair_pair, ofNat_encode, Code.eval_curry, hc, Nat.pair_unpair] using hm

/-- The numerical evaluator has the Turing factorization property for every parameter object. -/
theorem turingEvaluator_isTuringMorphism : RecursionCategory.IsTuringMorphism turingEvaluator := by
  intro V φ
  obtain ⟨c, hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp φ.computable)
  refine ⟨(codeParameter V c).hom, ?_, turingEvaluator_parameterization V φ c hc⟩
  change PCategoryStruct.rst (codeParameter V c).hom = 𝟙 V
  rw [pcategory_rst_eq]
  exact (codeParameter V c).property

end Numerical
end CategoricalEssentialIncompleteness
