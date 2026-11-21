/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkEvaluator

/-! # Turing factorization with equality of all three partial component functions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory Encodable Denumerable
open Nat.Partrec (Code)
open FailureOfComposition.Kleene (eval)

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def program {X Y : Carrier} (f : X ⟶ Y) : Code :=
  Classical.choose (Code.exists_code.mp (Partrec.nat_iff.mp (EnumerableCarriers.val_partrec f)))

theorem eval_program {X Y : Carrier} (f : X ⟶ Y) : Code.eval (program f) = val f :=
  Classical.choose_spec (Code.exists_code.mp (Partrec.nat_iff.mp
    (EnumerableCarriers.val_partrec f)))

def specialize (c : Code) (y : ℕ) : ℕ := encode (Code.curry c y)

theorem specialize_computable (c : Code) : Computable (specialize c) :=
  Computable.encode.comp (Code.primrec₂_curry.to_comp.comp (.const c) .id)

theorem eval_specialize (c : Code) (y x : ℕ) :
    eval (specialize c y) x = Code.eval c (Nat.pair y x) := by
  simp only [eval, specialize, ofNat_encode, Code.eval_curry]

def parameter {X : Object} (f : product X V ⟶ V) : X ⟶ V :=
  coherentEncoding X (specialize_computable (program f.center))
    (specialize_computable (program f.left)) (specialize_computable (program f.right))

theorem parameter_total {X : Object} (f : product X V ⟶ V) : isTotal (parameter f) :=
  coherentEncoding_total X (specialize_computable (program f.center))
    (specialize_computable (program f.left)) (specialize_computable (program f.right))

theorem endpoint_parameterization {X : Carrier}
    (f : EnumerableCarriers.product X natCarrier ⟶ natCarrier) :
    EnumerableCarriers.partialProdMap (endpointEncoding (specialize (program f))
      (specialize_computable (program f))) (𝟙 natCarrier) ≫ endpointEvaluator = f := by
  apply EnumerableCarriers.val_injective
  apply PFun.ext
  intro n m
  simp only [EnumerableCarriers.mem_val_comp, EnumerableCarriers.mem_partialProdMap_iff,
    mem_endpointEncoding, EnumerableCarriers.val_id, mem_supportIdentity]
  constructor
  · rintro ⟨k, ⟨⟨_, hk1⟩, _, hk2⟩, hm⟩
    change m ∈ eval (Nat.unpair (Nat.unpair k).1).2 (Nat.unpair k).2 at hm
    rw [hk1, Nat.unpair_pair, hk2, eval_specialize, eval_program, Nat.pair_unpair] at hm
    exact hm
  · intro hm
    have hn := EnumerableCarriers.val_source f n m hm
    refine ⟨Nat.pair (Nat.pair 0 (specialize (program f) (Nat.unpair n).1))
      (Nat.unpair n).2, ⟨⟨hn.1, by simp⟩, Set.mem_univ _, by simp⟩, ?_⟩
    change m ∈ endpointEval _
    simpa only [endpointEval, Nat.unpair_pair, eval_specialize, eval_program,
      Nat.pair_unpair] using hm

theorem central_specialized {X : Object} (f : product X V ⟶ V) (y x a b : ℕ)
    (ha : a ∈ val X.leftMap y) (hb : b ∈ val X.rightMap y) :
    centerEval (Nat.pair (quadCode (0, specialize (program f.center) y,
      specialize (program f.left) a, specialize (program f.right) b)) x) =
        val f.center (Nat.pair y x) := by
  apply Part.ext
  intro m
  rw [mem_centerEval]
  have hc : centralEval (Nat.pair (quadCode (0, specialize (program f.center) y,
      specialize (program f.left) a, specialize (program f.right) b)) x) =
        val f.center (Nat.pair y x) := by
    simp only [centralEval, Nat.unpair_pair, Equiv.symm_apply_apply, eval_specialize, eval_program]
  have hl : leftEval (Nat.pair (quadCode (0, specialize (program f.center) y,
      specialize (program f.left) a, specialize (program f.right) b)) x) =
        val f.left (Nat.pair a (leftCoordinate x)) := by
    simp only [leftEval, Nat.unpair_pair, Equiv.symm_apply_apply, eval_specialize, eval_program]
  have hr : rightEval (Nat.pair (quadCode (0, specialize (program f.center) y,
      specialize (program f.left) a, specialize (program f.right) b)) x) =
        val f.right (Nat.pair b (rightCoordinate x)) := by
    simp only [rightEval, Nat.unpair_pair, Equiv.symm_apply_apply, eval_specialize, eval_program]
  rw [hc, hl, hr]
  constructor
  · exact And.left
  · intro hm
    refine ⟨hm, ?_, ?_⟩
    · apply f.natural_left (Nat.pair y x) m (Nat.pair a (leftCoordinate x))
        (leftCoordinate m) hm
      · exact (EnumerableCarriers.mem_partialProdMap_iff X.leftMap V.leftMap _ _).mpr
          (by simpa only [Nat.unpair_pair] using And.intro ha ((mem_V_left x _).mpr rfl))
      · exact (mem_V_left m _).mpr rfl
    · apply f.natural_right (Nat.pair y x) m (Nat.pair b (rightCoordinate x))
        (rightCoordinate m) hm
      · exact (EnumerableCarriers.mem_partialProdMap_iff X.rightMap V.rightMap _ _).mpr
          (by simpa only [Nat.unpair_pair] using And.intro hb ((mem_V_right x _).mpr rfl))
      · exact (mem_V_right m _).mpr rfl

theorem center_parameterization {X : Object} (f : product X V ⟶ V) :
    EnumerableCarriers.partialProdMap (parameter f).center (𝟙 natCarrier) ≫ centerEvaluator =
      f.center := by
  apply EnumerableCarriers.val_injective
  apply PFun.ext
  intro n m
  rw [EnumerableCarriers.mem_val_comp]
  constructor
  · rintro ⟨k, hk, hm⟩
    obtain ⟨hp, hi⟩ := (EnumerableCarriers.mem_partialProdMap_iff _ _ n k).mp hk
    obtain ⟨a, ha, b, hb, he⟩ := (mem_centerEncoding X
      (specialize (program f.center)) (specialize (program f.left))
      (specialize (program f.right)) _ _).mp hp
    obtain ⟨_, hx⟩ := (mem_supportIdentity natCarrier.support _ _).mp hi
    have hk : k=Nat.pair (quadCode (0, specialize (program f.center) (Nat.unpair n).1,
        specialize (program f.left) a, specialize (program f.right) b)) (Nat.unpair n).2 := by
      rw [he, ← hx, Nat.pair_unpair]
    change m ∈ centerEval k at hm
    rw [hk, central_specialized f _ _ a b ha hb, Nat.pair_unpair] at hm
    exact hm
  · intro hm
    have hs := EnumerableCarriers.val_source f.center n m hm
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.leftMap).mp X.left_total (Nat.unpair n).1 hs.1)
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.rightMap).mp X.right_total (Nat.unpair n).1 hs.1)
    let p := quadCode (0, specialize (program f.center) (Nat.unpair n).1,
      specialize (program f.left) a, specialize (program f.right) b)
    refine ⟨Nat.pair p (Nat.unpair n).2, ?_, ?_⟩
    · apply (EnumerableCarriers.mem_partialProdMap_iff _ _ _ _).mpr
      constructor
      · simp only [Nat.unpair_pair]
        exact (mem_centerEncoding X (specialize (program f.center))
            (specialize (program f.left)) (specialize (program f.right)) _ p).mpr
              ⟨a,ha,b,hb,rfl⟩
      · change (Nat.unpair (Nat.pair p (Nat.unpair n).2)).2 ∈
          supportIdentity natCarrier.support (Nat.unpair n).2
        simp only [Nat.unpair_pair]
        exact (mem_supportIdentity _ _ _).mpr ⟨Set.mem_univ _,rfl⟩
    · change m ∈ centerEval (Nat.pair p (Nat.unpair n).2)
      rw [show p=quadCode (0, specialize (program f.center) (Nat.unpair n).1,
        specialize (program f.left) a, specialize (program f.right) b) from rfl,
        central_specialized f _ _ a b ha hb, Nat.pair_unpair]
      exact hm

theorem tau_parameterization {X : Object} (f : product X V ⟶ V) :
    productMap (parameter f) (𝟙 V) ≫ tau = f :=
  Hom.ext (center_parameterization f) (endpoint_parameterization f.left)
    (endpoint_parameterization f.right)

/-- Theorem B.7, including simultaneous undefinedness in the central component. -/
theorem tau_isTuring : RecursionCategory.IsTuringMorphism tau := by
  intro X f
  refine ⟨parameter f, ?_, tau_parameterization f⟩
  change PCategoryStruct.rst (parameter f) = 𝟙 X
  rw [induced_restriction]
  exact parameter_total f

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
