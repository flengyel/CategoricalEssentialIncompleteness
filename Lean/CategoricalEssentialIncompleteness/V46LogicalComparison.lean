/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Comparison
import CategoricalEssentialIncompleteness.V46SplitExtension

/-! # Interpreted theories and the logical comparison -/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open PCategoryStruct (nearProd)

namespace CategoricalEssentialIncompleteness.LocalConnectedness

section Consistency

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C]
variable [HasZeroMorphisms C] [RestrictionZero C]

/-- Consistency descends to a smaller restriction idempotent. -/
theorem consistency_of_le {S : C} (ν : S ⟶ S) {t d : Idem S}
    (ht : t ≤ d) (hd : d ⊓ Idem.pull ν d = ⊥) :
    t ⊓ Idem.pull ν t = ⊥ :=
  le_antisymm (hd ▸ inf_le_inf ht (Idem.pull_mono ν ht)) bot_le

variable [Ranges C]

omit [HasZeroMorphisms C] [RestrictionZero C] in
/-- A factorization through a morphism received by `d` puts the range
below `d`. This applies to the partial identity of a validity subobject. -/
theorem range_le_of_factorization {P V S : C} (c : P ⟶ S)
    (k : P ⟶ V) (v : V ⟶ S) (d : Idem S)
    (hc : c = k ≫ v) (hv : v ≫ d.hom = v) : Ranges.range c ≤ d := by
  apply Ranges.least
  rw [hc, Category.assoc, hv]

theorem consistency_of_sound_factorization {P V S : C}
    (c : P ⟶ S) (k : P ⟶ V) (v : V ⟶ S) (d : Idem S)
    (hc : c = k ≫ v) (hv : v ≫ d.hom = v) (ν : S ⟶ S)
    (hd : d ⊓ Idem.pull ν d = ⊥) :
    Ranges.range c ⊓ Idem.pull ν (Ranges.range c) = ⊥ :=
  consistency_of_le ν (range_le_of_factorization c k v d hc hv) hd

omit [HasZeroMorphisms C] [RestrictionZero C] in
/-- A total inclusion splitting the conclusion range factors totally
through every total restriction monomorphism receiving the conclusions. -/
theorem theory_inclusion_factors {P T V S : C}
    (c : P ⟶ S) (m : T ⟶ S) (r : S ⟶ T) (hm : isTotal m)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = (Ranges.range c).hom)
    (k : P ⟶ V) (v : V ⟶ S) (q : S ⟶ V) (hv : isTotal v)
    (hvq : v ≫ q = 𝟙 V) (hqv : q ≫ v = rst q) (hc : c = k ≫ v) :
    ∃ w : T ⟶ V, isTotal w ∧ w ≫ v = m := by
  have hvd : v ≫ (Idem.ofRestrict q).hom = v := by
    change v ≫ rst q = v
    rw [← hqv, ← Category.assoc, hvq, Category.id_comp]
  have ht := range_le_of_factorization c k v (Idem.ofRestrict q) hc hvd
  have hmt : m ≫ (Ranges.range c).hom = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hmd : m ≫ (Idem.ofRestrict q).hom = m := by
    calc
      _ = (m ≫ (Ranges.range c).hom) ≫ (Idem.ofRestrict q).hom := by rw [hmt]
      _ = m := by rw [Category.assoc, ht, hmt]
  have hw : (m ≫ q) ≫ v = m := by
    rw [Category.assoc, hqv]
    exact hmd
  refine ⟨m ≫ q, ?_, hw⟩
  change rst (m ≫ q) = 𝟙 T
  rw [← rst_comp_of_isTotal (m ≫ q) hv, hw]
  exact hm

end Consistency

section Interpretation

variable {C : Type u₁} {A : Type u₂} [Category.{v₁} C] [Category.{v₂} A]
variable [RestrictionCategory C] [RestrictionCategory A] [Ranges C] [Ranges A]
variable [HasZeroMorphisms C] [HasZeroMorphisms A]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A]

/-- The range and splitting equations in Proposition 4.1, for any range
functor interpreting the category containing the sentence theory. -/
theorem interpreted_theory_equations (G : RangeFunctor C A) {P T S : C}
    (c : P ⟶ S) (m : T ⟶ S) (r : S ⟶ T) (t : Idem S)
    (ht : t = Ranges.range c) (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = t.hom) :
    G.mapIdem t = Ranges.range (G.toFunctor.map c) ∧
      G.toFunctor.map r ≫ G.toFunctor.map m = (G.mapIdem t).hom ∧
      G.toFunctor.map m ≫ G.toFunctor.map r = 𝟙 (G.toFunctor.obj T) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Idem.ext
    rw [ht]
    exact G.map_range c
  · change _ = G.toFunctor.map t.hom
    rw [← G.toFunctor.map_comp, hrm]
  · rw [← G.toFunctor.map_comp, hmr, G.toFunctor.map_id]

variable [RestrictionZero C] [RestrictionZero A] [RestrictionCoproducts C]
variable [RestrictionCoproducts A]
variable [BinaryJoins C] [BinaryJoins A]

omit [RestrictionZero C] [RestrictionZero A]
  [RestrictionCoproducts C] [RestrictionCoproducts A] in
/-- Noncoverage of an interpreted theory implies source noncoverage. -/
theorem source_noncoverage_of_interpretation (G : RangeFunctor C A)
    {S : C} (t : Idem S) (ν : S ⟶ S)
    (h : G.mapIdem t ⊔ Idem.pull (G.toFunctor.map ν) (G.mapIdem t) ≠ ⊤) :
    t ⊔ Idem.pull ν t ≠ ⊤ := by
  intro hc
  apply h
  rw [← G.map_pull, ← G.map_sup, hc, G.map_top]

end Interpretation

section Comparison

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R]
variable [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A] [BinaryJoins A] [TotalJoinInverse A]

/-- The target conclusion of Theorem 4.2 for the interpreted sentence
object, total substitution and total negation. -/
theorem logical_comparison_target (F : RangeFunctor R A) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    {S : A} (θ : F.toFunctor.obj U ⟶ S) (hθ : isTotal θ)
    (ν : S ⟶ S) (t : Idem S) (ht : t ⊓ Idem.pull ν t = ⊥)
    (ha0 : F.mapIdem (diagonal0 τ b) ≤ Idem.pull θ t)
    (ha1 : F.mapIdem (diagonal1 τ b) ≤ Idem.pull θ (Idem.pull ν t))
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (hs0 : Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      Idem.pull θ (Idem.pull ν t))
    (hs1 : Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      Idem.pull θ t)
    (ℓ : U ⟶ coprod U U)
    (hℓ : F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom) :
    ∃ g : U ⟶ U, isTotal g ∧
      Idem.pull (F.toFunctor.map g ≫ θ) t = ⊥ ∧
      Idem.pull (F.toFunctor.map g ≫ θ) (Idem.pull ν t) = ⊥ ∧
      t ⊔ Idem.pull ν t ≠ ⊤ := by
  have hd : Idem.pull θ t ⊓ Idem.pull θ (Idem.pull ν t) = ⊥ := by
    rw [← Idem.pull_inf, ht, Idem.pull_bot]
  obtain ⟨g, hg, hP, hN⟩ := comparison_zero_inverse_images F τ hτ b
    (Idem.pull θ t) (Idem.pull θ (Idem.pull ν t)) hd ha0 ha1 s hs0 hs1 ℓ hℓ
  have hgt : isTotal (F.toFunctor.map g ≫ θ) := isTotal_comp (F.map_total g hg) hθ
  have hp : Idem.pull (F.toFunctor.map g ≫ θ) t = ⊥ := by
    rw [Idem.pull_comp]; exact hP
  have hn : Idem.pull (F.toFunctor.map g ≫ θ) (Idem.pull ν t) = ⊥ := by
    rw [Idem.pull_comp]; exact hN
  refine ⟨g, hg, hp, hn, ?_⟩
  intro hc
  have he := TotalJoinInverse.pull_sup (F.toFunctor.map g ≫ θ) hgt t (Idem.pull ν t)
  rw [hc, Idem.pull_top_of_total _ hgt, hp, hn, sup_idem] at he
  apply hU
  rw [F.toFunctor.map_id]
  exact congrArg Idem.hom he

end Comparison

section SplitComparison

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R]
variable [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A]
variable [Ranges R] [Ranges A] [BinaryJoins R] [BinaryJoins A] [TotalJoinInverse A]

/-- Theorem 4.2 for the constructed extension by chosen splittings.
The canonical inclusion isomorphism identifies the interpreted source
object with `F U`; identity splittings make this identification the identity. -/
theorem logical_comparison (F : RangeFunctor R A)
    (splittings : ∀ X : SplitObject R, V46.TargetSplitting F X) {U : R}
    (τ : nearProd U U ⟶ U) (hτ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (hU : F.toFunctor.map (𝟙 U) ≠ 0)
    {S : SplitObject R} (θ : (splittingInclusion (C := R)).obj U ⟶ S)
    (hθ : isTotal θ) (ν : S ⟶ S) (tA : Idem S)
    (ht : (V46.chosenSplitRangeFunctor F splittings).mapIdem tA ⊓
      Idem.pull ((V46.chosenSplitRangeFunctor F splittings).toFunctor.map ν)
        ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA) = ⊥)
    (ha0 : F.mapIdem (diagonal0 τ b) ≤
      Idem.pull ((V46.chosenSplitExtensionInclusionIso F splittings).inv.app U ≫
        (V46.chosenSplitExtension F splittings).map θ)
        ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA))
    (ha1 : F.mapIdem (diagonal1 τ b) ≤
      Idem.pull ((V46.chosenSplitExtensionInclusionIso F splittings).inv.app U ≫
        (V46.chosenSplitExtension F splittings).map θ)
        (Idem.pull ((V46.chosenSplitExtension F splittings).map ν)
          ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA)))
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (hs0 : Idem.pull s (summand0 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      Idem.pull ((V46.chosenSplitExtensionInclusionIso F splittings).inv.app U ≫
        (V46.chosenSplitExtension F splittings).map θ)
        (Idem.pull ((V46.chosenSplitExtension F splittings).map ν)
          ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA)))
    (hs1 : Idem.pull s (summand1 (F.toFunctor.obj U) (F.toFunctor.obj U)) =
      Idem.pull ((V46.chosenSplitExtensionInclusionIso F splittings).inv.app U ≫
        (V46.chosenSplitExtension F splittings).map θ)
        ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA))
    (ℓ : U ⟶ coprod U U)
    (hℓ : F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom) :
    ∃ g : U ⟶ U, isTotal g ∧
      Idem.pull ((V46.chosenSplitExtension F splittings).map
        ((splittingInclusion (C := R)).map g ≫ θ))
        ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA) = ⊥ ∧
      Idem.pull ((V46.chosenSplitExtension F splittings).map
        ((splittingInclusion (C := R)).map g ≫ θ))
        (Idem.pull ((V46.chosenSplitExtension F splittings).map ν)
          ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA)) = ⊥ ∧
      (V46.chosenSplitRangeFunctor F splittings).mapIdem tA ⊔
        Idem.pull ((V46.chosenSplitExtension F splittings).map ν)
          ((V46.chosenSplitRangeFunctor F splittings).mapIdem tA) ≠ ⊤ ∧
      tA ⊔ Idem.pull ν tA ≠ ⊤ := by
  let G := V46.chosenSplitRangeFunctor F splittings
  let E := G.toFunctor
  let I := splittingInclusion (C := R)
  let σ : I ⋙ E ≅ F.toFunctor := V46.chosenSplitExtensionInclusionIso F splittings
  let θ' := σ.inv.app U ≫ E.map θ
  have hθ' : isTotal θ' := isTotal_comp (iso_total (σ.app U).symm) (G.map_total θ hθ)
  obtain ⟨g, hg, hp, hn, hnc⟩ := logical_comparison_target F τ hτ b hU
    θ' hθ' (E.map ν) (G.mapIdem tA) ht ha0 ha1 s hs0 hs1 ℓ hℓ
  have hmap : E.map (I.map g ≫ θ) = σ.hom.app U ≫ (F.toFunctor.map g ≫ θ') := by
    have hnatur := σ.hom.naturality g
    change E.map (I.map g) ≫ σ.hom.app U = σ.hom.app U ≫ F.toFunctor.map g at hnatur
    have hid : σ.hom.app U ≫ σ.inv.app U = 𝟙 _ := (σ.app U).hom_inv_id
    change E.map (I.map g ≫ θ) =
      σ.hom.app U ≫ (F.toFunctor.map g ≫ (σ.inv.app U ≫ E.map θ))
    rw [E.map_comp]
    calc
      E.map (I.map g) ≫ E.map θ =
          (E.map (I.map g) ≫ σ.hom.app U) ≫ (σ.inv.app U ≫ E.map θ) := by
        rw [Category.assoc, ← Category.assoc (σ.hom.app U), hid, Category.id_comp]
      _ = (σ.hom.app U ≫ F.toFunctor.map g) ≫ (σ.inv.app U ≫ E.map θ) := by
        rw [hnatur]
      _ = _ := Category.assoc _ _ _
  refine ⟨g, hg, ?_, ?_, hnc, source_noncoverage_of_interpretation G tA ν hnc⟩
  · change Idem.pull (E.map (I.map g ≫ θ)) (G.mapIdem tA) = ⊥
    rw [hmap, Idem.pull_comp, hp, Idem.pull_bot]
  · change Idem.pull (E.map (I.map g ≫ θ)) (Idem.pull (E.map ν) (G.mapIdem tA)) = ⊥
    rw [hmap, Idem.pull_comp, hn, Idem.pull_bot]

end SplitComparison

end CategoricalEssentialIncompleteness.LocalConnectedness
