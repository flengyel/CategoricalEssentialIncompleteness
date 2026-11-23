/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnumeration
public import CategoricalEssentialIncompleteness.ClassicalSplitEquivalence
public import CategoricalEssentialIncompleteness.EnumerableLimits
public import CategoricalEssentialIncompleteness.V46MonicPartialSliceComparison

/-! # Infinite computably enumerable carriers (§5)

The least halting stage singles out one pair for each input in the carrier.
The increasing enumeration of these pairs projects to a computable injection
onto the carrier. Least search supplies its partial recursive inverse.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace CategoricalEssentialIncompleteness.V46.EnumerableCarrierEnumeration

/-- Codes of inputs paired with the first stage at which the program returns the input. -/
def firstStages (c : Code) : Set ℕ :=
  {p | let (x, s) := Nat.unpair p
       x ∈ evaln s c x ∧ x ∉ evaln (s - 1) c x}

theorem firstStages_computable (c : Code) : ComputablePred (· ∈ firstStages c) := by
  classical
  let input : ℕ → ℕ := fun p => p.unpair.1
  let stage : ℕ → ℕ := fun p => p.unpair.2
  have hx : Computable input := Computable.fst.comp Computable.unpair
  have hs : Computable stage := Computable.snd.comp Computable.unpair
  have test (s : ℕ → ℕ) (h : Computable s) :
      Computable fun p => decide (evaln (s p) c (input p) = some (input p)) :=
    Primrec.eq.decide.to_comp.comp
      (primrec_evaln.to_comp.comp ((h.pair (Computable.const c)).pair hx))
      (Primrec.option_some.to_comp.comp hx)
  exact (Primrec.and.to_comp.comp (test stage hs) (Primrec.not.to_comp.comp
    (test (fun p => stage p - 1) (Primrec.nat_sub.to_comp.comp hs (Computable.const 1))))).of_eq
      (fun p => by simp [firstStages, input, stage, Option.mem_def]) |>.computablePred

private theorem firstStage_le {c : Code} {x s k : ℕ}
    (h : x ∉ evaln (s - 1) c x) (hk : x ∈ evaln k c x) : s ≤ k := by
  by_contra! hks
  exact h (evaln_mono (by omega) hk)

/-- First projection is a bijection from the first halting stages onto the support. -/
theorem firstStages_bijOn {A : Set ℕ} {c : Code} (hc : eval c = supportIdentity A) :
    Set.BijOn (fun p : ℕ => p.unpair.1) (firstStages c) A := by
  constructor
  · intro p hp
    have h := evaln_sound hp.1
    rw [hc] at h
    exact ((mem_supportIdentity _ _ _).mp h).1
  constructor
  · intro p hp q hq hx
    change p.unpair.1 = q.unpair.1 at hx
    have hs : p.unpair.2 = q.unpair.2 := by
      apply le_antisymm
      · apply firstStage_le (x := p.unpair.1) hp.2
        rw [hx]
        exact hq.1
      · apply firstStage_le (x := q.unpair.1) hq.2
        rw [← hx]
        exact hp.1
    calc p = Nat.pair p.unpair.1 p.unpair.2 := (Nat.pair_unpair p).symm
         _ = Nat.pair q.unpair.1 q.unpair.2 := congrArg₂ Nat.pair hx hs
         _ = q := Nat.pair_unpair q
  · intro x hx
    have hx' : x ∈ eval c x := hc ▸ (mem_supportIdentity _ _ _).mpr ⟨hx, rfl⟩
    have stages := evaln_complete.mp hx'
    let s := Nat.find stages
    have hs : x ∈ evaln s c x := Nat.find_spec stages
    have hpos := evaln_bound hs
    have hprev : x ∉ evaln (s - 1) c x := Nat.find_min stages (by change s - 1 < s; omega)
    exact ⟨Nat.pair x s, by simpa [firstStages] using And.intro hs hprev, by simp⟩

/-- Every infinite c.e. set is the range of a total computable injection. -/
theorem exists_enumeration (A : Set ℕ) (hA : REPred (· ∈ A)) (h : A.Infinite) :
    ∃ e : ℕ → ℕ, Computable e ∧ Function.Injective e ∧ Set.range e = A := by
  obtain ⟨c, hc⟩ := exists_code.mp (Partrec.nat_iff.mp (supportIdentity_partrec A hA))
  have hb := firstStages_bijOn hc
  have hi : (firstStages c).Infinite :=
    (Set.infinite_image_iff hb.2.1).mp (hb.image_eq.symm ▸ h)
  let D : Numerical := ⟨firstStages c, firstStages_computable c, hi⟩
  refine ⟨fun n => (D.enumerate n).unpair.1,
    (Computable.fst.comp Computable.unpair).comp D.enumerate_computable,
    fun i j hij => D.enumerate_injective (hb.2.1 (D.enumerate_mem i) (D.enumerate_mem j) hij), ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    exact hb.1 (D.enumerate_mem n)
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := hb.2.2 hx
    obtain ⟨i, rfl⟩ := D.enumerate_surjective hp
    exact ⟨i, rfl⟩

/-- Least search for a preimage under the enumeration. -/
def inverseSearch (e : ℕ → ℕ) (x : ℕ) : Part ℕ :=
  Nat.rfind fun n => Part.some (decide (e n = x))

theorem inverseSearch_partrec {e : ℕ → ℕ} (he : Computable e) : Partrec (inverseSearch e) :=
  Partrec.rfind (Primrec.eq.decide.to_comp.comp (he.comp Computable.snd) Computable.fst).partrec

theorem mem_inverseSearch {e : ℕ → ℕ} (hi : Function.Injective e) (x n : ℕ) :
    n ∈ inverseSearch e x ↔ e n = x := by
  constructor
  · intro hn
    exact of_decide_eq_true (Part.mem_some_iff.mp (Nat.rfind_spec hn)).symm
  · rintro rfl
    apply Nat.mem_rfind.mpr
    refine ⟨by simp, fun {m} hmn => ?_⟩
    have hne : e m ≠ e n := fun he => hmn.ne (hi he)
    simp [hne]

/-- The inverse search has domain precisely the enumerated set. The composites
are the identity on the natural numbers and the partial identity on the set. -/
theorem inverseSearch_equations {A : Set ℕ} {e : ℕ → ℕ} (hi : Function.Injective e)
    (hr : Set.range e = A) :
    (∀ x, (inverseSearch e x).Dom ↔ x ∈ A) ∧
    (∀ n, (Part.some (e n)).bind (inverseSearch e) = Part.some n) ∧
    (∀ x, (inverseSearch e x).bind (fun n => Part.some (e n)) = supportIdentity A x) := by
  refine ⟨fun x => ?_, fun n => ?_, fun x => ?_⟩
  · simp only [Part.dom_iff_mem, mem_inverseSearch hi, ← hr, Set.mem_range]
  · simp only [Part.bind_some]
    exact Part.eq_some_iff.mpr ((mem_inverseSearch hi _ _).mpr rfl)
  · apply Part.ext
    intro y
    simp only [Part.mem_bind_iff, mem_inverseSearch hi, Part.mem_some_iff, mem_supportIdentity,
      ← hr, Set.mem_range]
    exact ⟨fun ⟨n, hn, hy⟩ => ⟨⟨n, hn⟩, hy.trans hn⟩,
      fun ⟨⟨n, hn⟩, hy⟩ => ⟨n, hn, hy.trans hn.symm⟩⟩

open LocalConnectedness ClassicalPrograms CategoryTheory.RestrictionCategory

/-- The enumeration and least search as inverse morphisms in the restriction splitting. -/
def splitIso (A : Set ℕ) (hA : REPred (· ∈ A)) (e : ℕ → ℕ) (he : Computable e)
    (hi : Function.Injective e) (hr : Set.range e = A) : parameterObject ≅ ceObject A hA where
  hom := totalFromU hA e he (fun n => hr ▸ ⟨n, rfl⟩)
  inv := {
    hom := omegaArrow (inverseSearch e) (inverseSearch_partrec he)
    source := (supportedArrow hA (REPred.const True : REPred (· ∈ (Set.univ : Set ℕ)))
      (inverseSearch e) (inverseSearch_partrec he)
      (fun x n hn => hr ▸ ⟨n, (mem_inverseSearch hi x n).mp hn⟩)
      (fun _ _ _ => Set.mem_univ _)).source
    target := Category.comp_id _ }
  hom_inv_id := by
    apply SplitObject.Hom.ext
    apply J.map_injective
    rw [SplitObject.comp_hom, J.map_comp]
    funext n
    exact (inverseSearch_equations hi hr).2.1 n
  inv_hom_id := by
    apply SplitObject.Hom.ext
    apply J.map_injective
    rw [SplitObject.comp_hom, J.map_comp]
    funext x
    exact (inverseSearch_equations hi hr).2.2 x

/-- Postcomposition with an isomorphism of bases induces an equivalence of
the categories of partial maps in their slices. -/
def partialSliceEquivalence {D : Type*} [Category D] [HasPullbacks D] {X Y : D} (i : X ≅ Y) :
    PartialMaps.Par (Over X) ≌ PartialMaps.Par (Over Y) := by
  let F := MonicPartialSliceComparison.postcompose i.hom
  letI : F.Full := MonicPartialSliceComparison.full i.hom
  letI : F.Faithful := MonicPartialSliceComparison.faithful i.hom
  letI : F.EssSurj := ⟨fun Z => by
    let P : PartialMaps.Par (Over X) := ⟨Over.mk (Z.obj.hom ≫ i.inv)⟩
    let j : (F.obj P).obj ≅ Z.obj := Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ Z.obj.hom = (Z.obj.hom ≫ i.inv) ≫ i.hom
      simp)
    exact ⟨P, ⟨(PartialMaps.toTotal (D := Over Y) ⋙ wideSubcategoryInclusion _).mapIso j⟩⟩⟩
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

abbrev TotalSplit := WideSubcategory (isTotal (C := SplitObject Rec))

scoped instance totalSplitPullbacks : HasPullbacks TotalSplit :=
  Adjunction.hasLimitsOfShape_of_equivalence
    EnumerableCarriers.inclusion_rst.totalEquivalence.inverse

/-- Both directions of an isomorphism in the splitting are total. -/
def totalSplitIso {X Y : SplitObject Rec} (i : X ≅ Y) :
    (⟨X⟩ : TotalSplit) ≅ ⟨Y⟩ where
  hom := ⟨i.hom, iso_total i⟩
  inv := ⟨i.inv, iso_total i.symm⟩
  hom_inv_id := WideSubcategory.hom_ext _ i.hom_inv_id
  inv_hom_id := WideSubcategory.hom_ext _ i.inv_hom_id

/-- The final example of §5, with the realizing partial functions and the
equivalence induced by postcomposition on the two partial-map slices. -/
theorem infinite_enumerable_carrier (A : Set ℕ) (hA : REPred (· ∈ A)) (h : A.Infinite) :
    ∃ (e : ℕ → ℕ) (r : ℕ → Part ℕ), Computable e ∧ Function.Injective e ∧ Set.range e = A ∧
      Partrec r ∧ (∀ x, (r x).Dom ↔ x ∈ A) ∧ (∀ n, (Part.some (e n)).bind r = Part.some n) ∧
      (∀ x, (r x).bind (fun n => Part.some (e n)) = supportIdentity A x) ∧
      ∃ i : parameterObject ≅ ceObject A hA, J.map i.hom.hom = (fun n => Part.some (e n)) ∧
        J.map i.inv.hom = r ∧ isTotal i.hom ∧ isTotal i.inv ∧
        ∃ E : PartialMaps.Par (Over (⟨parameterObject⟩ : TotalSplit)) ≌
              PartialMaps.Par (Over (⟨ceObject A hA⟩ : TotalSplit)),
          E.functor = MonicPartialSliceComparison.postcompose (totalSplitIso i).hom := by
  obtain ⟨e, he, hi, hr⟩ := exists_enumeration A hA h
  obtain ⟨hd, hleft, hright⟩ := inverseSearch_equations hi hr
  let i := splitIso A hA e he hi hr
  exact ⟨e, inverseSearch e, he, hi, hr, inverseSearch_partrec he, hd, hleft, hright,
    i, rfl, rfl, iso_total i, iso_total i.symm, partialSliceEquivalence (totalSplitIso i), rfl⟩

end CategoricalEssentialIncompleteness.V46.EnumerableCarrierEnumeration
