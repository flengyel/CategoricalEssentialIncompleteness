/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.PCat

/-!
# Ranges, `rP`-categories, sections

Appendix A, subsection "Ranges and sections".

A domain `r` *receives* `f` when `f r = f`, and is *the* range of `f` when in
addition `β f = β' f` implies `β r = β' r` for all parallel `β, β'` out of the
target. That second clause determines `r`, so `IsRange` is a predicate and the
range operation is recovered from it by `HasRanges.ran_eq`.

Two departures from the appendix, both weakenings of its hypotheses.

* `ran 1 = 1` is stated there for `rP`-categories. Uniqueness of ranges proves
  it from the range axioms alone; `IsRP` is not needed. See `HasRanges.ran_id`.
* `rst σ = ran f` for a section `σ` of `f` is stated there as a consequence of
  the section equations. It is really the statement that `rst σ` *is* a range of
  `f`, which holds with no `HasRanges` hypothesis at all; the identification
  with `ran f` then follows by uniqueness. See `IsSection.isRange`.

The last section defines total range lifting and derives it from a section, and
hence from the axiom of choice. Appendix B uses that derivation.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-! ### Ranges -/

/-- `r` is a range of `f`: it is a domain, it receives `f`, and it is the least
such in the sense that any two morphisms agreeing after `f` agree after `r`. -/
structure IsRange {X Y : C} (r : Y ⟶ Y) (f : X ⟶ Y) : Prop where
  /-- `r` is a restriction idempotent. -/
  isDomain : rst r = r
  /-- `r` receives `f`: `f r = f`. -/
  receives : f ≫ r = f
  /-- `β f = β' f` implies `β r = β' r`. -/
  uniq : ∀ {W : C} (β β' : Y ⟶ W), f ≫ β = f ≫ β' → r ≫ β = r ≫ β'

/-- A morphism has at most one range. -/
theorem IsRange.unique {X Y : C} {r r' : Y ⟶ Y} {f : X ⟶ Y}
    (h : IsRange r f) (h' : IsRange r' f) : r = r' := by
  have e1 : r ≫ r' = r := by
    have := h.uniq r' (𝟙 Y) (by rw [h'.receives, Category.comp_id])
    rwa [Category.comp_id] at this
  have e2 : r' ≫ r = r' := by
    have := h'.uniq r (𝟙 Y) (by rw [h.receives, Category.comp_id])
    rwa [Category.comp_id] at this
  have comm : r ≫ r' = r' ≫ r := by
    have := PCategory.rst_comm' r r'
    rwa [h.isDomain, h'.isDomain] at this
  calc r = r ≫ r' := e1.symm
    _ = r' ≫ r := comm
    _ = r' := e2

/-- A `P`-category has ranges if every morphism has one. -/
class HasRanges (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] where
  ran : {X Y : C} → (X ⟶ Y) → (Y ⟶ Y)
  isRange : ∀ {X Y : C} (f : X ⟶ Y), IsRange (ran f) f

namespace HasRanges

variable [HasRanges C]

/-- Anything satisfying the range axioms for `f` is `ran f`. -/
lemma ran_eq {X Y : C} {r : Y ⟶ Y} {f : X ⟶ Y} (h : IsRange r f) : ran f = r :=
  (isRange f).unique h

@[simp] lemma rst_ran {X Y : C} (f : X ⟶ Y) : rst (ran f) = ran f :=
  (isRange f).isDomain

@[simp] lemma comp_ran {X Y : C} (f : X ⟶ Y) : f ≫ ran f = f :=
  (isRange f).receives

lemma ran_uniq {X Y W : C} (f : X ⟶ Y) (β β' : Y ⟶ W) (h : f ≫ β = f ≫ β') :
    ran f ≫ β = ran f ≫ β' :=
  (isRange f).uniq β β' h

/-- Minimality: any domain receiving `f` is above `ran f`. Used wherever the
manuscript says "the defining minimality of the range". -/
lemma ran_le_of_receives {X Y : C} (f : X ⟶ Y) {d : Y ⟶ Y} (hd : f ≫ d = f) :
    ran f ≫ d = ran f := by
  have h := ran_uniq f d (𝟙 Y) (by rw [hd, Category.comp_id])
  rwa [Category.comp_id] at h

/-- If a domain is above `ran f`, then it receives `f`. Converse of
`ran_le_of_receives`. -/
lemma comp_of_ran_le {X Y : C} (f : X ⟶ Y) {d : Y ⟶ Y} (h : ran f ≫ d = ran f) :
    f ≫ d = f := by
  calc f ≫ d = (f ≫ ran f) ≫ d := by rw [comp_ran]
    _ = f ≫ ran f ≫ d := Category.assoc _ _ _
    _ = f ≫ ran f := by rw [h]
    _ = f := comp_ran f

/-- `ran (hf) ≤ ran f`: a range absorbs precomposition. This is the
manuscript's elementary range calculus. -/
lemma ran_comp_le {W X Y : C} (h : W ⟶ X) (f : X ⟶ Y) :
    ran (h ≫ f) ≫ ran f = ran (h ≫ f) :=
  ran_le_of_receives _ (by rw [Category.assoc, comp_ran])

/-- `ran (δf) = ran f` whenever `δ` has a section. Stated for a split
epimorphism with the section given explicitly rather than for an isomorphism:
only `σδ = 1` is used, and `inv` would bring in `Classical.choice`, since
Mathlib defines it by `Classical.choose` from the `IsIso` existential. -/
lemma ran_comp_of_section {P Q R : C} (δ : P ⟶ Q) (σ : Q ⟶ P)
    (hσ : σ ≫ δ = 𝟙 Q) (f : Q ⟶ R) : ran (δ ≫ f) = ran f := by
  have h1 : ran (δ ≫ f) ≫ ran f = ran (δ ≫ f) := ran_comp_le δ f
  have hh : σ ≫ δ ≫ f = f := by rw [← Category.assoc, hσ, Category.id_comp]
  have h2 : ran f ≫ ran (δ ≫ f) = ran f := by
    have hx := ran_comp_le σ (δ ≫ f)
    rwa [hh] at hx
  have hcomm : ran (δ ≫ f) ≫ ran f = ran f ≫ ran (δ ≫ f) := by
    have hx := PCategory.rst_comm' (ran (δ ≫ f)) (ran f)
    rwa [rst_ran, rst_ran] at hx
  rw [← h1, hcomm, h2]

/-- `ran 1 = 1`. Appendix A states this for `rP`-categories; the range axioms
alone suffice. -/
@[simp] lemma ran_id (X : C) : ran (𝟙 X) = 𝟙 X :=
  ran_eq ⟨PCategory.rst_id X, Category.comp_id _, fun _ _ h => h⟩

end HasRanges

/-! ### `rP`-categories -/

/-- Heller's `rP`-category: ranges compatible with the near product. -/
class IsRP (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] : Prop where
  ran_nearProd_map : ∀ {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z),
    HasRanges.ran (nearProd_map f g)
      = nearProd_map (HasRanges.ran f) (HasRanges.ran g)

/-- Appendix A: if `b = ran o`, then `ran (o ⊠ 1) = b ⊠ 1`, and Lemma A.3
identifies that domain with `rst (b p₀)`. -/
lemma ran_nearProd_id [HasRanges C] [IsRP C] {T A I : C} (o : T ⟶ A) :
    HasRanges.ran (nearProd_map o (𝟙 I))
      = rst (p0 A I ≫ HasRanges.ran o) := by
  rw [IsRP.ran_nearProd_map, HasRanges.ran_id,
    PCategory.nearProd_domain_left _ (HasRanges.rst_ran o)]

/-! ### Sections and the axiom of choice -/

/-- A section of `f`: `f σ = rst σ` and `f σ f = f`. -/
structure IsSection {X Y : C} (f : X ⟶ Y) (σ : Y ⟶ X) : Prop where
  /-- `f σ = rst σ`. -/
  comp_eq_rst : σ ≫ f = rst σ
  /-- `f σ f = f`. -/
  comp_self : f ≫ σ ≫ f = f

/-- The restriction of a section of `f` is a range of `f`. No `HasRanges`
hypothesis is needed. -/
theorem IsSection.isRange {X Y : C} {f : X ⟶ Y} {σ : Y ⟶ X}
    (h : IsSection f σ) : IsRange (rst σ) f where
  isDomain := PCategory.rst_rst σ
  receives := by rw [← h.comp_eq_rst]; exact h.comp_self
  uniq _ _ hb := by rw [← h.comp_eq_rst, Category.assoc, Category.assoc, hb]

/-- Appendix A: `rst σ_f = ran f`. -/
theorem IsSection.rst_eq_ran [HasRanges C] {X Y : C} {f : X ⟶ Y} {σ : Y ⟶ X}
    (h : IsSection f σ) : rst σ = HasRanges.ran f :=
  (HasRanges.ran_eq h.isRange).symm

/-- A `P`-category satisfies the axiom of choice if every morphism has a
section. -/
class HasChoice (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] : Prop where
  exists_isSection : ∀ {X Y : C} (f : X ⟶ Y), ∃ σ : Y ⟶ X, IsSection f σ

/-- Choice supplies ranges, since the restriction of a section is one. -/
theorem exists_isRange_of_hasChoice [HasChoice C] {X Y : C} (f : X ⟶ Y) :
    ∃ r : Y ⟶ Y, IsRange r f := by
  obtain ⟨σ, hσ⟩ := HasChoice.exists_isSection f
  exact ⟨rst σ, hσ.isRange⟩

/-! ### Partial monomorphisms and the weak axiom of choice

Heller p. 1261, Di Paola--Heller Def. 6.2, Rosolini 2.5.10. A partial
monomorphism need not have a section under the axiom of choice only in the
trivial sense that choice gives every morphism one; the point of the weak axiom
is that it asks for sections exactly where they are unique. -/

/-- `f` is a partial monomorphism when `fθ = fθ'` implies `(rst f)θ = (rst f)θ'`. -/
def IsPartialMono {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {W : C} (θ θ' : W ⟶ X), θ ≫ f = θ' ≫ f → θ ≫ rst f = θ' ≫ rst f

/-- A `P`-category satisfies the weak axiom of choice when every partial
monomorphism has a section. -/
class HasWeakChoice (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] : Prop where
  exists_isSection : ∀ {X Y : C} (f : X ⟶ Y), IsPartialMono f →
    ∃ σ : Y ⟶ X, IsSection f σ

/-- Choice implies weak choice. -/
theorem hasWeakChoice_of_hasChoice [HasChoice C] : HasWeakChoice C :=
  ⟨fun f _ => HasChoice.exists_isSection f⟩

/-! ### Total range lifting

`f` has total range lifting when every total morphism received by `ran f`
factors through `f` by a total morphism. This is clause (1) of Lemma A.4,
quantified over `q`; `Dom.exists_total_lift_iff_exists_section` states the
equivalence with a section of the pullback projection in `Dom C`, whereas the
lemma below produces the lift directly from a section of `f` in `C`. -/

/-- Every total morphism received by `ran f` lifts along `f` to a total
morphism. -/
def HasTotalRangeLifting [HasRanges C] {X Y : C} (f : X ⟶ Y) : Prop :=
  ∀ {Z : C} (q : Z ⟶ Y), rst q = 𝟙 Z → q ≫ HasRanges.ran f = q →
    ∃ p : Z ⟶ X, rst p = 𝟙 Z ∧ p ≫ f = q

/-- A section of `f` supplies total range lifting: the lift of `q` is `q σ`. -/
theorem IsSection.hasTotalRangeLifting [HasRanges C] {X Y : C} {f : X ⟶ Y}
    {σ : Y ⟶ X} (h : IsSection f σ) : HasTotalRangeLifting f := by
  intro Z q hq hρ
  refine ⟨q ≫ σ, ?_, ?_⟩
  · rw [PCategory.rst_comp_rst_right', h.rst_eq_ran, hρ, hq]
  · rw [Category.assoc, h.comp_eq_rst, h.rst_eq_ran, hρ]

/-- Under the axiom of choice every morphism has total range lifting. -/
theorem hasTotalRangeLifting_of_hasChoice [HasRanges C] [HasChoice C] {X Y : C}
    (f : X ⟶ Y) : HasTotalRangeLifting f := by
  obtain ⟨σ, hσ⟩ := HasChoice.exists_isSection f
  exact hσ.hasTotalRangeLifting

end CategoryTheory
