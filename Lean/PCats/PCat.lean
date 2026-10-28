/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Restriction

/-!
# `P`-categories

Rosolini `P`-categories: Appendix A, sections A.2 and A.3, through the domain
calculus and Lemma A.3.

## Structural note

`PCategory` is a Prop-valued mixin over the data class `PCategoryStruct` rather
than a `structure` in an `extends` chain. This keeps the associator and symmetry
axioms statable — they mention `assoc` and `swap`, which are defined from the
data — and avoids instance-diamond questions downstream.

Only *naturality* of `assoc` and `swap` is assumed. Their invertibility is
derived in `isIso_assoc` and `isIso_swap`, following Rosolini's remark that the
four nested-projection identities are exactly what proves `α` and `µ`
isomorphisms.

## Spelling convention

Two terms denote the restriction operation once `inducedRestriction` is in
scope: `PCategoryStruct.rst` and the class projection `RestrictionCategory.rst`.
They are definitionally equal (`restrictionCategory_rst` is `rfl`) but have
different head constants, so `rw` and `simp` cannot cross between them —
`kabstract` filters candidate subterms by head constant before ever calling
`isDefEq`.

* Inside `namespace PCategory`, `PCategoryStruct.rst` is the normal form.
  Every lemma statement here uses it.
* To use a `RestrictionCategory` lemma, restate it with an explicit type
  ascription and let `exact` cross the definitional equality. The primed names
  below are exactly these bridges: `rst_comp_rst_right'`, together with the
  R2/R3/R4 lemmas `rst_comm'`, `rst_comp_rst'`, `rst_comp'`, which run the
  other way.
* Never repair a spelling mismatch with `rw [restrictionCategory_rst]`; it
  fires only when the projection spelling is already present syntactically.
-/

universe v u

namespace CategoryTheory

/-! ## 2. `P`-category data (Appendix A, §A.2) -/

/-- The data of a `P`-category: the near product `⊠`, its action on morphisms,
the diagonal, and the two projections. -/
class PCategoryStruct (C : Type u) [Category.{v} C] where
  nearProd (X Y : C) : C
  nearProd_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : nearProd W Y ⟶ nearProd X Z
  diag (X : C) : X ⟶ nearProd X X
  p0 (X Y : C) : nearProd X Y ⟶ X
  p1 (X Y : C) : nearProd X Y ⟶ Y

namespace PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C]

/-- Partial pairing `⟨f, g⟩ = (f ⊠ g) Δ`. -/
def partialPairing {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ nearProd X Y :=
  diag W ≫ nearProd_map f g

/-- Restriction in a `P`-category: `rst f = p₀ (1 ⊠ f) Δ`.  The second displayed
form in Appendix A, §A.3, is `rst_eq` below — a theorem, not an axiom. -/
def rst {X Y : C} (f : X ⟶ Y) : X ⟶ X :=
  diag X ≫ nearProd_map (𝟙 X) f ≫ p0 X Y

/-- Heller's `ass` (1.2), `(X ⊠ Y) ⊠ Z ⟶ X ⊠ (Y ⊠ Z)`; Rosolini's `α⁻¹`. -/
def assoc (X Y Z : C) : nearProd (nearProd X Y) Z ⟶ nearProd X (nearProd Y Z) :=
  partialPairing
    (p0 (nearProd X Y) Z ≫ p0 X Y)
    (partialPairing (p0 (nearProd X Y) Z ≫ p1 X Y) (p1 (nearProd X Y) Z))

/-- Rosolini's `tr` (Appendix A, §A.2). -/
def swap (X Y : C) : nearProd X Y ⟶ nearProd Y X :=
  partialPairing (p1 X Y) (p0 X Y)

end PCategoryStruct

open PCategoryStruct in
/-- The `P`-category axioms.  Rosolini Def. 2.1.2; Heller p. 1253 diagram (1.1)
and p. 1260. -/
class PCategory (C : Type u) [Category.{v} C] [PCategoryStruct C] : Prop where
  -- Bifunctoriality of `⊠`.
  nearProd_id : ∀ (X Y : C), nearProd_map (𝟙 X) (𝟙 Y) = 𝟙 (nearProd X Y)
  nearProd_comp : ∀ {U V W X Y Z : C} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z),
    nearProd_map f h ≫ nearProd_map g k = nearProd_map (f ≫ g) (h ≫ k)
  -- Diagonal--projection identities: Heller (1.1) for U = 2.
  diag_p0 : ∀ (X : C), diag X ≫ p0 X X = 𝟙 X
  diag_p1 : ∀ (X : C), diag X ≫ p1 X X = 𝟙 X
  diag_p0_p1 : ∀ (X Y : C),
    diag (nearProd X Y) ≫ nearProd_map (p0 X Y) (p1 X Y) = 𝟙 (nearProd X Y)
  -- Nested-projection identities.
  p0_p0 : ∀ (X Y Z : C), nearProd_map (𝟙 X) (p0 Y Z) ≫ p0 X Y = p0 X (nearProd Y Z)
  p0_p1 : ∀ (X Y Z : C), nearProd_map (𝟙 X) (p1 Y Z) ≫ p0 X Z = p0 X (nearProd Y Z)
  p1_p0 : ∀ (X Y Z : C), nearProd_map (p0 X Y) (𝟙 Z) ≫ p1 X Z = p1 (nearProd X Y) Z
  p1_p1 : ∀ (X Y Z : C), nearProd_map (p1 X Y) (𝟙 Z) ≫ p1 Y Z = p1 (nearProd X Y) Z
  -- Naturality of the diagonal; half-naturality of the projections.
  diag_nat : ∀ {X Y : C} (f : X ⟶ Y), f ≫ diag Y = diag X ≫ nearProd_map f f
  p0_nat : ∀ {X Y Z : C} (f : X ⟶ Y), nearProd_map f (𝟙 Z) ≫ p0 Y Z = p0 X Z ≫ f
  p1_nat : ∀ {X Y Z : C} (f : X ⟶ Y), nearProd_map (𝟙 Z) f ≫ p1 Z Y = p1 Z X ≫ f
  -- `ass` and `tr` are natural. Their invertibility is *not* an axiom: Rosolini
  -- notes that the four nested-projection identities are what proves `α` and
  -- `µ` isomorphisms, and `isIso_assoc`/`isIso_swap` below derive it.
  assoc_nat : ∀ {X X' Y Y' Z Z' : C} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    nearProd_map (nearProd_map f g) h ≫ assoc X' Y' Z'
      = assoc X Y Z ≫ nearProd_map f (nearProd_map g h)
  swap_nat : ∀ {X X' Y Y' : C} (f : X ⟶ X') (g : Y ⟶ Y'),
    nearProd_map f g ≫ swap X' Y' = swap X Y ≫ nearProd_map g f

namespace PCategory

open PCategoryStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-! ### Factorizations of `f ⊠ g` -/

lemma nearProd_comp_id_id_comp {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    nearProd_map f (𝟙 Y) ≫ nearProd_map (𝟙 X) g = nearProd_map f g := by
  rw [nearProd_comp, Category.comp_id, Category.id_comp]

lemma nearProd_id_comp_comp_id {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    nearProd_map (𝟙 W) g ≫ nearProd_map f (𝟙 Z) = nearProd_map f g := by
  rw [nearProd_comp, Category.id_comp, Category.comp_id]

/-! ### Lemma A.2 (reindexing of partial pairings) -/

/-- `⟨f, g⟩ h = ⟨fh, gh⟩`. -/
lemma comp_partialPairing {W Z X Y : C} (h : W ⟶ Z) (f : Z ⟶ X) (g : Z ⟶ Y) :
    h ≫ partialPairing f g = partialPairing (h ≫ f) (h ≫ g) := by
  dsimp [partialPairing]
  rw [← Category.assoc, diag_nat, Category.assoc, nearProd_comp]

/-! ### Lemma A.1 (projections of partial pairings) -/

/-- `p₀ ⟨f, g⟩ = f rst g`. -/
lemma p0_partialPairing {Z X Y : C} (f : Z ⟶ X) (g : Z ⟶ Y) :
    partialPairing f g ≫ p0 X Y = rst g ≫ f := by
  dsimp [partialPairing, rst]
  rw [← nearProd_id_comp_comp_id f g]
  rw [Category.assoc, Category.assoc, p0_nat]
  simp only [Category.assoc]

/-! ### The symmetry `tr`, and the second form of `rst` -/

/-- `p₁ tr = p₀`.  Uses only `p1_nat`, `p1_p1`, `diag_p1`, `nearProd_comp`; in
particular it does not depend on Lemma A.1 for `p₁`. -/
lemma swap_p1 (X Y : C) : swap X Y ≫ p1 Y X = p0 X Y := by
  dsimp [swap, partialPairing]
  rw [← nearProd_comp_id_id_comp (p1 X Y) (p0 X Y)]
  rw [Category.assoc, Category.assoc, p1_nat]
  rw [← Category.assoc (nearProd_map (p1 X Y) (𝟙 (nearProd X Y))), p1_p1]
  rw [← Category.assoc, diag_p1, Category.id_comp]

/-- `tr Δ = Δ`. -/
lemma diag_swap (X : C) : diag X ≫ swap X X = diag X := by
  dsimp [swap]
  rw [comp_partialPairing, diag_p0, diag_p1]
  dsimp [partialPairing]
  rw [nearProd_id, Category.comp_id]

/-- Appendix A, §A.3: `p₀ (1 ⊠ f) Δ = p₁ (f ⊠ 1) Δ`.  Formerly an axiom of
`PCategory`; it is a consequence of `swap_nat`. -/
lemma rst_eq {X Y : C} (f : X ⟶ Y) :
    diag X ≫ nearProd_map (𝟙 X) f ≫ p0 X Y
      = diag X ≫ nearProd_map f (𝟙 X) ≫ p1 Y X := by
  rw [← swap_p1 X Y]
  rw [← Category.assoc (nearProd_map (𝟙 X) f) (swap X Y) (p1 Y X)]
  rw [swap_nat (𝟙 X) f]
  rw [Category.assoc, ← Category.assoc (diag X) (swap X X), diag_swap]

/-- `p₁ ⟨f, g⟩ = g rst f`. -/
lemma p1_partialPairing {Z X Y : C} (f : Z ⟶ X) (g : Z ⟶ Y) :
    partialPairing f g ≫ p1 X Y = rst f ≫ g := by
  dsimp [partialPairing, rst]
  rw [← nearProd_comp_id_id_comp f g]
  rw [Category.assoc, Category.assoc, p1_nat]
  rw [← Category.assoc (nearProd_map f (𝟙 Z)) (p1 X Z) g]
  rw [← Category.assoc (diag Z) (nearProd_map f (𝟙 Z) ≫ p1 X Z) g]
  rw [← rst_eq]

/-! ### Totality of the projections -/

lemma p0_isTotal (X Y : C) : rst (p0 X Y) = 𝟙 (nearProd X Y) := by
  dsimp [rst]
  rw [p0_p0, diag_p0]

lemma p1_isTotal (X Y : C) : rst (p1 X Y) = 𝟙 (nearProd X Y) := by
  dsimp [rst]
  rw [p0_p1, diag_p0]

/-! ### Auxiliary pairing lemmas -/

lemma partialPairing_comp_nearProd_map {W X Y X' Y' : C}
    (u : W ⟶ X) (v : W ⟶ Y) (a : X ⟶ X') (b : Y ⟶ Y') :
    partialPairing u v ≫ nearProd_map a b = partialPairing (u ≫ a) (v ≫ b) := by
  dsimp [partialPairing]
  rw [Category.assoc, nearProd_comp]

lemma partialPairing_id_id (X : C) : partialPairing (𝟙 X) (𝟙 X) = diag X := by
  dsimp [partialPairing]
  rw [nearProd_id, Category.comp_id]

lemma partialPairing_p0_p1 (X Y : C) :
    partialPairing (p0 X Y) (p1 X Y) = 𝟙 (nearProd X Y) :=
  diag_p0_p1 X Y

omit [PCategory C] in
/-- `rst f = ⟨1, f⟩ p₀`. -/
lemma rst_eq_partialPairing {X Y : C} (f : X ⟶ Y) :
    rst f = partialPairing (𝟙 X) f ≫ p0 X Y := by
  dsimp [rst, partialPairing]
  rw [Category.assoc]

lemma rst_id (X : C) : rst (𝟙 X) = 𝟙 X := by
  dsimp [rst]
  rw [nearProd_id, Category.id_comp, diag_p0]

lemma diag_isTotal (X : C) : rst (diag X) = 𝟙 X := by
  dsimp [rst]
  rw [← p0_p0 X X X,
    ← Category.assoc (nearProd_map (𝟙 X) (diag X)) (nearProd_map (𝟙 X) (p0 X X)) (p0 X X),
    nearProd_comp, Category.id_comp, diag_p0, nearProd_id, Category.id_comp, diag_p0]

/-! ### The associator: projection and coherence identities -/

lemma assoc_nearProd_p0 (X Y Z : C) :
    assoc X Y Z ≫ nearProd_map (𝟙 X) (p0 Y Z) = p0 (nearProd X Y) Z := by
  dsimp [assoc]
  rw [partialPairing_comp_nearProd_map, Category.comp_id,
    p0_partialPairing (p0 (nearProd X Y) Z ≫ p1 X Y) (p1 (nearProd X Y) Z),
    p1_isTotal, Category.id_comp, ← comp_partialPairing, partialPairing_p0_p1,
    Category.comp_id]

lemma assoc_p0 (X Y Z : C) :
    assoc X Y Z ≫ p0 X (nearProd Y Z) = p0 (nearProd X Y) Z ≫ p0 X Y := by
  rw [← p0_p0 X Y Z, ← Category.assoc, assoc_nearProd_p0]

/-- Coherence: `⟨Δ, 1⟩ ass = ⟨1, Δ⟩`.  The only place the associator's naturality
is prepared for use. -/
lemma diag_assoc (X : C) :
    partialPairing (diag X) (𝟙 X) ≫ assoc X X X = partialPairing (𝟙 X) (diag X) := by
  have h0 : partialPairing (diag X) (𝟙 X) ≫ p0 (nearProd X X) X = diag X := by
    rw [p0_partialPairing, rst_id, Category.id_comp]
  have h1 : partialPairing (diag X) (𝟙 X) ≫ p1 (nearProd X X) X = 𝟙 X := by
    rw [p1_partialPairing, diag_isTotal, Category.id_comp]
  dsimp [assoc]
  rw [comp_partialPairing, ← Category.assoc, h0, diag_p0, comp_partialPairing,
    ← Category.assoc, h0, diag_p1, h1, partialPairing_id_id]

/-- `⟨⟨1, f⟩, g⟩ ass = ⟨1, ⟨f, g⟩⟩`. -/
lemma partialPairing_assoc {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    partialPairing (partialPairing (𝟙 X) f) g ≫ assoc X Y Z
      = partialPairing (𝟙 X) (partialPairing f g) := by
  have e1 : partialPairing (partialPairing (𝟙 X) f) g
      = partialPairing (diag X) (𝟙 X) ≫ nearProd_map (nearProd_map (𝟙 X) f) g := by
    rw [partialPairing_comp_nearProd_map, Category.id_comp]
    rfl
  rw [e1, Category.assoc, assoc_nat (𝟙 X) f g, ← Category.assoc, diag_assoc,
    partialPairing_comp_nearProd_map, Category.id_comp]
  rfl

/-! ### The three remaining restriction axioms -/

/-- `rst ⟨f, g⟩ = rst g rst f`.  This is the crux; everything below is
bookkeeping. -/
lemma rst_partialPairing_eq {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst (partialPairing f g) = rst g ≫ rst f := by
  rw [rst_eq_partialPairing, ← partialPairing_assoc, Category.assoc, assoc_p0,
    ← Category.assoc, p0_partialPairing (partialPairing (𝟙 X) f) g, Category.assoc,
    ← rst_eq_partialPairing]

/-- Via the nested projection `p₀ (1 ⊠ p₀) = p₀`. -/
lemma rst_partialPairing_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst (partialPairing f g) = rst (rst g ≫ f) := by
  rw [rst_eq_partialPairing (partialPairing f g), rst_eq_partialPairing (rst g ≫ f),
    ← p0_p0 X Y Z, ← Category.assoc, partialPairing_comp_nearProd_map,
    Category.comp_id, p0_partialPairing f g]

/-- Via the nested projection `p₀ (1 ⊠ p₁) = p₀`. -/
lemma rst_partialPairing_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst (partialPairing f g) = rst (rst f ≫ g) := by
  rw [rst_eq_partialPairing (partialPairing f g), rst_eq_partialPairing (rst f ≫ g),
    ← p0_p1 X Y Z, ← Category.assoc, partialPairing_comp_nearProd_map,
    Category.comp_id, p1_partialPairing f g]

lemma rst_partialPairing_comm {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst (partialPairing f g) = rst (partialPairing g f) := by
  rw [rst_partialPairing_left f g, rst_partialPairing_right g f]

/-- R2. -/
lemma rst_comm' {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst f ≫ rst g = rst g ≫ rst f := by
  rw [← rst_partialPairing_eq g f, ← rst_partialPairing_eq f g]
  exact rst_partialPairing_comm g f

/-- R3. -/
lemma rst_comp_rst' {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) :
    rst (rst f ≫ g) = rst f ≫ rst g := by
  rw [← rst_partialPairing_right f g, rst_partialPairing_eq f g, rst_comm' g f]

/-- R4.  Needs neither the associator nor the symmetry. -/
lemma rst_comp' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rst (f ≫ g) ≫ f = f ≫ rst g := by
  rw [rst_eq_partialPairing g, ← Category.assoc, comp_partialPairing,
    Category.comp_id, p0_partialPairing f (f ≫ g)]

/-! ### The induced restriction category (Rosolini Prop. 2.1.4, Cor. 2.1.5) -/

instance inducedRestriction : RestrictionCategory C where
  rst := rst
  rst_comp_self {X Y} f := by
    dsimp [rst]
    rw [rst_eq]
    rw [Category.assoc, Category.assoc]
    rw [← p1_nat]
    rw [← Category.assoc (nearProd_map f (𝟙 X))]
    rw [nearProd_comp]
    rw [Category.comp_id, Category.id_comp]
    rw [← Category.assoc (diag X)]
    rw [← diag_nat]
    rw [Category.assoc]
    rw [diag_p1]
    rw [Category.comp_id]
  rst_comm := rst_comm'
  rst_comp_rst := rst_comp_rst'
  rst_comp := rst_comp'

@[simp] lemma restrictionCategory_rst {X Y : C} (f : X ⟶ Y) :
    RestrictionCategory.rst f = rst f := rfl

/-! ### Domain calculus (Appendix A, §A.3, and Lemma A.3) -/

/-- `rst ⟨f, g⟩ = rst f rst g` (Lemma A.1, third identity). -/
lemma rst_partialPairing {Z X Y : C} (f : Z ⟶ X) (g : Z ⟶ Y) :
    rst (partialPairing f g) = rst f ≫ rst g := by
  rw [rst_partialPairing_eq, rst_comm']

/-- Every `h : Z ⟶ X ⊠ Y` is the partial pairing of its own projections.  This
holds for arbitrary `h`, not just total `h`, because `⟨p₀, p₁⟩ = 1`. -/
lemma partialPairing_proj {Z X Y : C} (h : Z ⟶ nearProd X Y) :
    partialPairing (h ≫ p0 X Y) (h ≫ p1 X Y) = h := by
  rw [← comp_partialPairing, partialPairing_p0_p1, Category.comp_id]

/-- `f ⊠ g = ⟨p₀ f, p₁ g⟩`. -/
lemma nearProd_eq_partialPairing {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    nearProd_map f g = partialPairing (p0 W Y ≫ f) (p1 W Y ≫ g) := by
  dsimp [partialPairing]
  rw [← nearProd_comp, ← Category.assoc, diag_p0_p1, Category.id_comp]

/-- `rst (gf) = rst (rst g f)`, at the `PCategoryStruct.rst` spelling. -/
lemma rst_comp_rst_right' {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rst (f ≫ g) = rst (f ≫ rst g) :=
  RestrictionCategory.rst_comp_rst_right f g

lemma rst_rst {X Y : C} (f : X ⟶ Y) : rst (rst f) = rst f := by
  have h := rst_comp_rst_right' (𝟙 X) f
  simp only [Category.id_comp] at h
  exact h.symm

/-- `rst (gf) = rst f` for total `g`, at the `PCategoryStruct.rst` spelling. -/
lemma rst_comp_of_isTotal' {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z}
    (hg : rst g = 𝟙 Y) : rst (f ≫ g) = rst f :=
  RestrictionCategory.rst_comp_of_isTotal f hg

/-- Lemma A.3, first identity: `d ⊠ 1 = rst (d p₀)`. -/
lemma nearProd_domain_left {X Y : C} (d : X ⟶ X) (hd : rst d = d) :
    nearProd_map d (𝟙 Y) = rst (p0 X Y ≫ d) := by
  have h0 : rst (p0 X Y ≫ d) ≫ p0 X Y = p0 X Y ≫ d := by
    rw [rst_comp', hd]
  have h1 : nearProd_map d (𝟙 Y) ≫ p0 X Y = p0 X Y ≫ d := by
    rw [nearProd_eq_partialPairing, Category.comp_id, p0_partialPairing,
      p1_isTotal, Category.id_comp]
  have h2 : nearProd_map d (𝟙 Y) ≫ p1 X Y = rst (p0 X Y ≫ d) ≫ p1 X Y := by
    rw [nearProd_eq_partialPairing, Category.comp_id, p1_partialPairing]
  calc nearProd_map d (𝟙 Y)
      = partialPairing (nearProd_map d (𝟙 Y) ≫ p0 X Y)
          (nearProd_map d (𝟙 Y) ≫ p1 X Y) := (partialPairing_proj _).symm
    _ = partialPairing (rst (p0 X Y ≫ d) ≫ p0 X Y)
          (rst (p0 X Y ≫ d) ≫ p1 X Y) := by rw [h0, h1, h2]
    _ = rst (p0 X Y ≫ d) := partialPairing_proj _

/-- Lemma A.3, second identity: `1 ⊠ e = rst (e p₁)`. -/
lemma nearProd_domain_right {X Y : C} (e : Y ⟶ Y) (he : rst e = e) :
    nearProd_map (𝟙 X) e = rst (p1 X Y ≫ e) := by
  have h0 : rst (p1 X Y ≫ e) ≫ p1 X Y = p1 X Y ≫ e := by
    rw [rst_comp', he]
  have h1 : nearProd_map (𝟙 X) e ≫ p1 X Y = p1 X Y ≫ e := by
    rw [nearProd_eq_partialPairing, Category.comp_id, p1_partialPairing,
      p0_isTotal, Category.id_comp]
  have h2 : nearProd_map (𝟙 X) e ≫ p0 X Y = rst (p1 X Y ≫ e) ≫ p0 X Y := by
    rw [nearProd_eq_partialPairing, Category.comp_id, p0_partialPairing]
  calc nearProd_map (𝟙 X) e
      = partialPairing (nearProd_map (𝟙 X) e ≫ p0 X Y)
          (nearProd_map (𝟙 X) e ≫ p1 X Y) := (partialPairing_proj _).symm
    _ = partialPairing (rst (p1 X Y ≫ e) ≫ p0 X Y)
          (rst (p1 X Y ≫ e) ≫ p1 X Y) := by rw [h0, h1, h2]
    _ = rst (p1 X Y ≫ e) := partialPairing_proj _

/-- Lemma A.3: if `rst (d p₀)` receives `w`, then `d` receives the first
projection of `w`. -/
lemma comp_p0_domain_of_comp_rst {Z X Y : C} (d : X ⟶ X) (hd : rst d = d)
    (w : Z ⟶ nearProd X Y) (hw : w ≫ rst (p0 X Y ≫ d) = w) :
    (w ≫ p0 X Y) ≫ d = w ≫ p0 X Y := by
  rw [Category.assoc, ← p0_nat (Z := Y) d, ← Category.assoc,
    nearProd_domain_left d hd, hw]

/-- Lemma A.3: if `rst (e p₁)` receives `w`, then `e` receives the second
projection of `w`. -/
lemma comp_p1_domain_of_comp_rst {Z X Y : C} (e : Y ⟶ Y) (he : rst e = e)
    (w : Z ⟶ nearProd X Y) (hw : w ≫ rst (p1 X Y ≫ e) = w) :
    (w ≫ p1 X Y) ≫ e = w ≫ p1 X Y := by
  rw [Category.assoc, ← p1_nat (Z := X) e, ← Category.assoc,
    nearProd_domain_right e he, hw]

/-- `rst (f ⊠ g) = rst f ⊠ rst g` (Di Paola--Heller Lemma 3.5(v)). -/
lemma rst_nearProd_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    rst (nearProd_map f g) = nearProd_map (rst f) (rst g) := by
  have hl : nearProd_map (rst f) (𝟙 Y) = rst (p0 W Y ≫ f) := by
    rw [nearProd_domain_left (rst f) (rst_rst f), ← rst_comp_rst_right']
  have hr : nearProd_map (𝟙 W) (rst g) = rst (p1 W Y ≫ g) := by
    rw [nearProd_domain_right (rst g) (rst_rst g), ← rst_comp_rst_right']
  have hsplit : nearProd_map (rst f) (rst g)
      = nearProd_map (rst f) (𝟙 Y) ≫ nearProd_map (𝟙 W) (rst g) := by
    rw [nearProd_comp, Category.comp_id, Category.id_comp]
  rw [hsplit, hl, hr, nearProd_eq_partialPairing, rst_partialPairing]

/-- Appendix A: `p₁ (f ⊠ 1) = p₁ (rst f ⊠ 1)`. -/
lemma p1_proj_domain_id {X Y Z : C} (f : X ⟶ Y) :
    nearProd_map f (𝟙 Z) ≫ p1 Y Z = nearProd_map (rst f) (𝟙 Z) ≫ p1 X Z := by
  rw [nearProd_eq_partialPairing f (𝟙 Z), nearProd_eq_partialPairing (rst f) (𝟙 Z)]
  simp only [Category.comp_id, p1_partialPairing]
  rw [← rst_comp_rst_right' (p0 X Z) f]

/-- Appendix A: `p₀ (1 ⊠ f) = p₀ (1 ⊠ rst f)`. -/
lemma p0_proj_domain_id {Z X Y : C} (f : Z ⟶ Y) :
    nearProd_map (𝟙 X) f ≫ p0 X Y = nearProd_map (𝟙 X) (rst f) ≫ p0 X Z := by
  rw [nearProd_eq_partialPairing (𝟙 X) f, nearProd_eq_partialPairing (𝟙 X) (rst f)]
  simp only [Category.comp_id, p0_partialPairing]
  rw [← rst_comp_rst_right' (p1 X Z) f]

/-! ### Naturality of the projections at a total argument

The content of Heller's naturalizer clause `C × P ⊆ nat p₀`, `P × C ⊆ nat p₁`:
totality of the argument in the discarded coordinate is all the naturality
square needs. `PCats.HellerNaturalizer` builds `P` itself and derives the two
containments from these lemmas.
The companion equations fail without it — `p1_proj_domain_id` and
`p0_proj_domain_id` above are their corrected forms. -/

/-- `p₀ (f ⊠ g) = f p₀` when `g` is total. -/
lemma p0_nat_of_isTotal {W X Y Z : C} (f : W ⟶ X) {g : Y ⟶ Z}
    (hg : rst g = 𝟙 Y) : nearProd_map f g ≫ p0 X Z = p0 W Y ≫ f := by
  rw [← nearProd_comp_id_id_comp f g, Category.assoc, p0_proj_domain_id, hg,
    nearProd_id, Category.id_comp, p0_nat]

/-- `p₁ (f ⊠ g) = g p₁` when `f` is total. -/
lemma p1_nat_of_isTotal {W X Y Z : C} {f : W ⟶ X} (g : Y ⟶ Z)
    (hf : rst f = 𝟙 W) : nearProd_map f g ≫ p1 X Z = p1 W Y ≫ g := by
  rw [← nearProd_id_comp_comp_id f g, Category.assoc, p1_proj_domain_id, hf,
    nearProd_id, Category.id_comp, p1_nat]

/-! ### The near product is a categorical product on the total subcategory

Appendix A, lines 122–131. Rosolini Prop. 2.1.7 and Cor. 2.1.8; Heller p. 1261.
The universal property splits unevenly: existence of the mediating morphism
needs `u` and `v` total, uniqueness does not. -/

/-- `rst (p₀ h) = rst h`. -/
lemma rst_comp_p0 {Z X Y : C} (h : Z ⟶ nearProd X Y) :
    rst (h ≫ p0 X Y) = rst h := by
  rw [rst_comp_rst_right', p0_isTotal, Category.comp_id]

/-- `rst (p₁ h) = rst h`. -/
lemma rst_comp_p1 {Z X Y : C} (h : Z ⟶ nearProd X Y) :
    rst (h ≫ p1 X Y) = rst h := by
  rw [rst_comp_rst_right', p1_isTotal, Category.comp_id]

/-- If either projection of `h` is total, then `h` is total. -/
lemma isTotal_of_comp_p0 {Z X Y : C} {h : Z ⟶ nearProd X Y}
    (h0 : rst (h ≫ p0 X Y) = 𝟙 Z) : rst h = 𝟙 Z := by
  rwa [rst_comp_p0] at h0

lemma isTotal_of_comp_p1 {Z X Y : C} {h : Z ⟶ nearProd X Y}
    (h1 : rst (h ≫ p1 X Y) = 𝟙 Z) : rst h = 𝟙 Z := by
  rwa [rst_comp_p1] at h1

/-- Total morphisms are closed under the near product. -/
lemma isTotal_nearProd_map {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z}
    (hf : rst f = 𝟙 W) (hg : rst g = 𝟙 Y) :
    rst (nearProd_map f g) = 𝟙 (nearProd W Y) := by
  rw [rst_nearProd_map, hf, hg, nearProd_id]

/-- `⟨u, v⟩` is total when `u` and `v` are. -/
lemma isTotal_partialPairing {Z X Y : C} {u : Z ⟶ X} {v : Z ⟶ Y}
    (hu : rst u = 𝟙 Z) (hv : rst v = 𝟙 Z) : rst (partialPairing u v) = 𝟙 Z := by
  rw [rst_partialPairing, hu, hv, Category.comp_id]

/-- `p₀ ⟨u, v⟩ = u` when `v` is total. -/
lemma p0_partialPairing_of_isTotal {Z X Y : C} (u : Z ⟶ X) {v : Z ⟶ Y}
    (hv : rst v = 𝟙 Z) : partialPairing u v ≫ p0 X Y = u := by
  rw [p0_partialPairing, hv, Category.id_comp]

/-- `p₁ ⟨u, v⟩ = v` when `u` is total. -/
lemma p1_partialPairing_of_isTotal {Z X Y : C} {u : Z ⟶ X} (v : Z ⟶ Y)
    (hu : rst u = 𝟙 Z) : partialPairing u v ≫ p1 X Y = v := by
  rw [p1_partialPairing, hu, Category.id_comp]

/-- Uniqueness of the mediating morphism. This holds for arbitrary `h`, not only
total `h`, because `⟨p₀, p₁⟩ = 1`; the appendix states the pairing property for
total `h` only, which is weaker than what the axioms give. -/
lemma eq_partialPairing_of_proj {Z X Y : C} {h : Z ⟶ nearProd X Y}
    {u : Z ⟶ X} {v : Z ⟶ Y} (h0 : h ≫ p0 X Y = u) (h1 : h ≫ p1 X Y = v) :
    h = partialPairing u v := by
  rw [← h0, ← h1, partialPairing_proj]

/-- The universal property of the binary product, on total morphisms. -/
theorem existsUnique_partialPairing {Z X Y : C} {u : Z ⟶ X} {v : Z ⟶ Y}
    (hu : rst u = 𝟙 Z) (hv : rst v = 𝟙 Z) :
    ∃! h : Z ⟶ nearProd X Y, h ≫ p0 X Y = u ∧ h ≫ p1 X Y = v := by
  refine ⟨partialPairing u v,
    ⟨p0_partialPairing_of_isTotal u hv, p1_partialPairing_of_isTotal v hu⟩, ?_⟩
  rintro h ⟨h0, h1⟩
  exact eq_partialPairing_of_proj h0 h1

/-! ### The associator and the symmetry are isomorphisms

`assoc` is Heller's `ass` from (1.2), running `(X ⊠ Y) ⊠ Z ⟶ X ⊠ (Y ⊠ Z)`, and
`assocInv` is its inverse. Rosolini writes his `α` in the opposite direction, so
`assoc` is his `α⁻¹` and `assocInv` is his `α`.

Invertibility is a theorem, not an axiom: Rosolini Def. 2.1.2 assumes only that
`α` and `µ` are natural, and remarks that the four nested-projection identities
are what proves them isomorphisms. -/

lemma swap_p0 (X Y : C) : swap X Y ≫ p0 Y X = p1 X Y := by
  dsimp [swap, partialPairing]
  rw [← nearProd_id_comp_comp_id (p1 X Y) (p0 X Y)]
  rw [Category.assoc, Category.assoc, p0_nat]
  rw [← Category.assoc (nearProd_map (𝟙 (nearProd X Y)) (p0 X Y)), p0_p0]
  rw [← Category.assoc, diag_p0, Category.id_comp]

lemma swap_swap (X Y : C) : swap X Y ≫ swap Y X = 𝟙 (nearProd X Y) := by
  have h0 : (swap X Y ≫ swap Y X) ≫ p0 X Y = p0 X Y := by
    rw [Category.assoc, swap_p0, swap_p1]
  have h1 : (swap X Y ≫ swap Y X) ≫ p1 X Y = p1 X Y := by
    rw [Category.assoc, swap_p1, swap_p0]
  rw [eq_partialPairing_of_proj h0 h1, partialPairing_p0_p1]

instance isIso_swap (X Y : C) : IsIso (swap X Y) :=
  ⟨⟨swap Y X, swap_swap X Y, swap_swap Y X⟩⟩

lemma assoc_p1 (X Y Z : C) :
    assoc X Y Z ≫ p1 X (nearProd Y Z)
      = partialPairing (p0 (nearProd X Y) Z ≫ p1 X Y) (p1 (nearProd X Y) Z) := by
  have ht : rst (p0 (nearProd X Y) Z ≫ p0 X Y)
      = 𝟙 (nearProd (nearProd X Y) Z) := by
    rw [rst_comp_of_isTotal' _ (p0_isTotal X Y), p0_isTotal]
  dsimp [assoc]
  rw [p1_partialPairing, ht, Category.id_comp]

/-- The inverse of `assoc`; Rosolini's `α`. -/
def assocInv (X Y Z : C) :
    nearProd X (nearProd Y Z) ⟶ nearProd (nearProd X Y) Z :=
  partialPairing
    (partialPairing (p0 X (nearProd Y Z)) (p1 X (nearProd Y Z) ≫ p0 Y Z))
    (p1 X (nearProd Y Z) ≫ p1 Y Z)

lemma assocInv_p0 (X Y Z : C) :
    assocInv X Y Z ≫ p0 (nearProd X Y) Z
      = partialPairing (p0 X (nearProd Y Z)) (p1 X (nearProd Y Z) ≫ p0 Y Z) := by
  have ht : rst (p1 X (nearProd Y Z) ≫ p1 Y Z)
      = 𝟙 (nearProd X (nearProd Y Z)) := by
    rw [rst_comp_of_isTotal' _ (p1_isTotal Y Z), p1_isTotal]
  dsimp [assocInv]
  rw [p0_partialPairing, ht, Category.id_comp]

lemma assocInv_p1 (X Y Z : C) :
    assocInv X Y Z ≫ p1 (nearProd X Y) Z = p1 X (nearProd Y Z) ≫ p1 Y Z := by
  have ht : rst (partialPairing (p0 X (nearProd Y Z))
      (p1 X (nearProd Y Z) ≫ p0 Y Z)) = 𝟙 (nearProd X (nearProd Y Z)) := by
    rw [rst_partialPairing, p0_isTotal, rst_comp_of_isTotal' _ (p0_isTotal Y Z),
      p1_isTotal, Category.comp_id]
  dsimp [assocInv]
  rw [p1_partialPairing, ht, Category.id_comp]

lemma assoc_assocInv (X Y Z : C) :
    assoc X Y Z ≫ assocInv X Y Z = 𝟙 (nearProd (nearProd X Y) Z) := by
  have h0 : (assoc X Y Z ≫ assocInv X Y Z) ≫ p0 (nearProd X Y) Z
      = p0 (nearProd X Y) Z := by
    rw [Category.assoc, assocInv_p0, comp_partialPairing, assoc_p0,
      ← Category.assoc, assoc_p1, p0_partialPairing, p1_isTotal,
      Category.id_comp, ← comp_partialPairing, partialPairing_p0_p1,
      Category.comp_id]
  have h1 : (assoc X Y Z ≫ assocInv X Y Z) ≫ p1 (nearProd X Y) Z
      = p1 (nearProd X Y) Z := by
    rw [Category.assoc, assocInv_p1, ← Category.assoc, assoc_p1,
      p1_partialPairing, rst_comp_of_isTotal' _ (p1_isTotal X Y), p0_isTotal,
      Category.id_comp]
  rw [eq_partialPairing_of_proj h0 h1, partialPairing_p0_p1]

lemma assocInv_assoc (X Y Z : C) :
    assocInv X Y Z ≫ assoc X Y Z = 𝟙 (nearProd X (nearProd Y Z)) := by
  have h0 : (assocInv X Y Z ≫ assoc X Y Z) ≫ p0 X (nearProd Y Z)
      = p0 X (nearProd Y Z) := by
    rw [Category.assoc, assoc_p0, ← Category.assoc, assocInv_p0,
      p0_partialPairing, rst_comp_of_isTotal' _ (p0_isTotal Y Z), p1_isTotal,
      Category.id_comp]
  have h1 : (assocInv X Y Z ≫ assoc X Y Z) ≫ p1 X (nearProd Y Z)
      = p1 X (nearProd Y Z) := by
    rw [Category.assoc, assoc_p1, comp_partialPairing, ← Category.assoc,
      assocInv_p0, p1_partialPairing, p0_isTotal, Category.id_comp,
      assocInv_p1, ← comp_partialPairing, partialPairing_p0_p1,
      Category.comp_id]
  rw [eq_partialPairing_of_proj h0 h1, partialPairing_p0_p1]

instance isIso_assoc (X Y Z : C) : IsIso (assoc X Y Z) :=
  ⟨⟨assocInv X Y Z, assoc_assocInv X Y Z, assocInv_assoc X Y Z⟩⟩

end PCategory
end CategoryTheory
