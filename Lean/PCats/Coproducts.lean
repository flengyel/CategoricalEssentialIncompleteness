/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Ranges

/-!
# Coproducts, `P⁺`-categories, distributivity

Appendix A, lines 93–108. A `P`-category has coproducts when it carries a binary
coproduct with natural injections and codiagonals satisfying the equations dual
to the diagonal and projection equations of `PCategory`. The coproducts are
distributive when the two comparison morphisms are isomorphisms; that is
Heller's `P⁺`-structure, and a `P⁺`-category that is also an `rP`-category is an
`rP⁺`-category.

The injections are natural in *both* variables, where the projections are
half-natural: `p₀` is natural in the first variable only and `p₁` in the second.
A projection discards an argument, so a partial morphism in the discarded
coordinate is undefined on one side of the naturality square and not the other;
that is the failure `p1_proj_domain_id` repairs. An injection discards nothing,
so both squares commute and no restricted form is needed.

Two consequences. The four nested-injection identities `i0_i0`, `i0_i1`,
`i1_i0`, `i1_i1` are *theorems* here, immediate from naturality in the second
and first variable respectively — unlike their near-product duals, which must be
assumed. And `coprod` is a categorical coproduct: `existsUnique_copair`
has no totality hypothesis on either the mediating morphism or the two given
ones, whereas `existsUnique_partialPairing` needs both given morphisms total.

`copair_inj`, the eta rule `[i₀h, i₁h] = h`, is the dual of `partialPairing_proj`
and holds for the same reason: `[i₀, i₁] = 1`.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

/-- The data of a binary coproduct: the object, its action on morphisms, the
codiagonal, and the two injections. -/
class CoprodStruct (C : Type u) [Category.{v} C] where
  coprod (X Y : C) : C
  coprod_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : coprod W Y ⟶ coprod X Z
  codiag (X : C) : coprod X X ⟶ X
  i0 (X Y : C) : X ⟶ coprod X Y
  i1 (X Y : C) : Y ⟶ coprod X Y

namespace CoprodStruct

variable {C : Type u} [Category.{v} C] [CoprodStruct C]

/-- Copairing: `[f, g] = ∇ (f + g)`, dual to `⟨f, g⟩ = (f ⊠ g) Δ`. -/
def copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : coprod X Y ⟶ Z :=
  coprod_map f g ≫ codiag Z

end CoprodStruct

open CoprodStruct in
/-- A `P`-category has coproducts when the coproduct data satisfies the
equations dual to those of `PCategory`. -/
class HasCoproducts (C : Type u) [Category.{v} C] [CoprodStruct C] : Prop where
  -- Bifunctoriality of `+`.
  coprod_id : ∀ (X Y : C), coprod_map (𝟙 X) (𝟙 Y) = 𝟙 (coprod X Y)
  coprod_comp : ∀ {U V W X Y Z : C} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z),
    coprod_map f h ≫ coprod_map g k = coprod_map (f ≫ g) (h ≫ k)
  -- Dual to the diagonal–projection identities.
  i0_codiag : ∀ (X : C), i0 X X ≫ codiag X = 𝟙 X
  i1_codiag : ∀ (X : C), i1 X X ≫ codiag X = 𝟙 X
  i0_i1_codiag : ∀ (X Y : C),
    coprod_map (i0 X Y) (i1 X Y) ≫ codiag (coprod X Y) = 𝟙 (coprod X Y)
  -- Naturality of the codiagonal, and of each injection in *both* variables.
  codiag_nat : ∀ {X Y : C} (f : X ⟶ Y), coprod_map f f ≫ codiag Y = codiag X ≫ f
  i0_nat : ∀ {X Y Z : C} (f : X ⟶ Y), f ≫ i0 Y Z = i0 X Z ≫ coprod_map f (𝟙 Z)
  i0_nat_right : ∀ {X Y Z : C} (g : Y ⟶ Z),
    i0 X Y ≫ coprod_map (𝟙 X) g = i0 X Z
  i1_nat : ∀ {X Y Z : C} (f : X ⟶ Y), f ≫ i1 Z Y = i1 Z X ≫ coprod_map (𝟙 Z) f
  i1_nat_left : ∀ {X Y Z : C} (f : X ⟶ Y),
    i1 X Z ≫ coprod_map f (𝟙 Z) = i1 Y Z

namespace HasCoproducts

open CoprodStruct

variable {C : Type u} [Category.{v} C] [CoprodStruct C] [HasCoproducts C]

/-! ### The nested-injection identities

Consequences of naturality, unlike their near-product duals. -/

lemma i0_i0 (X Y Z : C) :
    i0 X Y ≫ coprod_map (𝟙 X) (i0 Y Z) = i0 X (coprod Y Z) := i0_nat_right _

lemma i0_i1 (X Y Z : C) :
    i0 X Z ≫ coprod_map (𝟙 X) (i1 Y Z) = i0 X (coprod Y Z) := i0_nat_right _

lemma i1_i0 (X Y Z : C) :
    i1 X Z ≫ coprod_map (i0 X Y) (𝟙 Z) = i1 (coprod X Y) Z := i1_nat_left _

lemma i1_i1 (X Y Z : C) :
    i1 Y Z ≫ coprod_map (i1 X Y) (𝟙 Z) = i1 (coprod X Y) Z := i1_nat_left _

/-! ### Copairing -/

lemma coprod_map_split {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    coprod_map f (𝟙 Y) ≫ coprod_map (𝟙 X) g = coprod_map f g := by
  rw [coprod_comp, Category.comp_id, Category.id_comp]

lemma coprod_map_split' {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    coprod_map (𝟙 W) g ≫ coprod_map f (𝟙 Z) = coprod_map f g := by
  rw [coprod_comp, Category.id_comp, Category.comp_id]

/-- `[f, g] i₀ = f`, with no restriction correction: the dual of Lemma A.1 is
exact, because the injections are total in the sense of discarding nothing. -/
lemma i0_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    i0 X Y ≫ copair f g = f := by
  have h : i0 X Y ≫ coprod_map f g = f ≫ i0 Z Z := by
    rw [← coprod_map_split f g, ← Category.assoc, ← i0_nat, Category.assoc,
      i0_nat_right]
  dsimp [copair]
  rw [← Category.assoc, h, Category.assoc, i0_codiag, Category.comp_id]

/-- `[f, g] i₁ = g`. -/
lemma i1_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    i1 X Y ≫ copair f g = g := by
  have h : i1 X Y ≫ coprod_map f g = g ≫ i1 Z Z := by
    rw [← coprod_map_split' f g, ← Category.assoc, ← i1_nat, Category.assoc,
      i1_nat_left]
  dsimp [copair]
  rw [← Category.assoc, h, Category.assoc, i1_codiag, Category.comp_id]

/-- The eta rule `[i₀h, i₁h] = h`, dual to `partialPairing_proj` and holding for
the same reason, that `[i₀, i₁] = 1`. -/
lemma copair_inj {X Y Z : C} (h : coprod X Y ⟶ Z) :
    copair (i0 X Y ≫ h) (i1 X Y ≫ h) = h := by
  dsimp [copair]
  rw [← coprod_comp, Category.assoc, codiag_nat, ← Category.assoc,
    i0_i1_codiag, Category.id_comp]

lemma eq_copair_of_inj {X Y Z : C} {h : coprod X Y ⟶ Z} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h0 : i0 X Y ≫ h = f) (h1 : i1 X Y ≫ h = g) : h = copair f g := by
  rw [← h0, ← h1, copair_inj]

/-- `coprod` is a categorical coproduct. Unlike `existsUnique_partialPairing`,
there is no totality hypothesis: the near product is a product only on the total
subcategory, whereas the coproduct is a coproduct outright. -/
theorem existsUnique_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃! h : coprod X Y ⟶ Z, i0 X Y ≫ h = f ∧ i1 X Y ≫ h = g := by
  refine ⟨copair f g, ⟨i0_copair f g, i1_copair f g⟩, ?_⟩
  rintro h ⟨h0, h1⟩
  exact eq_copair_of_inj h0 h1

/-- `[f, g] k = [fk, gk]`, dual to `comp_partialPairing`. -/
lemma copair_comp {X Y Z W : C} (f : X ⟶ Z) (g : Y ⟶ Z) (k : Z ⟶ W) :
    copair f g ≫ k = copair (f ≫ k) (g ≫ k) := by
  dsimp [copair]
  rw [Category.assoc, ← codiag_nat, ← Category.assoc, coprod_comp]

/-- `[i₀, i₁] = 1`. -/
lemma copair_i0_i1 (X Y : C) :
    copair (i0 X Y) (i1 X Y) = 𝟙 (coprod X Y) := by
  have := copair_inj (𝟙 (coprod X Y))
  rwa [Category.comp_id, Category.comp_id] at this

end HasCoproducts

open CoprodStruct in
/-- The left comparison morphism `[1 ⊠ ι₀, 1 ⊠ ι₁] : (W ⊠ U) + (W ⊠ V) ⟶
W ⊠ (U + V)`. -/
def distribLeft {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [CoprodStruct C] (W U V : C) :
    coprod (nearProd W U) (nearProd W V) ⟶ nearProd W (coprod U V) :=
  copair (nearProd_map (𝟙 W) (i0 U V)) (nearProd_map (𝟙 W) (i1 U V))

namespace HasCoproducts

open CoprodStruct

/-! ### Restriction and the coproduct

The injections are jointly epimorphic, by `copair_inj`, and R4 moves a
restriction past an injection without any totality hypothesis. Together these
compute the restriction of a morphism out of a coproduct. -/

section Restriction

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [CoprodStruct C] [HasCoproducts C]

omit [PCategoryStruct C] [PCategory C] in
/-- Morphisms out of a coproduct agreeing after both injections are equal. -/
lemma hom_ext {X Y Z : C} {h h' : coprod X Y ⟶ Z}
    (h0 : i0 X Y ≫ h = i0 X Y ≫ h') (h1 : i1 X Y ≫ h = i1 X Y ≫ h') :
    h = h' :=
  calc h = copair (i0 X Y ≫ h) (i1 X Y ≫ h) := (copair_inj h).symm
    _ = copair (i0 X Y ≫ h') (i1 X Y ≫ h') := by rw [h0, h1]
    _ = h' := copair_inj h'

omit [PCategoryStruct C] [PCategory C] in
/-- Precomposing a coproduct map with the left injection selects its left
component. -/
lemma i0_coprod_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    i0 W Y ≫ coprod_map f g = f ≫ i0 X Z := by
  rw [← coprod_map_split f g, ← Category.assoc, ← i0_nat, Category.assoc,
    i0_nat_right]

omit [PCategoryStruct C] [PCategory C] in
/-- Precomposing a coproduct map with the right injection selects its right
component. -/
lemma i1_coprod_map {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    i1 W Y ≫ coprod_map f g = g ≫ i1 X Z := by
  rw [← coprod_map_split' f g, ← Category.assoc, ← i1_nat, Category.assoc,
    i1_nat_left]

omit [PCategoryStruct C] [PCategory C] in
/-- A coproduct map is the copairing of its two components followed by the
corresponding target injections. -/
lemma coprod_map_eq_copair {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) :
    coprod_map f g = copair (f ≫ i0 X Z) (g ≫ i1 X Z) := by
  apply hom_ext
  · rw [i0_coprod_map, i0_copair]
  · rw [i1_coprod_map, i1_copair]

omit [PCategoryStruct C] [PCategory C] in
/-- The coproduct of two zero endomorphisms is the zero endomorphism. -/
lemma coprod_map_zero [Limits.HasZeroMorphisms C] {X Y : C} :
    coprod_map (0 : X ⟶ X) (0 : Y ⟶ Y) = 0 := by
  apply hom_ext
  · rw [i0_coprod_map, Limits.zero_comp, Limits.comp_zero]
  · rw [i1_coprod_map, Limits.zero_comp, Limits.comp_zero]

/-- The restriction of a morphism out of a coproduct is the coproduct of the
restrictions of its two components. -/
lemma rst_eq_coprod_map {X Y Z : C} (M : coprod X Y ⟶ Z) :
    rst M = coprod_map (rst (i0 X Y ≫ M)) (rst (i1 X Y ≫ M)) := by
  apply hom_ext
  · rw [i0_coprod_map]
    exact (PCategory.rst_comp' (i0 X Y) M).symm
  · rw [i1_coprod_map]
    exact (PCategory.rst_comp' (i1 X Y) M).symm

/-- `rst [f, g] = rst f + rst g`. -/
lemma rst_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    rst (copair f g) = coprod_map (rst f) (rst g) := by
  rw [rst_eq_coprod_map, i0_copair, i1_copair]

/-- The left injection of `X + X` is total. -/
lemma isTotal_i0_self (X : C) : rst (i0 X X) = 𝟙 X := by
  have h := RestrictionCategory.rst_comp_absorb (i0 X X) (codiag X)
  rw [i0_codiag, RestrictionCategory.rst_id, Category.comp_id] at h
  exact h

/-- The right injection of `X + X` is total. -/
lemma isTotal_i1_self (X : C) : rst (i1 X X) = 𝟙 X := by
  have h := RestrictionCategory.rst_comp_absorb (i1 X X) (codiag X)
  rw [i1_codiag, RestrictionCategory.rst_id, Category.comp_id] at h
  exact h

/-- `rst (f + g) = rst f + rst g` for endomorphisms of a single object, where
the injections of `X + X` are total. -/
lemma rst_coprod_map_self {X : C} (f g : X ⟶ X) :
    rst (coprod_map f g) = coprod_map (rst f) (rst g) := by
  rw [coprod_map_eq_copair, rst_copair, PCategory.rst_comp_rst_right',
    isTotal_i0_self, Category.comp_id, PCategory.rst_comp_rst_right',
    isTotal_i1_self, Category.comp_id]

end Restriction

end HasCoproducts

open CoprodStruct in
/-- The right comparison morphism `[ι₀ ⊠ 1, ι₁ ⊠ 1] : (U ⊠ W) + (V ⊠ W) ⟶
(U + V) ⊠ W`. -/
def distribRight {C : Type u} [Category.{v} C] [PCategoryStruct C]
    [CoprodStruct C] (U V W : C) :
    coprod (nearProd U W) (nearProd V W) ⟶ nearProd (coprod U V) W :=
  copair (nearProd_map (i0 U V) (𝟙 W)) (nearProd_map (i1 U V) (𝟙 W))

/-- Heller's `P⁺`-structure: the coproducts are distributive over the near
product. Assumed only where stated. -/
class Distributive (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] [CoprodStruct C] [HasCoproducts C] : Prop where
  isIso_distribLeft : ∀ (W U V : C), IsIso (distribLeft W U V)
  isIso_distribRight : ∀ (U V W : C), IsIso (distribRight U V W)

attribute [instance] Distributive.isIso_distribLeft Distributive.isIso_distribRight

end CategoryTheory
