/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnrichedRestriction

/-!
# Internal composition and products of total arrows

The restriction-product equations imply closure of total arrows under pairing.
Identities, composition, and pairing therefore lift to the totality
pullbacks. Monicity of their inclusions then proves the category and ordinary
binary-product equations required by `InternalHom.CartesianLaws`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H)

/-- Chosen binary restriction products, with their partial projection equations. -/
structure Products where
  first_total : ∀ X Y, H.first X Y ≫ R.restriction (H.product X Y) X = H.unit (H.product X Y)
  second_total : ∀ X Y,
    H.second X Y ≫ R.restriction (H.product X Y) Y = H.unit (H.product X Y)
  pair_fst : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (H.pair f g) (H.fst Y Z) = H.comp (R.restrict g) f
  pair_snd : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (H.pair f g) (H.snd Y Z) = H.comp (R.restrict f) g
  pair_eta : ∀ {T X Y Z} (f : T ⟶ H.hom X (H.product Y Z)),
    H.pair (H.comp f (H.fst Y Z)) (H.comp f (H.snd Y Z)) = f

namespace Products
variable {R} (P : R.Products)
include P

@[simp] theorem fst_total {T : V} (X Y : O) :
    R.restrict (H.fst (T := T) X Y) = H.identity (H.product X Y) := by
  simp only [restrict, InternalHom.fst, Category.assoc, P.first_total, InternalHom.identity]

@[simp] theorem snd_total {T : V} (X Y : O) :
    R.restrict (H.snd (T := T) X Y) = H.identity (H.product X Y) := by
  simp only [restrict, InternalHom.snd, Category.assoc, P.second_total, InternalHom.identity]

/-- The restriction of a pairing is the meet of the two restrictions. -/
theorem restrict_pair {T : V} {X Y Z : O}
    (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z) :
    R.restrict (H.pair f g) = H.comp (R.restrict g) (R.restrict f) := by
  rw [← R.restrict_comp_of_total (H.pair f g) (H.fst Y Z) (P.fst_total Y Z), P.pair_fst]
  exact R.rst_comp_rst g f

theorem pair_total {T : V} {X Y Z : O} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z)
    (hf : R.restrict f = H.identity X) (hg : R.restrict g = H.identity X) :
    R.restrict (H.pair f g) = H.identity X := by
  rw [P.restrict_pair, hf, hg, R.id_comp]

end Products

private theorem terminal_from_self : terminal.from (⊤_ V) = 𝟙 (⊤_ V) :=
  terminalIsTerminal.hom_ext _ _

/-- The total-arrow reduct, with all operations constructed by pullback lifts. -/
def totalHom (P : R.Products) : InternalHom V O where
  hom := R.totalObject
  unit X := R.totalLift (H.unit X) (by
    simpa [InternalHom.identity, terminal_from_self] using (R.restrict_identity (T := ⊤_ V) X))
  composition X Y Z := R.totalLift
    (H.comp (prod.fst ≫ R.totalι X Y) (prod.snd ≫ R.totalι Y Z))
    (R.total_comp _ _ (R.total_condition prod.fst) (R.total_condition prod.snd))
  product := H.product
  first X Y := R.totalLift (H.first X Y) (by
    simpa [restrict, InternalHom.identity, terminal_from_self] using P.first_total X Y)
  second X Y := R.totalLift (H.second X Y) (by
    simpa [restrict, InternalHom.identity, terminal_from_self] using P.second_total X Y)
  pairing X Y Z := R.totalLift
    (H.pair (prod.fst ≫ R.totalι X Y) (prod.snd ≫ R.totalι X Z))
    (P.pair_total _ _ (R.total_condition prod.fst) (R.total_condition prod.snd))

variable (P : R.Products)

@[simp] theorem total_identity_ι {T : V} (X : O) :
    (R.totalHom P).identity (T := T) X ≫ R.totalι X X = H.identity X := by
  simp [InternalHom.identity, totalHom, Category.assoc]

@[simp] theorem total_fst_ι {T : V} (X Y : O) :
    (R.totalHom P).fst (T := T) X Y ≫ R.totalι (H.product X Y) X = H.fst X Y := by
  simp [InternalHom.fst, totalHom, Category.assoc]

@[simp] theorem total_snd_ι {T : V} (X Y : O) :
    (R.totalHom P).snd (T := T) X Y ≫ R.totalι (H.product X Y) Y = H.snd X Y := by
  simp [InternalHom.snd, totalHom, Category.assoc]

@[simp] theorem total_comp_ι {T : V} {X Y Z : O}
    (f : T ⟶ R.totalObject X Y) (g : T ⟶ R.totalObject Y Z) :
    (R.totalHom P).comp f g ≫ R.totalι X Z =
      H.comp (f ≫ R.totalι X Y) (g ≫ R.totalι Y Z) := by
  simp [InternalHom.comp, totalHom, Category.assoc]

@[simp] theorem total_pair_ι {T : V} {X Y Z : O}
    (f : T ⟶ R.totalObject X Y) (g : T ⟶ R.totalObject X Z) :
    (R.totalHom P).pair f g ≫ R.totalι X (H.product Y Z) =
      H.pair (f ≫ R.totalι X Y) (g ≫ R.totalι X Z) := by
  simp [InternalHom.pair, totalHom, Category.assoc]

/-- The constructed total hom-objects satisfy the internal category and product laws. -/
instance totalHom_cartesian : (R.totalHom P).CartesianLaws where
  assoc f g h := by
    apply (cancel_mono (R.totalι _ _)).mp
    simp only [R.total_comp_ι]
    exact R.assoc _ _ _
  id_comp f := by
    apply (cancel_mono (R.totalι _ _)).mp
    simp only [R.total_comp_ι, R.total_identity_ι]
    exact R.id_comp _
  comp_id f := by
    apply (cancel_mono (R.totalι _ _)).mp
    simp only [R.total_comp_ι, R.total_identity_ι]
    exact R.comp_id _
  pair_fst f g := by
    apply (cancel_mono (R.totalι _ _)).mp
    simp only [R.total_comp_ι]
    change H.comp ((R.totalHom P).pair f g ≫ R.totalι _ (H.product _ _))
      ((R.totalHom P).fst _ _ ≫ R.totalι (H.product _ _) _) = _
    simp only [R.total_pair_ι, R.total_fst_ι, P.pair_fst,
      R.total_condition, R.id_comp]
  pair_snd f g := by
    apply (cancel_mono (R.totalι _ _)).mp
    simp only [R.total_comp_ι]
    change H.comp ((R.totalHom P).pair f g ≫ R.totalι _ (H.product _ _))
      ((R.totalHom P).snd _ _ ≫ R.totalι (H.product _ _) _) = _
    simp only [R.total_pair_ι, R.total_snd_ι, P.pair_snd,
      R.total_condition, R.id_comp]
  pair_eta f := by
    apply (cancel_mono (R.totalι _ _)).mp
    change (R.totalHom P).pair _ _ ≫ R.totalι _ (H.product _ _) = _
    simp only [R.total_pair_ι, R.total_comp_ι]
    change H.pair (H.comp _ ((R.totalHom P).fst _ _ ≫ R.totalι (H.product _ _) _))
      (H.comp _ ((R.totalHom P).snd _ _ ≫ R.totalι (H.product _ _) _)) = _
    simp only [R.total_fst_ι, R.total_snd_ι]
    exact P.pair_eta _

end EnrichedRestriction
end CategoricalEssentialIncompleteness
