/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RangeFunctor
import CategoricalEssentialIncompleteness.RestrictionSplitting
import CategoricalEssentialIncompleteness.V46SplitCoproducts

/-! # Extension to the restriction splitting by chosen target splittings -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (HasZeroMorphisms zero_comp comp_zero)
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts

namespace CategoricalEssentialIncompleteness.LocalConnectedness.V46

variable {R : Type u₁} {A : Type u₂} [Category.{v₁} R] [Category.{v₂} A]
  [RestrictionCategory R] [RestrictionCategory A]
  [Ranges R] [Ranges A]
  [CoprodStruct R] [CategoryTheory.HasCoproducts R]
  [CoprodStruct A] [CategoryTheory.HasCoproducts A]
  [HasZeroMorphisms R] [HasZeroMorphisms A]

/-- The chosen splitting of the image of one source restriction idempotent. -/
structure TargetSplitting (F : RangeFunctor R A) (X : SplitObject R) where
  carrier : A
  inclusion : carrier ⟶ F.toFunctor.obj X.base
  retraction : F.toFunctor.obj X.base ⟶ carrier
  total : isTotal inclusion
  section_eq : inclusion ≫ retraction = 𝟙 carrier
  support_eq : retraction ≫ inclusion = F.toFunctor.map X.domain.hom

/-- A split target supplies the chosen splittings used by the extension. -/
def targetSplitting (F : RangeFunctor R A) [Splits A] (X : SplitObject R) :
    TargetSplitting F X := by
  let h := Splits.splitting (F.mapIdem X.domain)
  let Z := Classical.choose h
  let hZ := Classical.choose_spec h
  let m := Classical.choose hZ
  let hm := Classical.choose_spec hZ
  let r := Classical.choose hm
  let hr := Classical.choose_spec hm
  exact ⟨Z, m, r, hr.1, hr.2.1, hr.2.2⟩

/-- Choose the identity splitting on every included source object. -/
def normalizedTargetSplitting (F : RangeFunctor R A) [Splits A]
    (X : SplitObject R) : TargetSplitting F X := by
  classical
  exact if h : X.domain = ⊤ then
    { carrier := F.toFunctor.obj X.base
      inclusion := 𝟙 _
      retraction := 𝟙 _
      total := rst_id _
      section_eq := Category.id_comp _
      support_eq := by rw [h, Idem.top_hom, F.toFunctor.map_id, Category.id_comp] }
  else targetSplitting F X

theorem normalizedTargetSplitting_eq_top (F : RangeFunctor R A) [Splits A]
    (X : SplitObject R) (h : X.domain = ⊤) :
    normalizedTargetSplitting F X =
      { carrier := F.toFunctor.obj X.base
        inclusion := 𝟙 _
        retraction := 𝟙 _
        total := rst_id _
        section_eq := Category.id_comp _
        support_eq := by rw [h, Idem.top_hom, F.toFunctor.map_id, Category.id_comp] } := by
  unfold normalizedTargetSplitting
  exact dite_eq_left h

@[simp] theorem normalizedTargetSplitting_carrier (F : RangeFunctor R A) [Splits A]
    (X : R) :
    (normalizedTargetSplitting F ((splittingInclusion (C := R)).obj X)).carrier =
      F.toFunctor.obj X := by
  simp only [normalizedTargetSplitting, splittingInclusion]
  split_ifs <;> simp_all

variable (F : RangeFunctor R A) (s : ∀ X : SplitObject R, TargetSplitting F X)

/-- The extension sends `f` to `m_e ≫ F(f) ≫ r_d`. -/
def chosenSplitExtension : SplitObject R ⥤ A where
  obj X := (s X).carrier
  map {X Y} f := (s X).inclusion ≫ F.toFunctor.map f.hom ≫ (s Y).retraction
  map_id X := by
    change (s X).inclusion ≫ F.toFunctor.map X.domain.hom ≫ (s X).retraction = _
    rw [← (s X).support_eq]
    simp only [← Category.assoc, (s X).section_eq, Category.id_comp]
  map_comp {X Y Z} f g := by
    change (s X).inclusion ≫ F.toFunctor.map (f.hom ≫ g.hom) ≫ (s Z).retraction = _
    rw [F.toFunctor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (s Y).retraction, (s Y).support_eq]
    have h : F.toFunctor.map Y.domain.hom ≫ F.toFunctor.map g.hom =
        F.toFunctor.map g.hom := by rw [← F.toFunctor.map_comp, g.source]
    rw [← Category.assoc (F.toFunctor.map Y.domain.hom), h]

/-- The chosen extension preserves the restriction operation. -/
theorem chosenSplitExtension_restrict {X Y : SplitObject R} (f : X ⟶ Y) :
    (chosenSplitExtension F s).map (rst f) =
      rst ((chosenSplitExtension F s).map f) := by
  change (s X).inclusion ≫ F.toFunctor.map (rst f.hom) ≫ (s X).retraction =
    rst ((s X).inclusion ≫ F.toFunctor.map f.hom ≫ (s Y).retraction)
  rw [F.map_restrict]
  have htarget : F.toFunctor.map f.hom ≫ F.toFunctor.map Y.domain.hom =
      F.toFunctor.map f.hom := by rw [← F.toFunctor.map_comp, f.target]
  calc
    _ = (rst ((s X).inclusion ≫ F.toFunctor.map f.hom) ≫
        (s X).inclusion) ≫ (s X).retraction := by rw [rst_comp, Category.assoc]
    _ = rst ((s X).inclusion ≫ F.toFunctor.map f.hom) := by
      rw [Category.assoc, (s X).section_eq, Category.comp_id]
    _ = rst (((s X).inclusion ≫ F.toFunctor.map f.hom ≫
        (s Y).retraction) ≫ (s Y).inclusion) := by
      simp only [Category.assoc, (s Y).support_eq, htarget]
    _ = _ := rst_comp_of_isTotal _ (s Y).total

@[simp] theorem chosenSplitExtension_zero (X Y : SplitObject R) :
    (chosenSplitExtension F s).map (0 : X ⟶ Y) = 0 := by
  change (s X).inclusion ≫ F.toFunctor.map (0 : X.base ⟶ Y.base) ≫
    (s Y).retraction = 0
  rw [F.map_zero, zero_comp, comp_zero]

/-- The extension preserves ranges. The proof uses the range agreement law
and the support equation on a morphism of the restriction splitting. -/
theorem chosenSplitExtension_range {X Y : SplitObject R} (f : X ⟶ Y) :
    (chosenSplitExtension F s).map (Ranges.range f).hom =
      (Ranges.range ((chosenSplitExtension F s).map f)).hom := by
  let E := chosenSplitExtension F s
  let p : Idem (E.obj Y) := ⟨E.map (Ranges.range f).hom, by
    rw [← chosenSplitExtension_restrict F s, (Ranges.range f).restriction]⟩
  have hp : E.map f ≫ p.hom = E.map f := by
    change E.map f ≫ E.map (Ranges.range f).hom = E.map f
    rw [← E.map_comp, Ranges.receives]
  have hlower : Ranges.range (E.map f) ≤ p := Ranges.least _ p hp
  have hsource : F.toFunctor.map X.domain.hom ≫ F.toFunctor.map f.hom =
      F.toFunctor.map f.hom := by rw [← F.toFunctor.map_comp, f.source]
  have hsupport : (s X).retraction ≫ E.map f =
      F.toFunctor.map f.hom ≫ (s Y).retraction := by
    change (s X).retraction ≫ ((s X).inclusion ≫
      F.toFunctor.map f.hom ≫ (s Y).retraction) = _
    rw [← Category.assoc, (s X).support_eq, ← Category.assoc, hsource]
  have heq : F.toFunctor.map f.hom ≫
      ((s Y).retraction ≫ (Ranges.range (E.map f)).hom) =
      F.toFunctor.map f.hom ≫ (s Y).retraction := by
    rw [← Category.assoc, ← hsupport, Category.assoc, Ranges.receives]
  have heq' := Ranges.agreement (F.toFunctor.map f.hom)
    ((s Y).retraction ≫ (Ranges.range (E.map f)).hom) (s Y).retraction heq
  have hupper : p ≤ Ranges.range (E.map f) := by
    change E.map (Ranges.range f).hom ≫ (Ranges.range (E.map f)).hom =
      E.map (Ranges.range f).hom
    change ((s Y).inclusion ≫ F.toFunctor.map (Ranges.range f.hom).hom ≫
      (s Y).retraction) ≫ (Ranges.range (E.map f)).hom =
        (s Y).inclusion ≫ F.toFunctor.map (Ranges.range f.hom).hom ≫ (s Y).retraction
    rw [F.map_range]
    simpa only [Category.assoc] using congrArg (fun k => (s Y).inclusion ≫ k) heq'
  exact congrArg Idem.hom (le_antisymm hupper hlower)

/-- On the included source category, the chosen-splitting extension is
naturally isomorphic to the original functor. Identity splittings make
these components identities. -/
def chosenSplitExtensionInclusionIso :
    splittingInclusion (C := R) ⋙ chosenSplitExtension F s ≅ F.toFunctor := by
  refine NatIso.ofComponents
    (fun X =>
      { hom := (s ((splittingInclusion (C := R)).obj X)).inclusion
        inv := (s ((splittingInclusion (C := R)).obj X)).retraction
        hom_inv_id := (s ((splittingInclusion (C := R)).obj X)).section_eq
        inv_hom_id := by
          rw [(s ((splittingInclusion (C := R)).obj X)).support_eq]
          exact F.toFunctor.map_id X }) ?_
  intro X Y f
  change ((s ((splittingInclusion (C := R)).obj X)).inclusion ≫
    F.toFunctor.map f ≫ (s ((splittingInclusion (C := R)).obj Y)).retraction) ≫
      (s ((splittingInclusion (C := R)).obj Y)).inclusion = _
  rw [Category.assoc, Category.assoc,
    (s ((splittingInclusion (C := R)).obj Y)).support_eq]
  change (s ((splittingInclusion (C := R)).obj X)).inclusion ≫
    F.toFunctor.map f ≫ F.toFunctor.map (𝟙 Y) = _
  rw [F.toFunctor.map_id,
    Category.comp_id]

theorem inclusion_support (X : SplitObject R) :
    (s X).inclusion ≫ F.toFunctor.map X.domain.hom = (s X).inclusion := by
  rw [← (s X).support_eq, ← Category.assoc, (s X).section_eq, Category.id_comp]

theorem support_retraction (X : SplitObject R) :
    F.toFunctor.map X.domain.hom ≫ (s X).retraction = (s X).retraction := by
  rw [← (s X).support_eq, Category.assoc, (s X).section_eq, Category.comp_id]

section Coproducts

variable [RestrictionCoproducts R] [RestrictionCoproducts A]

/-- The binary coproduct object in the restriction splitting. -/
def splitCoproductObject (X Y : SplitObject R) : SplitObject R :=
  ⟨coprod X.base Y.base, X.domain.sum Y.domain⟩

/-- The comparison between the coproduct of the chosen splitting objects
and the chosen splitting of the source coproduct. -/
def chosenSplitCoproductIso (X Y : SplitObject R) :
    coprod ((chosenSplitExtension F s).obj X) ((chosenSplitExtension F s).obj Y) ≅
      (chosenSplitExtension F s).obj (splitCoproductObject X Y) where
  hom := coprod_map (s X).inclusion (s Y).inclusion ≫
    (F.comparison X.base Y.base).hom ≫ (s (splitCoproductObject X Y)).retraction
  inv := (s (splitCoproductObject X Y)).inclusion ≫
    (F.comparison X.base Y.base).inv ≫ coprod_map (s X).retraction (s Y).retraction
  hom_inv_id := by
    dsimp only [chosenSplitExtension]
    simp only [Category.assoc]
    rw [← Category.assoc (s (splitCoproductObject X Y)).retraction,
      (s (splitCoproductObject X Y)).support_eq]
    change coprod_map (s X).inclusion (s Y).inclusion ≫
      ((F.comparison X.base Y.base).hom ≫
        F.toFunctor.map (coprod_map X.domain.hom Y.domain.hom) ≫
        (F.comparison X.base Y.base).inv ≫
        coprod_map (s X).retraction (s Y).retraction) = _
    rw [← Category.assoc (F.comparison X.base Y.base).hom,
      F.comparison_sum]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, coprod_comp, inclusion_support F s X,
      inclusion_support F s Y, coprod_comp, (s X).section_eq, (s Y).section_eq,
      coprod_id]
  inv_hom_id := by
    dsimp only [chosenSplitExtension]
    simp only [Category.assoc]
    rw [← Category.assoc (coprod_map (s X).retraction (s Y).retraction),
      coprod_comp, (s X).support_eq, (s Y).support_eq]
    rw [← Category.assoc (F.comparison X.base Y.base).inv,
      F.comparison_inv_sum]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change (s (splitCoproductObject X Y)).inclusion ≫
      F.toFunctor.map (splitCoproductObject X Y).domain.hom ≫
      (s (splitCoproductObject X Y)).retraction = _
    rw [← Category.assoc, inclusion_support F s, (s (splitCoproductObject X Y)).section_eq]

omit [RestrictionCoproducts A] in
/-- The explicit splitting comparison is the canonical coproduct
comparison determined by the two injections. -/
theorem chosenSplitCoproductIso_canonical (X Y : SplitObject R) :
    coproductComparison (chosenSplitExtension F s) X Y =
      (chosenSplitCoproductIso F s X Y).hom := by
  apply hom_ext
  · rw [coproductComparison, i0_copair]
    change (s X).inclusion ≫ F.toFunctor.map (X.domain.hom ≫ i0 X.base Y.base) ≫
      (s (splitCoproductObject X Y)).retraction =
      i0 _ _ ≫ (coprod_map (s X).inclusion (s Y).inclusion ≫
        (F.comparison X.base Y.base).hom ≫ (s (splitCoproductObject X Y)).retraction)
    rw [F.toFunctor.map_comp]
    simp only [← Category.assoc]
    rw [inclusion_support F s X, i0_coprod_map]
    simp only [Category.assoc]
    rw [← Category.assoc (i0 _ _), F.i0_comparison]
  · rw [coproductComparison, i1_copair]
    change (s Y).inclusion ≫ F.toFunctor.map (Y.domain.hom ≫ i1 X.base Y.base) ≫
      (s (splitCoproductObject X Y)).retraction =
      i1 _ _ ≫ (coprod_map (s X).inclusion (s Y).inclusion ≫
        (F.comparison X.base Y.base).hom ≫ (s (splitCoproductObject X Y)).retraction)
    rw [F.toFunctor.map_comp]
    simp only [← Category.assoc]
    rw [inclusion_support F s Y, i1_coprod_map]
    simp only [Category.assoc]
    rw [← Category.assoc (i1 _ _), F.i1_comparison]

/-- A range functor with split target extends to the restriction
splitting, preserving restrictions, ranges, zeros and binary coproducts. -/
def chosenSplitRangeFunctor : RangeFunctor (SplitObject R) A where
  toFunctor := chosenSplitExtension F s
  map_restrict := chosenSplitExtension_restrict F s
  map_range := chosenSplitExtension_range F s
  map_zero := chosenSplitExtension_zero F s
  comparison_isIso X Y := by
    rw [chosenSplitCoproductIso_canonical F s X Y]
    infer_instance

/-- The extension with the identity splitting on source objects. -/
def splitRangeFunctor [Splits A] : RangeFunctor (SplitObject R) A :=
  chosenSplitRangeFunctor F (normalizedTargetSplitting F)

omit [RestrictionCoproducts A] in
@[simp] theorem splitRangeFunctor_obj_inclusion [Splits A] (X : R) :
    (splitRangeFunctor F).toFunctor.obj ((splittingInclusion (C := R)).obj X) =
      F.toFunctor.obj X :=
  normalizedTargetSplitting_carrier F X

omit [RestrictionCoproducts A] in
theorem splitRangeFunctor_inclusion [Splits A] :
    splittingInclusion (C := R) ⋙ (splitRangeFunctor F).toFunctor = F.toFunctor := by
  apply Functor.hext (fun X => splitRangeFunctor_obj_inclusion F X)
  intro X Y f
  change HEq
    ((normalizedTargetSplitting F (⟨X, ⊤⟩ : SplitObject R)).inclusion ≫
      F.toFunctor.map f ≫
      (normalizedTargetSplitting F (⟨Y, ⊤⟩ : SplitObject R)).retraction)
    (F.toFunctor.map f)
  rw [normalizedTargetSplitting_eq_top F (⟨X, ⊤⟩ : SplitObject R) rfl,
    normalizedTargetSplitting_eq_top F (⟨Y, ⊤⟩ : SplitObject R) rfl]
  simp


end Coproducts

end CategoricalEssentialIncompleteness.LocalConnectedness.V46
