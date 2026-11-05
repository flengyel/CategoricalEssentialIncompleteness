import CategoricalEssentialIncompleteness.V46SyntacticDerivationSuccessCarrier
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesRegular
import CategoricalEssentialIncompleteness.V46SyntacticPredicatesExtensive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! A literal Sigma-one successful-code carrier in the actual total split category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessTransport

section Option
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Regular C] [Regular D] [FinitaryExtensive C] [FinitaryExtensive D]
  (E : C ≌ D) (Q : C)

def optionIso : E.functor.obj (OptionSyntax.obj Q) ≅ OptionSyntax.obj (E.functor.obj Q) :=
  (asIso (coprodComparison E.functor (⊤_ C) Q)).symm ≪≫
    coprod.mapIso (asIso (terminalComparison E.functor)) (Iso.refl _)

@[simp, reassoc] theorem optionIso_some :
    E.functor.map (coprod.inr : Q ⟶ OptionSyntax.obj Q) ≫ (optionIso E Q).hom = coprod.inr := by
  have hi : E.functor.map (coprod.inr : Q ⟶ OptionSyntax.obj Q) ≫
      (asIso (coprodComparison E.functor (⊤_ C) Q)).inv = coprod.inr := by
    apply (cancel_mono (asIso (coprodComparison E.functor (⊤_ C) Q)).hom).mp
    simp [Category.assoc, coprodComparison]
  simp only [optionIso, Iso.trans_hom, Iso.symm_hom, coprod.mapIso_hom, Iso.refl_hom]
  rw [← Category.assoc, hi]
  simp

@[simp, reassoc] theorem optionIso_some_inv :
    (coprod.inr : E.functor.obj Q ⟶ OptionSyntax.obj (E.functor.obj Q)) ≫
      (optionIso E Q).inv = E.functor.map (coprod.inr : Q ⟶ OptionSyntax.obj Q) := by
  have he := congrArg (fun k => k ≫ (optionIso E Q).inv) (optionIso_some E Q)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using he.symm

def inverseValidator {W F : D} (v : W ⟶ OptionSyntax.obj F) :
    E.inverse.obj W ⟶ OptionSyntax.obj (E.inverse.obj F) :=
  E.inverse.map v ≫ (optionIso E.symm F).hom

def mappedOptionCounit (F : D) :
    E.functor.obj (OptionSyntax.obj (E.inverse.obj F)) ≅ OptionSyntax.obj F :=
  E.functor.mapIso (optionIso E.symm F).symm ≪≫ E.counitIso.app (OptionSyntax.obj F)

theorem inverseValidator_counit {W F : D} (v : W ⟶ OptionSyntax.obj F) :
    E.functor.map (inverseValidator E v) ≫ (mappedOptionCounit E F).hom =
      E.counitIso.hom.app W ≫ v := by
  let m := optionIso E.symm F
  have hm : E.functor.map m.hom ≫ E.functor.map m.inv = 𝟙 _ := by
    rw [← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id]
  change E.functor.map (E.inverse.map v ≫ m.hom) ≫
    (E.functor.map m.inv ≫ E.counitIso.hom.app (OptionSyntax.obj F)) = _
  rw [E.functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (E.functor.map m.hom) (E.functor.map m.inv), hm, Category.id_comp]
  simpa only [Functor.comp_map, Functor.id_map] using E.counitIso.hom.naturality v

theorem some_mappedOptionCounit (F : D) :
    E.functor.map (coprod.inr : E.inverse.obj F ⟶ OptionSyntax.obj (E.inverse.obj F)) ≫
      (mappedOptionCounit E F).hom =
      E.counitIso.hom.app F ≫ (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  let m := optionIso E.symm F
  have hs : (coprod.inr : E.inverse.obj F ⟶ OptionSyntax.obj (E.inverse.obj F)) ≫ m.inv =
      E.inverse.map (coprod.inr : F ⟶ OptionSyntax.obj F) := optionIso_some_inv E.symm F
  change E.functor.map (coprod.inr : E.inverse.obj F ⟶ OptionSyntax.obj (E.inverse.obj F)) ≫
    (E.functor.map m.inv ≫ E.counitIso.hom.app (OptionSyntax.obj F)) = _
  rw [← Category.assoc, ← E.functor.map_comp, hs]
  simpa only [Functor.comp_map, Functor.id_map] using
    E.counitIso.hom.naturality (coprod.inr : F ⟶ OptionSyntax.obj F)

end Option

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessTransport

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessTransport
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {W F : TotalSplit T}
  (v : W ⟶ OptionSyntax.obj F)

def predicateValidator :
    @Quiver.Hom (PredicateCategory T) inferInstance
      ((predicateEquivalence T).inverse.obj W)
      (OptionSyntax.obj ((predicateEquivalence T).inverse.obj F)) :=
  inverseValidator (predicateEquivalence T) v

def carrier : Carrier := SuccessCarrier.carrier (predicateValidator T v)

def codeObject : TotalSplit T := (predicateEquivalence T).functor.obj (carrier T v)

def conclusion : codeObject T v ⟶ F :=
  (predicateEquivalence T).functor.map
      (representedArrow T (SuccessCarrier.conclusion (predicateValidator T v))) ≫
    (predicateEquivalence T).counitIso.hom.app F

def inclusion : codeObject T v ⟶ W :=
  (predicateEquivalence T).functor.map
      (representedArrow T (SuccessCarrier.inclusion (predicateValidator T v))) ≫
    (predicateEquivalence T).counitIso.hom.app W

def optionCounit :
    (predicateEquivalence T).functor.obj
      (OptionSyntax.obj ((predicateEquivalence T).inverse.obj F)) ≅ OptionSyntax.obj F :=
  mappedOptionCounit (predicateEquivalence T) F

theorem validator_optionCounit :
    (predicateEquivalence T).functor.map (predicateValidator T v) ≫
      (optionCounit T (F := F)).hom = (predicateEquivalence T).counitIso.hom.app W ≫ v := by
  exact inverseValidator_counit (predicateEquivalence T) v

theorem some_optionCounit :
    (predicateEquivalence T).functor.map
        (coprod.inr : (predicateEquivalence T).inverse.obj F ⟶
          OptionSyntax.obj ((predicateEquivalence T).inverse.obj F)) ≫
      (optionCounit T (F := F)).hom =
      (predicateEquivalence T).counitIso.hom.app F ≫ (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  exact some_mappedOptionCounit (predicateEquivalence T) F

theorem isPullback : IsPullback (inclusion T v) (conclusion T v) v
    (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  let u := predicateValidator T v
  let : IsIso (SuccessCarrier.comparison u) := SuccessCarrier.comparison_isIso u
  have hp : IsPullback (representedArrow T (SuccessCarrier.inclusion u))
      (representedArrow T (SuccessCarrier.conclusion u)) u coprod.inr :=
    IsPullback.of_iso_pullback ⟨SuccessCarrier.square u⟩
      (asIso (SuccessCarrier.comparison u)) (by simp [SuccessCarrier.comparison])
      (by simp [SuccessCarrier.comparison])
  have hm := hp.map (predicateEquivalence T).functor
  apply hm.of_iso (Iso.refl _) ((predicateEquivalence T).counitIso.app W)
    ((predicateEquivalence T).counitIso.app F) (optionCounit T (F := F))
  · simp [inclusion, u]
  · simp [conclusion, u]
  · exact validator_optionCounit T v
  · exact some_optionCounit T (F := F)

def overIso : Over.mk (conclusion T v) ≅
    (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v) :=
  Over.isoMk (isPullback T v).isoPullback (by simp)

@[simp, reassoc] theorem overIso_tree :
    (overIso T v).hom.left ≫ pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) =
      inclusion T v := by simp [overIso]

def algebra (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ⟶
      (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) :
    Endofunctor.Algebra H where
  a := Over.mk (conclusion T v)
  str := H.map (overIso T v).hom ≫ α ≫ (overIso T v).inv

def algebraIso (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ⟶
      (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) :
    algebra T v H α ≅ Endofunctor.Algebra.mk _ α :=
  Endofunctor.Algebra.isoMk (overIso T v) (by simp [algebra, Category.assoc])

theorem algebra_tree (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ⟶
      (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) :
    (algebra T v H α).str.left ≫ inclusion T v =
      (H.map (overIso T v).hom).left ≫ α.left ≫
        pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) := by
  have hi : (overIso T v).inv.left ≫ inclusion T v =
      pullback.fst v (coprod.inr : F ⟶ OptionSyntax.obj F) := by
    rw [← overIso_tree T v, ← Category.assoc]
    simp
  simp only [algebra, Over.comp_left, Category.assoc, hi]

def initial (H : Over F ⥤ Over F)
    (α : H.obj ((Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v)) ⟶
      (Over.pullback (coprod.inr : F ⟶ OptionSyntax.obj F)).obj (Over.mk v))
    (h : IsInitial (Endofunctor.Algebra.mk _ α)) : IsInitial (algebra T v H α) :=
  h.ofIso (algebraIso T v H α).symm

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.SuccessTransport
