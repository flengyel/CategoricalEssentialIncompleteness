/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSentenceRanges
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # The literal sentence idempotent represents total-split sentence images -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.TotalSentenceImages
namespace Transport
universe v₁ v₂ u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Regular C] [Regular D] (E : C ≌ D) {P Fm S : D}

def inversePullbackIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    E.inverse.obj (pullback c j) ≅ pullback (E.inverse.map c) (E.inverse.map j) :=
  (E.inverse.map_isPullback (IsPullback.of_hasPullback c j)).isoPullback

def sentencePullbackIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    pullback c j ≅ E.functor.obj (pullback (E.inverse.map c) (E.inverse.map j)) :=
  (E.counitIso.app (pullback c j)).symm ≪≫ E.functor.mapIso (inversePullbackIso E c j)

@[reassoc] theorem sentencePullbackIso_snd (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sentencePullbackIso E c j).hom ≫
      E.functor.map (pullback.snd (E.inverse.map c) (E.inverse.map j)) ≫
      (E.counitIso.app S).hom = pullback.snd c j := by
  simp only [sentencePullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  have hi : (inversePullbackIso E c j).hom ≫
      pullback.snd (E.inverse.map c) (E.inverse.map j) = E.inverse.map (pullback.snd c j) :=
    (E.inverse.map_isPullback (IsPullback.of_hasPullback c j)).isoPullback_hom_snd
  have hn : E.functor.map (E.inverse.map (pullback.snd c j)) ≫ (E.counitIso.app S).hom =
      (E.counitIso.app (pullback c j)).hom ≫ pullback.snd c j := by
    simpa only [Functor.comp_map, Functor.id_map, Iso.app_hom] using
      E.counitIso.hom.naturality (pullback.snd c j)
  rw [← E.functor.map_comp_assoc, hi, hn]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def sourceImageE (c : P ⟶ Fm) (j : S ⟶ Fm) :
    pullback c j ⟶ E.functor.obj (image (pullback.snd (E.inverse.map c) (E.inverse.map j))) :=
  (sentencePullbackIso E c j).hom ≫
    E.functor.map (factorThruImage (pullback.snd (E.inverse.map c) (E.inverse.map j)))

def sourceImageM (c : P ⟶ Fm) (j : S ⟶ Fm) :
    E.functor.obj (image (pullback.snd (E.inverse.map c) (E.inverse.map j))) ⟶ S :=
  E.functor.map (image.ι (pullback.snd (E.inverse.map c) (E.inverse.map j))) ≫
    (E.counitIso.app S).hom

instance sourceImageE_strongEpi (c : P ⟶ Fm) (j : S ⟶ Fm) :
    StrongEpi (sourceImageE E c j) := by unfold sourceImageE; infer_instance

omit [Regular D] in
instance sourceImageM_mono (c : P ⟶ Fm) (j : S ⟶ Fm) : Mono (sourceImageM E c j) := by
  unfold sourceImageM
  infer_instance

@[reassoc] theorem sourceImage_fac (c : P ⟶ Fm) (j : S ⟶ Fm) :
    sourceImageE E c j ≫ sourceImageM E c j = pullback.snd c j := by
  unfold sourceImageE sourceImageM
  rw [Category.assoc, ← E.functor.map_comp_assoc, image.fac]
  exact sentencePullbackIso_snd E c j

/-- An actual strong epi/mono factorization identifies the source-chart
sentence image with the target image, including its inclusion triangle. -/
def sourceSentenceImageIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    E.functor.obj (image (pullback.snd (E.inverse.map c) (E.inverse.map j))) ≅
      image (pullback.snd c j) :=
  image.isoStrongEpiMono (sourceImageE E c j) (sourceImageM E c j) (sourceImage_fac E c j)

@[reassoc] theorem sourceSentenceImageIso_over (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sourceSentenceImageIso E c j).hom ≫ image.ι (pullback.snd c j) =
      E.functor.map (image.ι (pullback.snd (E.inverse.map c) (E.inverse.map j))) ≫
        (E.counitIso.app S).hom :=
  image.isoStrongEpiMono_hom_comp_ι
    (sourceImageE E c j) (sourceImageM E c j) (sourceImage_fac E c j)

end Transport

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {P Fm S : TotalSplit T}
local notation "E" => predicateEquivalence T

/-- The formula and sentence coordinates are the actual inverse
 equivalence chart, not an assumed identity on chosen pullback codes. -/
def sourceConclusion (c : P ⟶ Fm) :
    (E).inverse.obj P ⟶ (E).inverse.obj Fm := (E).inverse.map c

def sourceSentence (j : S ⟶ Fm) :
    (E).inverse.obj S ⟶ (E).inverse.obj Fm := (E).inverse.map j

instance sourceSentence_mono (j : S ⟶ Fm) [Mono j] : Mono (sourceSentence T j) := by
  unfold sourceSentence
  infer_instance

def inversePullbackIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (E).inverse.obj (pullback c j) ≅ pullback (sourceConclusion T c) (sourceSentence T j) :=
  Transport.inversePullbackIso (E) c j

def sentencePullbackIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    pullback c j ≅ (E).functor.obj (pullback (sourceConclusion T c) (sourceSentence T j)) :=
  Transport.sentencePullbackIso (E) c j

@[reassoc] theorem sentencePullbackIso_snd (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sentencePullbackIso T c j).hom ≫
      (E).functor.map (pullback.snd (sourceConclusion T c) (sourceSentence T j)) ≫
      ((E).counitIso.app S).hom = pullback.snd c j :=
  Transport.sentencePullbackIso_snd (E) c j

def sourceSentenceImageIso (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (E).functor.obj (image (pullback.snd (sourceConclusion T c) (sourceSentence T j))) ≅
      image (pullback.snd c j) :=
  Transport.sourceSentenceImageIso (E) c j

@[reassoc] theorem sourceSentenceImageIso_over (c : P ⟶ Fm) (j : S ⟶ Fm) :
    (sourceSentenceImageIso T c j).hom ≫ image.ι (pullback.snd c j) =
      (E).functor.map (image.ι
        (pullback.snd (sourceConclusion T c) (sourceSentence T j))) ≫
      ((E).counitIso.app S).hom :=
  Transport.sourceSentenceImageIso_over (E) c j

def sentencePredicate (c : P ⟶ Fm) (j : S ⟶ Fm) : Carrier :=
  SyntacticSentenceImages.programTheoryCarrier T (sourceConclusion T c) (sourceSentence T j)

def sentenceIdem (c : P ⟶ Fm) (j : S ⟶ Fm) : Idem (omegaObject T) :=
  predicateIdem T (sentencePredicate T c j)

/-- The splitting of [Sent(z) ∧ ∃p G_e(p,z)]_T represents the actual
sentence image in Tot(Split(S_T)), for arbitrary total arrows. -/
def sentenceSplittingIso (c : P ⟶ Fm) (j : S ⟶ Fm) [Mono j] :
    interpretedObject T (sentencePredicate T c j) ≅ image (pullback.snd c j) :=
  SyntacticSentenceImages.programTheorySplittingIso T
    (sourceConclusion T c) (sourceSentence T j) ≪≫ sourceSentenceImageIso T c j

end CategoricalEssentialIncompleteness.V46.TotalSentenceImages
