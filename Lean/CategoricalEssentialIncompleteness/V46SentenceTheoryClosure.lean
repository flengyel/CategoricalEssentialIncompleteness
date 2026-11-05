/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The sentence part of a generated theory is itself a sentence theory -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {V F L S A A' B : D}

/-- Replacing the nonlogical axiom objects by any axioms already in a
closed formula object preserves its closure. The unary and binary rules
are unchanged; only the nullary algebra operation is replaced. -/
theorem firstOrder_closed_reaxiomatize (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (axioms' : A' ⟶ S)
    (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F) (m : B ⟶ F)
    (hm : ClosedUnder (firstOrderRules logical sentence axioms all imp).inference m)
    (a' : A' ⟶ B) (ha' : a' ≫ m = axioms' ≫ sentence) :
    ClosedUnder (firstOrderRules logical sentence axioms' all imp).inference m := by
  obtain ⟨α⟩ := hm
  let R := firstOrderRules logical sentence axioms all imp
  let R' := firstOrderRules logical sentence axioms' all imp
  let Q := Over.mk m
  obtain ⟨a, ha⟩ := R.closed_contains_nullary m α
  let al : L ⟶ B := coprod.inl ≫ a
  have hl : al ≫ m = logical := by
    simp only [al, Category.assoc, ha]
    change coprod.inl ≫ coprod.desc logical (axioms ≫ sentence) = logical
    exact coprod.inl_desc _ _
  let step : ∀ i : Fin 3, R'.ruleObject Q i ⟶ B :=
    Fin.cases (pullback.fst _ _ ≫ coprod.desc al a')
      (Fin.cases (Sigma.ι (R.ruleObject Q) 1 ≫ α.left)
        (Fin.cases (Sigma.ι (R.ruleObject Q) 2 ≫ α.left) (fun i => Fin.elim0 i)))
  have hstep (i : Fin 3) : step i ≫ m = R'.ruleConclusion Q i := by
    fin_cases i
    · change (pullback.fst _ _ ≫ coprod.desc al a') ≫ m =
        pullback.fst _ _ ≫ coprod.desc logical (axioms' ≫ sentence)
      rw [Category.assoc]
      congr 1
      apply coprod.hom_ext <;> simp [hl, ha']
    · have h := congrArg (fun f => Sigma.ι (R.ruleObject Q) 1 ≫ f) (Over.w α)
      change Sigma.ι (R.ruleObject Q) 1 ≫ α.left ≫ m =
        Sigma.ι (R.ruleObject Q) 1 ≫ Sigma.desc (R.ruleConclusion Q) at h
      change (Sigma.ι (R.ruleObject Q) 1 ≫ α.left) ≫ m = R.ruleConclusion Q 1
      simpa only [Category.assoc, Sigma.ι_comp_desc] using h
    · have h := congrArg (fun f => Sigma.ι (R.ruleObject Q) 2 ≫ f) (Over.w α)
      change Sigma.ι (R.ruleObject Q) 2 ≫ α.left ≫ m =
        Sigma.ι (R.ruleObject Q) 2 ≫ Sigma.desc (R.ruleConclusion Q) at h
      change (Sigma.ι (R.ruleObject Q) 2 ≫ α.left) ≫ m = R.ruleConclusion Q 2
      simpa only [Category.assoc, Sigma.ι_comp_desc] using h
  refine ⟨Over.homMk (Sigma.desc step) ?_⟩
  change Sigma.desc step ≫ m = Sigma.desc (R'.ruleConclusion Q)
  apply Sigma.hom_ext
  intro i
  simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using hstep i

/-- A generated sentence conclusion is included in the formula image,
with its original formula coordinate. -/
def sentenceImageToFormula {P : D} (c : P ⟶ F) (sentence : S ⟶ F) :
    image (pullback.snd c sentence) ⟶ image c :=
  (sentenceImageIso c sentence).inv ≫ pullback.fst (image.ι c) sentence

omit [HasFiniteCoproducts D] in
@[reassoc] theorem sentenceImageToFormula_over {P : D} (c : P ⟶ F)
    (sentence : S ⟶ F) :
    sentenceImageToFormula c sentence ≫ image.ι c =
      image.ι (pullback.snd c sentence) ≫ sentence := by
  unfold sentenceImageToFormula
  rw [Category.assoc, pullback.condition]
  have hi : (sentenceImageIso c sentence).inv ≫ pullback.snd (image.ι c) sentence =
      image.ι (pullback.snd c sentence) := by
    apply (cancel_epi (sentenceImageIso c sentence).hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (sentenceImageIso_hom_ι c sentence).symm
  simpa only [Category.assoc] using congrArg (fun f => f ≫ sentence) hi

/-- Generating once more from the generated sentence image yields no
new sentences. This is the sentence-theory closure assertion, rather
than merely monotonicity of the sentence pullback. -/
theorem firstOrder_generated_sentence_closed (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P)
    (P' : Endofunctor.Algebra
      (firstOrderRules logical sentence (image.ι (pullback.snd P.a.hom sentence))
        all imp).inference) (hP' : IsInitial P') :
    ∃ w : pullback P'.a.hom sentence ⟶ image (pullback.snd P.a.hom sentence),
      w ≫ image.ι (pullback.snd P.a.hom sentence) = pullback.snd P'.a.hom sentence := by
  have hc := (firstOrder_least_image logical sentence axioms all imp P hP).1
  have hc' := firstOrder_closed_reaxiomatize logical sentence axioms
    (image.ι (pullback.snd P.a.hom sentence)) all imp (image.ι P.a.hom) hc
    (sentenceImageToFormula P.a.hom sentence)
    (sentenceImageToFormula_over P.a.hom sentence)
  obtain ⟨f, hf⟩ := (firstOrder_least_image logical sentence
    (image.ι (pullback.snd P.a.hom sentence)) all imp P' hP').2
      (image.ι P.a.hom) hc'
  let q : P'.a.left ⟶ image P.a.hom := factorThruImage P'.a.hom ≫ f
  have hq : q ≫ image.ι P.a.hom = P'.a.hom := by
    rw [Category.assoc, hf, image.fac]
  have hw : (pullback.fst P'.a.hom sentence ≫ q) ≫ image.ι P.a.hom =
      pullback.snd P'.a.hom sentence ≫ sentence := by
    rw [Category.assoc, hq, pullback.condition]
  refine ⟨pullback.lift (pullback.fst P'.a.hom sentence ≫ q)
    (pullback.snd P'.a.hom sentence) hw ≫ (sentenceImageIso P.a.hom sentence).hom, ?_⟩
  rw [Category.assoc, sentenceImageIso_hom_ι, pullback.lift_snd]

/-- Any sentence theory containing the axioms contains the generated
sentence image. Its theory condition is the factorization of its own
sentence-conclusion morphism through the given sentence subobject. -/
theorem firstOrder_generated_sentence_least (logical : L ⟶ F) (sentence : S ⟶ F)
    (axioms : A ⟶ S) (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
    (P : Endofunctor.Algebra (firstOrderRules logical sentence axioms all imp).inference)
    (hP : IsInitial P) {U : D} (m : U ⟶ S) [Mono m]
    (P' : Endofunctor.Algebra (firstOrderRules logical sentence m all imp).inference)
    (k : A ⟶ U) (hk : k ≫ m = axioms)
    (w : pullback P'.a.hom sentence ⟶ U)
    (hw : w ≫ m = pullback.snd P'.a.hom sentence) :
    imageSubobject (pullback.snd P.a.hom sentence) ≤ Subobject.mk m := by
  apply le_trans (firstOrder_sentence_image_monotone logical sentence axioms m all imp
    k hk P hP P')
  exact imageSubobject_le_mk m (pullback.snd P'.a.hom sentence) w hw

end CategoricalEssentialIncompleteness.V46
