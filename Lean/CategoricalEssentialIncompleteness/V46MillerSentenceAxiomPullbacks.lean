/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerAxiomSubobjects
import CategoricalEssentialIncompleteness.RestrictionSpans

/-! # External formula-word axioms on an actual sentence pullback

An arbitrary sentence monomorphism need not preserve scalar codes. Its
inverse is the already constructed partial inverse of a total mono.
The resulting finite-support lift returns the unique sentence point
over each formula word, and is guarded by that finite word support.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.Miller.SentenceAxiomPullbacks
variable {P : Uniform.Family}

/-- Both definedness and the value of the actual partial mono inverse. -/
theorem partialInverse_graph {X Y : Total.TotalCategory P} (s : X ⟶ Y) [Mono s] (w x : ℕ) :
    x ∈ Total.val (PartialSpans.inverse s) w ↔ w ∈ Total.val s.hom x := by
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff s.hom).mp s.property x
      (Total.val_target (PartialSpans.inverse s) w x hx))
    have hc : v ∈ Total.val (PartialSpans.inverse s ≫ s.hom) w :=
      (Total.mem_val_comp _ _ w v).mpr ⟨x,hx,hv⟩
    rw [PartialSpans.inverse_hom] at hc
    exact ((Total.mem_val_restriction (PartialSpans.inverse s) w v).mp hc).2 ▸ hv
  · intro hw
    have hc : x ∈ Total.val (s.hom ≫ PartialSpans.inverse s) x := by
      rw [PartialSpans.hom_inverse,Total.val_id]
      exact (Total.mem_supportIdentity X.obj.support x x).mpr
        ⟨Total.val_source s.hom x w hw,rfl⟩
    obtain ⟨w',hw',hx⟩ := (Total.mem_val_comp _ _ x x).mp hc
    exact Part.mem_unique hw' hw ▸ hx

variable {Fm : PredicateCategory 𝗣𝗔} {S : Total.TotalCategory P}

/-- Formula-word membership pulled back along the actual sentence map. -/
def pulledSupport (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) (Γ : Set ℕ) : Set ℕ :=
  {x | ∃ w,w ∈ Total.val s.hom x ∧ w ∈ Γ}

theorem pulledSupport_enumerable (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) :
    Uniform.Enumerable P (· ∈ pulledSupport s Γ) :=
  ((Total.graph_enumerable s.hom).and (hΓ.comp Computable.snd)).projection

def pulledIdem (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) : Idem S.obj :=
  Total.relativeIdem (pulledSupport s Γ) (pulledSupport_enumerable s Γ hΓ)
    (fun x ⟨w,hw,_⟩ => Total.val_source s.hom x w hw)

def axCarrier (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) : Total.TotalCategory P :=
  ⟨Total.subcarrier (pulledIdem s Γ hΓ)⟩

theorem axCarrier_support (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (x : ℕ) :
    x ∈ (axCarrier s Γ hΓ).obj.support ↔ ∃ w,w ∈ Total.val s.hom x ∧ w ∈ Γ := by
  change x ∈ Total.support (pulledIdem s Γ hΓ) ↔ _
  rw [pulledIdem,Total.support_relativeIdem]
  rfl

def inclusion (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) : axCarrier s Γ hΓ ⟶ S :=
  ⟨Total.into (pulledIdem s Γ hΓ),Total.into_total _⟩

theorem inclusion_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (x y : ℕ) :
    y ∈ Total.val (inclusion s Γ hΓ).hom x ↔ x ∈ (axCarrier s Γ hΓ).obj.support ∧ y=x :=
  Total.mem_val_idem (pulledIdem s Γ hΓ) x y

instance inclusion_mono (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) : Mono (inclusion s Γ hΓ) where
  right_cancellation f g he := by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (Total.into (pulledIdem s Γ hΓ))).mp
    exact congrArg (fun k => k.hom) he

theorem inclusion_word_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (x w : ℕ) :
    w ∈ Total.val (inclusion s Γ hΓ ≫ s).hom x ↔
      x ∈ (axCarrier s Γ hΓ).obj.support ∧ w ∈ Total.val s.hom x := by
  change w ∈ Total.val ((inclusion s Γ hΓ).hom ≫ s.hom) x ↔
    x ∈ (axCarrier s Γ hΓ).obj.support ∧ w ∈ Total.val s.hom x
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨y,hy,hw⟩
    obtain ⟨hx,rfl⟩ := (inclusion_graph s Γ hΓ x y).mp hy
    exact ⟨hx,hw⟩
  · rintro ⟨hx,hw⟩
    exact ⟨x,(inclusion_graph s Γ hΓ x x).mpr ⟨hx,rfl⟩,hw⟩

/-- The composite has exactly the specified word codes that are sentences. -/
theorem imageCodes_inclusion (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) :
    AxiomSubobjects.imageCodes (inclusion s Γ hΓ ≫ s) = Γ ∩ AxiomSubobjects.imageCodes s := by
  ext w
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨hs,hw⟩ := (inclusion_word_graph s Γ hΓ x w).mp hx
    obtain ⟨w',hw',hΓ'⟩ := (axCarrier_support s Γ hΓ x).mp hs
    have he : w'=w := Part.mem_unique hw' hw
    exact ⟨he ▸ hΓ',x,hw⟩
  · rintro ⟨hΓw,x,hw⟩
    exact ⟨x,(inclusion_word_graph s Γ hΓ x w).mpr
      ⟨(axCarrier_support s Γ hΓ x).mpr ⟨w,hw,hΓw⟩,hw⟩⟩

theorem imageCodes_of_sentence_codes (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
    (hΓS : Γ ⊆ AxiomSubobjects.imageCodes s) :
    AxiomSubobjects.imageCodes (inclusion s Γ hΓ ≫ s) = Γ := by
  rw [imageCodes_inclusion]
  exact Set.inter_eq_left.mpr hΓS

private theorem wordProjection_supported (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (x w : ℕ)
    (hw : w ∈ Total.val (inclusion s Γ hΓ ≫ s).hom x) :
    w ∈ Total.support (AxiomSubobjects.axiomIdem P Fm Γ hΓ) := by
  obtain ⟨hx,hs⟩ := (inclusion_word_graph s Γ hΓ x w).mp hw
  obtain ⟨w',hw',hΓ'⟩ := (axCarrier_support s Γ hΓ x).mp hx
  have hΓw : w ∈ Γ := Part.mem_unique hw' hs ▸ hΓ'
  exact (AxiomSubobjects.axCarrier_support P Fm Γ hΓ w).mpr
    ⟨hΓw,(AxiomSubobjects.mapped_support P Fm w).mp (Total.val_target s.hom x w hs)⟩

def wordProjection (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) :
    axCarrier s Γ hΓ ⟶ AxiomSubobjects.axCarrier P Fm Γ hΓ :=
  ⟨Total.intoSubcarrier (inclusion s Γ hΓ ≫ s).hom (AxiomSubobjects.axiomIdem P Fm Γ hΓ)
      (wordProjection_supported s Γ hΓ),
    Total.intoSubcarrier_total _ (inclusion s Γ hΓ ≫ s).property _ (wordProjection_supported s Γ hΓ)⟩

theorem wordProjection_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (x w : ℕ) :
    w ∈ Total.val (wordProjection s Γ hΓ).hom x ↔
      x ∈ (axCarrier s Γ hΓ).obj.support ∧ w ∈ Total.val s.hom x :=
  inclusion_word_graph s Γ hΓ x w

theorem wordProjection_square (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) :
    inclusion s Γ hΓ ≫ s = wordProjection s Γ hΓ ≫ AxiomSubobjects.axiomInclusion P Fm Γ hΓ := by
  apply WideSubcategory.hom_ext
  exact (Total.intoSubcarrier_fac (inclusion s Γ hΓ ≫ s).hom
    (AxiomSubobjects.axiomIdem P Fm Γ hΓ) (wordProjection_supported s Γ hΓ)).symm

private theorem cone_supported (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
    {Z : Total.TotalCategory P} (f : Z ⟶ S) (g : Z ⟶ AxiomSubobjects.axCarrier P Fm Γ hΓ)
    (he : f ≫ s = g ≫ AxiomSubobjects.axiomInclusion P Fm Γ hΓ)
    (z x : ℕ) (hx : x ∈ Total.val f.hom z) : x ∈ Total.support (pulledIdem s Γ hΓ) := by
  obtain ⟨w,hw⟩ := Part.dom_iff_mem.mp ((Total.total_iff s.hom).mp s.property x
    (Total.val_target f.hom z x hx))
  have hc : w ∈ Total.val (f ≫ s).hom z := (Total.mem_val_comp _ _ z w).mpr ⟨x,hx,hw⟩
  rw [he] at hc
  obtain ⟨v,_,hv⟩ := (Total.mem_val_comp _ _ z w).mp hc
  obtain ⟨hΓv,_,hevw⟩ := (AxiomSubobjects.axiomInclusion_graph P Fm Γ hΓ v w).mp hv
  exact (axCarrier_support s Γ hΓ x).mpr ⟨w,hw,hevw.symm ▸ hΓv⟩

def coneLift (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
    {Z : Total.TotalCategory P} (f : Z ⟶ S) (g : Z ⟶ AxiomSubobjects.axCarrier P Fm Γ hΓ)
    (he : f ≫ s = g ≫ AxiomSubobjects.axiomInclusion P Fm Γ hΓ) : Z ⟶ axCarrier s Γ hΓ :=
  ⟨Total.intoSubcarrier f.hom (pulledIdem s Γ hΓ) (cone_supported s Γ hΓ f g he),
    Total.intoSubcarrier_total f.hom f.property _ (cone_supported s Γ hΓ f g he)⟩

theorem coneLift_fst (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
    {Z : Total.TotalCategory P} (f : Z ⟶ S) (g : Z ⟶ AxiomSubobjects.axCarrier P Fm Γ hΓ)
    (he : f ≫ s = g ≫ AxiomSubobjects.axiomInclusion P Fm Γ hΓ) :
    coneLift s Γ hΓ f g he ≫ inclusion s Γ hΓ = f := by
  apply WideSubcategory.hom_ext
  exact Total.intoSubcarrier_fac f.hom _ (cone_supported s Γ hΓ f g he)

theorem coneLift_snd (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ))
    {Z : Total.TotalCategory P} (f : Z ⟶ S) (g : Z ⟶ AxiomSubobjects.axCarrier P Fm Γ hΓ)
    (he : f ≫ s = g ≫ AxiomSubobjects.axiomInclusion P Fm Γ hΓ) :
    coneLift s Γ hΓ f g he ≫ wordProjection s Γ hΓ = g := by
  apply (cancel_mono (AxiomSubobjects.axiomInclusion P Fm Γ hΓ)).mp
  calc
    (coneLift s Γ hΓ f g he ≫ wordProjection s Γ hΓ) ≫
        AxiomSubobjects.axiomInclusion P Fm Γ hΓ =
        (coneLift s Γ hΓ f g he ≫ inclusion s Γ hΓ) ≫ s := by
      rw [Category.assoc,← wordProjection_square,← Category.assoc]
    _ = f ≫ s := congrArg (fun k => k ≫ s) (coneLift_fst s Γ hΓ f g he)
    _ = _ := he

/-- A genuine categorical pullback, not only equality of decoded supports. -/
theorem axiomPullback (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) :
    IsPullback (inclusion s Γ hΓ) (wordProjection s Γ hΓ) s
      (AxiomSubobjects.axiomInclusion P Fm Γ hΓ) := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (wordProjection_square s Γ hΓ))
  refine PullbackCone.IsLimit.mk (wordProjection_square s Γ hΓ)
    (fun t => coneLift s Γ hΓ t.fst t.snd t.condition) ?_ ?_ ?_
  · intro t
    exact coneLift_fst s Γ hΓ t.fst t.snd t.condition
  · intro t
    exact coneLift_snd s Γ hΓ t.fst t.snd t.condition
  · intro t m hm _
    apply (cancel_mono (inclusion s Γ hΓ)).mp
    exact hm.trans (coneLift_fst s Γ hΓ t.fst t.snd t.condition).symm

def finiteFormulaInclusion (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ (Syntax.predicateFunctor P).obj Fm :=
  AxiomSubobjects.finiteIntoSentence P Fm L
    (fun w hw => AxiomSubobjects.imageCodes_sentence s w (hLS w hw))

instance finiteFormulaInclusion_mono (s : S ⟶ (Syntax.predicateFunctor P).obj Fm)
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    Mono (finiteFormulaInclusion s L hLS) :=
  AxiomSubobjects.finiteIntoSentence_mono P Fm L
    (fun w hw => AxiomSubobjects.imageCodes_sentence s w (hLS w hw))

private def finiteToSentenceValue (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    ((Syntax.predicateFunctor P).obj (finiteCarrier L)).obj ⟶ S.obj :=
  (finiteFormulaInclusion s L hLS).hom ≫ PartialSpans.inverse s

private theorem finiteToSentenceValue_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) (w x : ℕ) :
    x ∈ Total.val (finiteToSentenceValue s L hLS) w ↔ w ∈ L ∧ w ∈ Total.val s.hom x := by
  change x ∈ Total.val ((finiteFormulaInclusion s L hLS).hom ≫ PartialSpans.inverse s) w ↔ _
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨v,hv,hx⟩
    obtain ⟨hL,he⟩ := (AxiomSubobjects.finiteIntoSentence_graph P Fm L _ w v).mp hv
    subst v
    exact ⟨hL,(partialInverse_graph s w x).mp hx⟩
  · rintro ⟨hL,hw⟩
    exact ⟨w,(AxiomSubobjects.finiteIntoSentence_graph P Fm L _ w w).mpr ⟨hL,rfl⟩,
      (partialInverse_graph s w x).mpr hw⟩

def finiteToSentence (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ S :=
  ⟨finiteToSentenceValue s L hLS,(Total.total_iff _).mpr (fun w hw => by
    have hL := (AxiomSubobjects.mapped_finite_support P L w).mp hw
    obtain ⟨x,hx⟩ := hLS w hL
    exact Part.dom_iff_mem.mpr ⟨x,(finiteToSentenceValue_graph s L hLS w x).mpr ⟨hL,hx⟩⟩)⟩

theorem finiteToSentence_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) (w x : ℕ) :
    x ∈ Total.val (finiteToSentence s L hLS).hom w ↔ w ∈ L ∧ w ∈ Total.val s.hom x :=
  finiteToSentenceValue_graph s L hLS w x

theorem finiteToSentence_word (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    finiteToSentence s L hLS ≫ s = finiteFormulaInclusion s L hLS := by
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro w hw
  have hL := (AxiomSubobjects.mapped_finite_support P L w).mp hw
  obtain ⟨x,hx⟩ := hLS w hL
  have hc : w ∈ Total.val (finiteToSentence s L hLS ≫ s).hom w :=
    (Total.mem_val_comp _ _ w w).mpr
      ⟨x,(finiteToSentence_graph s L hLS w x).mpr ⟨hL,hx⟩,hx⟩
  exact (Part.eq_some_iff.mpr hc).trans
    (Part.eq_some_iff.mpr ((AxiomSubobjects.finiteIntoSentence_graph P Fm L _ w w).mpr ⟨hL,rfl⟩)).symm

instance finiteToSentence_mono (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (L : List ℕ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    Mono (finiteToSentence s L hLS) := by
  let : Mono (finiteToSentence s L hLS).hom := Total.mono_of_total_injective _
    (finiteToSentence s L hLS).property (by
      intro w w' x hx hx'
      exact Part.mem_unique ((finiteToSentence_graph s L hLS w x).mp hx).2
        ((finiteToSentence_graph s L hLS w' x).mp hx').2)
  exact ⟨fun f g he => by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (finiteToSentence s L hLS).hom).mp
    exact congrArg (fun k => k.hom) he⟩

private theorem finiteLift_supported (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s)
    (w x : ℕ) (hx : x ∈ Total.val (finiteToSentence s L hLS).hom w) :
    x ∈ Total.support (pulledIdem s Γ hΓ) := by
  obtain ⟨hL,hs⟩ := (finiteToSentence_graph s L hLS w x).mp hx
  exact (axCarrier_support s Γ hΓ x).mpr ⟨w,hs,hLΓ w hL⟩

/-- This lift returns a sentence point, not the original formula word. -/
def finiteLift (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    (Syntax.predicateFunctor P).obj (finiteCarrier L) ⟶ axCarrier s Γ hΓ :=
  ⟨Total.intoSubcarrier (finiteToSentence s L hLS).hom (pulledIdem s Γ hΓ)
      (finiteLift_supported s Γ hΓ L hLΓ hLS),
    Total.intoSubcarrier_total _ (finiteToSentence s L hLS).property _
      (finiteLift_supported s Γ hΓ L hLΓ hLS)⟩

theorem finiteLift_graph (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) (w x : ℕ) :
    x ∈ Total.val (finiteLift s Γ hΓ L hLΓ hLS).hom w ↔ w ∈ L ∧ w ∈ Total.val s.hom x :=
  finiteToSentence_graph s L hLS w x

theorem finiteLift_inclusion (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    finiteLift s Γ hΓ L hLΓ hLS ≫ inclusion s Γ hΓ = finiteToSentence s L hLS := by
  apply WideSubcategory.hom_ext
  exact Total.intoSubcarrier_fac _ _ (finiteLift_supported s Γ hΓ L hLΓ hLS)

theorem finiteLift_formula (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    finiteLift s Γ hΓ L hLΓ hLS ≫ inclusion s Γ hΓ ≫ s = finiteFormulaInclusion s L hLS := by
  rw [← Category.assoc,finiteLift_inclusion,finiteToSentence_word]

theorem finiteSubobject_le (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    Subobject.mk (finiteToSentence s L hLS) ≤ Subobject.mk (inclusion s Γ hΓ) :=
  Subobject.mk_le_mk_of_comm (finiteLift s Γ hΓ L hLΓ hLS)
    (finiteLift_inclusion s Γ hΓ L hLΓ hLS)

theorem finiteLift_wordProjection (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    finiteLift s Γ hΓ L hLΓ hLS ≫ wordProjection s Γ hΓ =
      AxiomSubobjects.finiteIntoAxioms P Fm Γ hΓ L hLΓ
        (fun w hw => AxiomSubobjects.imageCodes_sentence s w (hLS w hw)) := by
  apply (cancel_mono (AxiomSubobjects.axiomInclusion P Fm Γ hΓ)).mp
  calc
    (finiteLift s Γ hΓ L hLΓ hLS ≫ wordProjection s Γ hΓ) ≫
        AxiomSubobjects.axiomInclusion P Fm Γ hΓ =
        finiteLift s Γ hΓ L hLΓ hLS ≫ inclusion s Γ hΓ ≫ s := by
      rw [Category.assoc,← wordProjection_square]
    _ = finiteFormulaInclusion s L hLS := finiteLift_formula s Γ hΓ L hLΓ hLS
    _ = _ := (AxiomSubobjects.finiteIntoAxioms_fac P Fm Γ hΓ L hLΓ
      (fun w hw => AxiomSubobjects.imageCodes_sentence s w (hLS w hw))).symm

theorem finiteWordSubobject_le (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
    (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (· ∈ Γ)) (L : List ℕ)
    (hLΓ : ∀ w ∈ L,w ∈ Γ) (hLS : ∀ w ∈ L,w ∈ AxiomSubobjects.imageCodes s) :
    Subobject.mk (finiteFormulaInclusion s L hLS) ≤ Subobject.mk (inclusion s Γ hΓ ≫ s) :=
  Subobject.mk_le_mk_of_comm (finiteLift s Γ hΓ L hLΓ hLS)
    (finiteLift_formula s Γ hΓ L hLΓ hLS)

section GivenMono
variable (s : S ⟶ (Syntax.predicateFunctor P).obj Fm) [Mono s]
variable {B : Total.TotalCategory P} (a : B ⟶ S) [Mono a]

def givenCodes : Set ℕ := AxiomSubobjects.imageCodes (a ≫ s)

omit [Mono s] [Mono a] in
theorem givenCodes_enumerable : Uniform.Enumerable P (· ∈ givenCodes s a) :=
  AxiomSubobjects.imageCodes_enumerable (a ≫ s)

omit [Mono s] [Mono a] in
theorem givenCodes_sentence : givenCodes s a ⊆ AxiomSubobjects.imageCodes s := by
  rintro w ⟨b,hb⟩
  obtain ⟨x,_,hx⟩ := (Total.mem_val_comp _ _ b w).mp hb
  exact ⟨x,hx⟩

omit [Mono s] [Mono a] in
theorem givenCodes_recovered :
    AxiomSubobjects.imageCodes
      (inclusion s (givenCodes s a) (givenCodes_enumerable s a) ≫ s) = givenCodes s a :=
  imageCodes_of_sentence_codes s (givenCodes s a) (givenCodes_enumerable s a) (givenCodes_sentence s a)

omit [Mono a] in
theorem pulled_given_support (x : ℕ) :
    x ∈ (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)).obj.support ↔
      x ∈ Total.support (Ranges.range a.hom) := by
  rw [axCarrier_support,Total.support_range]
  constructor
  · rintro ⟨w,hx,b,hb⟩
    obtain ⟨u,hu,hsu⟩ := (Total.mem_val_comp _ _ b w).mp hb
    have he : u=x := Part.mem_unique ((partialInverse_graph s w u).mpr hsu)
      ((partialInverse_graph s w x).mpr hx)
    exact ⟨b,he ▸ hu⟩
  · rintro ⟨b,hb⟩
    obtain ⟨w,hw⟩ := Part.dom_iff_mem.mp ((Total.total_iff s.hom).mp s.property x
      (Total.val_target a.hom b x hb))
    exact ⟨w,hw,b,(Total.mem_val_comp _ _ b w).mpr ⟨x,hb,hw⟩⟩

omit [Mono a] in
private theorem given_supported (b x : ℕ) (hx : x ∈ Total.val a.hom b) :
    x ∈ Total.support (pulledIdem s (givenCodes s a) (givenCodes_enumerable s a)) :=
  (pulled_given_support s a x).mpr (by rw [Total.support_range]; exact ⟨b,hx⟩)

def givenForward : B ⟶ axCarrier s (givenCodes s a) (givenCodes_enumerable s a) :=
  ⟨Total.intoSubcarrier a.hom (pulledIdem s (givenCodes s a) (givenCodes_enumerable s a))
      (given_supported s a),
    Total.intoSubcarrier_total a.hom a.property _ (given_supported s a)⟩

omit [Mono a] in
theorem givenForward_graph (b x : ℕ) :
    x ∈ Total.val (givenForward s a).hom b ↔ x ∈ Total.val a.hom b := Iff.rfl

omit [Mono a] in
theorem givenForward_inclusion :
    givenForward s a ≫ inclusion s (givenCodes s a) (givenCodes_enumerable s a) = a := by
  apply WideSubcategory.hom_ext
  exact Total.intoSubcarrier_fac a.hom _ (given_supported s a)

def givenBackward : axCarrier s (givenCodes s a) (givenCodes_enumerable s a) ⟶ B :=
  let k := (inclusion s (givenCodes s a) (givenCodes_enumerable s a)).hom ≫ PartialSpans.inverse a
  ⟨k,(Total.total_iff k).mpr (fun x hx => by
    have hr := (pulled_given_support s a x).mp hx
    rw [Total.support_range] at hr
    obtain ⟨b,hb⟩ := hr
    exact Part.dom_iff_mem.mpr ⟨b,(Total.mem_val_comp _ _ x b).mpr
      ⟨x,(inclusion_graph s (givenCodes s a) (givenCodes_enumerable s a) x x).mpr ⟨hx,rfl⟩,
        (partialInverse_graph a x b).mpr hb⟩⟩)⟩

theorem givenBackward_graph (x b : ℕ) :
    b ∈ Total.val (givenBackward s a).hom x ↔
      x ∈ (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)).obj.support ∧
        x ∈ Total.val a.hom b := by
  change b ∈ Total.val ((inclusion s (givenCodes s a) (givenCodes_enumerable s a)).hom ≫
    PartialSpans.inverse a) x ↔ _
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨u,hu,hb⟩
    obtain ⟨hx,he⟩ := (inclusion_graph s (givenCodes s a) (givenCodes_enumerable s a) x u).mp hu
    subst u
    exact ⟨hx,(partialInverse_graph a x b).mp hb⟩
  · rintro ⟨hx,hb⟩
    exact ⟨x,(inclusion_graph s (givenCodes s a) (givenCodes_enumerable s a) x x).mpr ⟨hx,rfl⟩,
      (partialInverse_graph a x b).mpr hb⟩

/-- The original arbitrary axiom mono is recovered on its actual sentence
points. No formula-word identity or section of a proof image is used. -/
def givenPresentation : B ≅ axCarrier s (givenCodes s a) (givenCodes_enumerable s a) where
  hom := givenForward s a
  inv := givenBackward s a
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro b hb
    obtain ⟨x,hx⟩ := Part.dom_iff_mem.mp ((Total.total_iff a.hom).mp a.property b hb)
    have hf := (givenForward_graph s a b x).mpr hx
    have hg := (givenBackward_graph s a x b).mpr
      ⟨Total.val_target (givenForward s a).hom b x hf,hx⟩
    exact (Part.eq_some_iff.mpr ((Total.mem_val_comp _ _ b b).mpr ⟨x,hf,hg⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity B.obj.support b b).mpr ⟨hb,rfl⟩)).symm
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro x hx
    have hr := (pulled_given_support s a x).mp hx
    rw [Total.support_range] at hr
    obtain ⟨b,hb⟩ := hr
    have hf := (givenBackward_graph s a x b).mpr ⟨hx,hb⟩
    have hg := (givenForward_graph s a b x).mpr hb
    exact (Part.eq_some_iff.mpr ((Total.mem_val_comp _ _ x x).mpr ⟨b,hf,hg⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ x x).mpr ⟨hx,rfl⟩)).symm

theorem givenPresentation_inclusion :
    (givenPresentation s a).hom ≫ inclusion s (givenCodes s a) (givenCodes_enumerable s a) = a :=
  givenForward_inclusion s a

theorem givenPresentation_graph (b x : ℕ) :
    x ∈ Total.val (givenPresentation s a).hom.hom b ↔ x ∈ Total.val a.hom b :=
  givenForward_graph s a b x

theorem givenPresentation_inverse_graph (x b : ℕ) :
    b ∈ Total.val (givenPresentation s a).inv.hom x ↔
      x ∈ (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)).obj.support ∧
        x ∈ Total.val a.hom b := givenBackward_graph s a x b

theorem given_subobject_eq :
    Subobject.mk a = Subobject.mk (inclusion s (givenCodes s a) (givenCodes_enumerable s a)) :=
  Subobject.mk_eq_mk_of_comm _ _ (givenPresentation s a) (givenPresentation_inclusion s a)

private def imageForward : Total.imageObject a ⟶
    axCarrier s (givenCodes s a) (givenCodes_enumerable s a) :=
  AxiomSubobjects.supportInclusion (Total.imageObject a)
    (axCarrier s (givenCodes s a) (givenCodes_enumerable s a))
    (fun x hx => (pulled_given_support s a x).mpr hx)

private def imageBackward : axCarrier s (givenCodes s a) (givenCodes_enumerable s a) ⟶
    Total.imageObject a :=
  AxiomSubobjects.supportInclusion (axCarrier s (givenCodes s a) (givenCodes_enumerable s a))
    (Total.imageObject a) (fun x hx => (pulled_given_support s a x).mp hx)

omit [Mono a] in
private theorem imageForward_graph (x y : ℕ) :
    y ∈ Total.val (imageForward s a).hom x ↔ x ∈ Total.support (Ranges.range a.hom) ∧ y=x :=
  AxiomSubobjects.supportInclusion_graph (Total.imageObject a)
    (axCarrier s (givenCodes s a) (givenCodes_enumerable s a))
    (fun x hx => (pulled_given_support s a x).mpr hx) x y

omit [Mono a] in
private theorem imageBackward_graph (x y : ℕ) :
    y ∈ Total.val (imageBackward s a).hom x ↔
      x ∈ (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)).obj.support ∧ y=x :=
  AxiomSubobjects.supportInclusion_graph
    (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)) (Total.imageObject a)
    (fun x hx => (pulled_given_support s a x).mp hx) x y

/-- The actual image carrier and the pulled axiom carrier have identical
sentence-point support. Both chart maps are guarded identities on those
points, without identifying them with formula words. -/
def imagePresentation : Total.imageObject a ≅ axCarrier s (givenCodes s a) (givenCodes_enumerable s a) where
  hom := imageForward s a
  inv := imageBackward s a
  hom_inv_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro x hx
    have hy := (pulled_given_support s a x).mpr hx
    have hf := (imageForward_graph s a x x).mpr ⟨hx,rfl⟩
    have hg := (imageBackward_graph s a x x).mpr ⟨hy,rfl⟩
    exact (Part.eq_some_iff.mpr ((Total.mem_val_comp _ _ x x).mpr ⟨x,hf,hg⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ x x).mpr ⟨hx,rfl⟩)).symm
  inv_hom_id := by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro x hx
    have hy := (pulled_given_support s a x).mp hx
    have hf := (imageBackward_graph s a x x).mpr ⟨hx,rfl⟩
    have hg := (imageForward_graph s a x x).mpr ⟨hy,rfl⟩
    exact (Part.eq_some_iff.mpr ((Total.mem_val_comp _ _ x x).mpr ⟨x,hf,hg⟩)).trans
      (Part.eq_some_iff.mpr ((Total.mem_supportIdentity _ x x).mpr ⟨hx,rfl⟩)).symm

omit [Mono a] in
theorem imagePresentation_graph (x y : ℕ) :
    y ∈ Total.val (imagePresentation s a).hom.hom x ↔
      x ∈ Total.support (Ranges.range a.hom) ∧ y=x := imageForward_graph s a x y

omit [Mono a] in
theorem imagePresentation_inverse_graph (x y : ℕ) :
    y ∈ Total.val (imagePresentation s a).inv.hom x ↔
      x ∈ (axCarrier s (givenCodes s a) (givenCodes_enumerable s a)).obj.support ∧ y=x :=
  imageBackward_graph s a x y

omit [Mono a] in
theorem imagePresentation_inclusion :
    (imagePresentation s a).hom ≫ inclusion s (givenCodes s a) (givenCodes_enumerable s a) =
      Total.imageInclusion a := by
  apply WideSubcategory.hom_ext
  apply Total.val_injective
  funext x
  apply Part.ext
  intro y
  change y ∈ Total.val ((imagePresentation s a).hom.hom ≫
    (inclusion s (givenCodes s a) (givenCodes_enumerable s a)).hom) x ↔
      y ∈ Total.val (Total.imageInclusion a).hom x
  rw [Total.mem_val_comp]
  constructor
  · rintro ⟨u,hu,hy⟩
    obtain ⟨hx,he⟩ := (imagePresentation_graph s a x u).mp hu
    subst u
    obtain ⟨_,he⟩ := (inclusion_graph s (givenCodes s a) (givenCodes_enumerable s a) x y).mp hy
    subst y
    exact (Total.mem_val_idem (Ranges.range a.hom) x x).mpr ⟨hx,rfl⟩
  · intro hy
    obtain ⟨hx,he⟩ := (Total.mem_val_idem (Ranges.range a.hom) x y).mp hy
    subst y
    exact ⟨x,(imagePresentation_graph s a x x).mpr ⟨hx,rfl⟩,
      (inclusion_graph s (givenCodes s a) (givenCodes_enumerable s a) x x).mpr
        ⟨(pulled_given_support s a x).mpr hx,rfl⟩⟩
end GivenMono

end CategoricalEssentialIncompleteness.V46.Miller.SentenceAxiomPullbacks
