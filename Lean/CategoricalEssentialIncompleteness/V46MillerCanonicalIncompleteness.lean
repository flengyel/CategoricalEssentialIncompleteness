/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalProofComparisonChosen
public import CategoricalEssentialIncompleteness.V46MillerIncompleteness
public import CategoricalEssentialIncompleteness.V46MillerTotalPartialMaps
public import CategoricalEssentialIncompleteness.V46RegularImage

/-! # Incompleteness of the actual chosen canonical Γ image

The theory idempotent here is the range of the chosen canonical sentence
conclusion. Its identification with the literal sentence theory is derived
from the proved generated-subobject comparison and the partial inverse of
the actual regular-image mono. No proof-fiber selector is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalIncompleteness
attribute [instance 2000] Uniform.nativeRestriction

section RangeComparison
variable (a : Point)

/-- A regular-epi factor has exactly the range of its total monic factor.
The partial inverse is constructed from that mono, rather than supplied. -/
private theorem range_factor {X I Y : Total.CanonicalTotal a}
    (e : X ⟶ I) (m : I ⟶ Y) [IsRegularEpi e] [Mono m] :
    Ranges.range (e.hom ≫ m.hom)=Ranges.range m.hom := by
  obtain ⟨r,hmr,hrm⟩ := Total.mono_has_partial_inverse a m
  apply Idem.ext
  have h := LocalConnectedness.V46.range_regularImage e m r hmr hrm
  have hm := LocalConnectedness.V46.range_regularImage (𝟙 I) m r hmr hrm
  have hm' : (Ranges.range m.hom).hom=r≫m.hom := by
    simpa only [show (𝟙 I : I ⟶ I).hom=𝟙 I.obj from rfl,Category.id_comp] using hm
  exact h.trans hm'.symm

/-- Equality to the actual image subobject determines the restriction range.
The isomorphism is obtained from equality in Subobject, not postulated. -/
private theorem range_of_image_eq {X I Y : Total.CanonicalTotal a}
    (f : X ⟶ Y) (m : I ⟶ Y) [Mono m]
    (h : imageSubobject f=Subobject.mk m) :
    Ranges.range f.hom=Ranges.range m.hom := by
  let i : image f ≅ I := Subobject.isoOfMkEqMk (image.ι f) m h
  have hi : i.hom≫m=image.ι f := Subobject.ofMkLEMk_comp h.le
  let e : X ⟶ I := factorThruImage f≫i.hom
  have : IsRegularEpi e := by dsimp only [e]; infer_instance
  have hfac : e≫m=f := by
    dsimp only [e]
    rw [Category.assoc,hi,image.fac]
  have hh : Ranges.range (e≫m).hom=Ranges.range m.hom := range_factor a e m
  exact (congrArg (fun k : X ⟶ Y => Ranges.range k.hom) hfac).symm.trans hh

def idemIso {X Y : SplitObject (Uniform.PointObject a)} (i : X ≅ Y) :
    Idem X ≃o Idem Y where
  toEquiv := Idem.isoEquiv i
  map_rel_iff' := by
    intro c d
    change Idem.pull i.inv c≤Idem.pull i.inv d ↔ c≤d
    constructor
    · intro h
      have hh := Idem.pull_mono i.hom h
      simpa only [← Idem.pull_comp,i.hom_inv_id,Idem.pull_id] using hh
    · intro h
      exact Idem.pull_mono i.inv h

private theorem range_post_iso {X Y Z : SplitObject (Uniform.PointObject a)}
    (f : X ⟶ Y) (i : Y ≅ Z) :
    Ranges.range (f≫i.hom)=Idem.pull i.inv (Ranges.range f) := by
  apply le_antisymm
  · apply Ranges.least
    rw [show (Idem.pull i.inv (Ranges.range f)).hom=
      i.inv≫(Ranges.range f).hom≫i.hom from Idem.isoEquiv_hom i (Ranges.range f)]
    calc
      (f≫i.hom)≫(i.inv≫(Ranges.range f).hom≫i.hom)=
          (f≫(Ranges.range f).hom)≫i.hom := by
        simp only [Category.assoc,Iso.hom_inv_id_assoc]
      _=f≫i.hom := by rw [Ranges.receives]
  · have h : Ranges.range f≤Idem.pull i.hom (Ranges.range (f≫i.hom)) := by
      apply Ranges.least
      rw [show (Idem.pull i.hom (Ranges.range (f≫i.hom))).hom=
        i.hom≫(Ranges.range (f≫i.hom)).hom≫i.inv from
        Idem.isoEquiv_hom i.symm (Ranges.range (f≫i.hom))]
      calc
        f≫i.hom≫(Ranges.range (f≫i.hom)).hom≫i.inv =
            ((f≫i.hom)≫(Ranges.range (f≫i.hom)).hom)≫i.inv := by
          simp only [Category.assoc]
        _ = (f≫i.hom)≫i.inv := by rw [Ranges.receives]
        _ = f := by rw [Category.assoc,i.hom_inv_id,Category.comp_id]
    have hh := Idem.pull_mono i.inv h
    simpa only [← Idem.pull_comp,i.inv_hom_id,Idem.pull_id] using hh
end RangeComparison

variable (a : Point)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d
local notation "SC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (CategoricalSyntax.sentenceObject (S₁)))
local notation "LC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (TheorySentenceWords.literalObject (P)))
local notation "CS" => WideSubcategory.obj (CategoricalSyntax.sentenceObject (S₂))

/-- The actual equivalence uses the original source sentence coordinate.
This equality does not identify a chosen sentence point with a formula word. -/
theorem mapped_sentence_object : ((E).functor.obj (S₁).sentenceObject).obj=(SC) :=
  congrArg (fun X : Total.CanonicalTotal a => X.obj)
    (Total.pointPresentation_object a (S₁).sentenceObject)

theorem mapped_arrow_value {X Y : Total.TotalCategory (P)} (f : X ⟶ Y) :
    ((E).functor.map f).hom.hom.val=Total.val f.hom :=
  Total.pointPresentation_value a f

def sourceSentenceIso : (SC) ≅ (CS) where
  hom := (CanonicalPresentation.mappedSentenceIso a (V) σ π d).hom.hom
  inv := (CanonicalPresentation.mappedSentenceIso a (V) σ π d).inv.hom
  hom_inv_id := congrArg (fun k : (E).functor.obj (S₁).sentenceObject ⟶
    (E).functor.obj (S₁).sentenceObject => k.hom)
    (CanonicalPresentation.mappedSentenceIso a (V) σ π d).hom_inv_id
  inv_hom_id := congrArg (fun k : (S₂).sentenceObject ⟶ (S₂).sentenceObject => k.hom)
    (CanonicalPresentation.mappedSentenceIso a (V) σ π d).inv_hom_id

/-- The fixed chart from the genuine canonical sentence pullback to literal
recursive sentences; it is independent of Γ. -/
def sentenceChart : (CS) ≅ (LC) :=
  (sourceSentenceIso a).symm≪≫Incompleteness.splitSentenceIso (P)

def chartIdemIso : Idem (CS) ≃o Idem (LC) := idemIso a (sentenceChart a)

/-- This is the range of the chosen canonical initial-algebra conclusion. -/
def theoremIdem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) : Idem (CS) :=
  Ranges.range (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ).hom

/-- The displayed idempotent represents the regular image of this exact
chosen conclusion, through the inverse of its actual image inclusion. -/
theorem theorem_regular_image (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    ∃ r : (CS) ⟶ (image (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).obj,
      (image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom≫r=𝟙 _ ∧
      r≫(image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom=rst r ∧
      (theoremIdem a Γ hΓ).hom=
        r≫(image.ι (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ)).hom := by
  let c : CanonicalPresentation.chosenSentenceProofObject a σ π d Γ hΓ ⟶
      (S₂).sentenceObject := CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ
  obtain ⟨r,hmr,hrm⟩ := Total.mono_has_partial_inverse a (image.ι c)
  refine ⟨r,hmr,hrm,?_⟩
  have hh : (Ranges.range (factorThruImage c≫image.ι c).hom).hom=
      r≫(image.ι c).hom :=
    LocalConnectedness.V46.range_regularImage (factorThruImage c) (image.ι c) r hmr hrm
  have hfac : (Ranges.range (factorThruImage c≫image.ι c).hom).hom=
      (Ranges.range c.hom).hom :=
    congrArg (fun k : CanonicalPresentation.chosenSentenceProofObject a σ π d Γ hΓ ⟶
      (S₂).sentenceObject => (Ranges.range k.hom).hom) (image.fac c)
  exact hfac.symm.trans hh

def nu : (CS) ⟶ (CS) := (S₂).sentenceNegation.hom

def refutationIdem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) : Idem (CS) :=
  Idem.pull (nu a) (theoremIdem a Γ hΓ)

theorem nu_total : isTotal (nu a) := (S₂).sentenceNegation.property

/-- The canonical chosen image and the source image have the same range,
using the actual regular image and its constructed monic partial inverse. -/
theorem theorem_range_comparison (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    theoremIdem a Γ hΓ=Ranges.range
      (((E).functor.map (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)).hom≫
        (sourceSentenceIso a).hom) := by
  let c : NamedProofImage.sentenceProofObject (P) σ π d Γ hΓ ⟶
      (S₁).sentenceObject := NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ
  let j : (E).functor.obj (S₁).sentenceObject ≅ (S₂).sentenceObject :=
    CanonicalPresentation.mappedSentenceIso a (V) σ π d
  let m : (E).functor.obj (image c) ⟶ (S₂).sentenceObject :=
    (E).functor.map (image.ι c)≫j.hom
  let e : (E).functor.obj (NamedProofImage.sentenceProofObject (P) σ π d Γ hΓ) ⟶
      (E).functor.obj (image c) := (E).functor.map (factorThruImage c)
  have hm : Mono m := by dsimp only [m]; infer_instance
  have he : IsRegularEpi e := by dsimp only [e]; infer_instance
  have hc : theoremIdem a Γ hΓ=Ranges.range m.hom :=
    range_of_image_eq a (CanonicalPresentation.chosenSentenceConclusion a σ π d Γ hΓ) m
      (CanonicalPresentation.chosen_canonical_sentenceTheory_eq a σ π d Γ hΓ)
  have hf : Ranges.range (e≫m).hom=Ranges.range m.hom := range_factor a e m
  have hfac : e≫m=(E).functor.map c≫j.hom := by
    dsimp only [e,m]
    rw [← Category.assoc,← CategoryTheory.Functor.map_comp,image.fac]
  have hfac' : Ranges.range ((E).functor.map c≫j.hom).hom=Ranges.range m.hom :=
    (congrArg (fun k : (E).functor.obj
      (NamedProofImage.sentenceProofObject (P) σ π d Γ hΓ) ⟶
        (S₂).sentenceObject => Ranges.range k.hom) hfac).symm.trans hf
  exact hc.trans hfac'.symm

/-- The fixed point-presentation functor is the actual inclusion on
supported arrows, so its range is the included original sentence range. -/
theorem mapped_source_range (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    Ranges.range ((E).functor.map
      (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)).hom=
        TheoryDomainApplication.theoremIdem a Γ hΓ := rfl

/-- Recover the exact SC idempotent, including its chosen sentence coding. -/
theorem source_theorem_conjugacy (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    Idem.pull (sourceSentenceIso a).hom (theoremIdem a Γ hΓ)=
      TheoryDomainApplication.theoremIdem a Γ hΓ := by
  rw [theorem_range_comparison a Γ hΓ,range_post_iso a,← Idem.pull_comp,
    (sourceSentenceIso a).hom_inv_id,Idem.pull_id]
  exact mapped_source_range a Γ hΓ

/-- Extension of T_a is equivalent to inclusion of the actual chosen
canonical generated theory ranges. -/
theorem extends_iff_theoremIdem_le (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    RealClosedBounds.Extends a Γ ↔
      theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a Γ hΓ := by
  constructor
  · intro hext
    have hs := TheoryDomainApplication.theoremIdem_mono a Γ hΓ hext
    change TheoryDomainApplication.theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤ TheoryDomainApplication.theoremIdem a Γ hΓ at hs
    rw [← source_theorem_conjugacy a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a),← source_theorem_conjugacy a Γ hΓ] at hs
    have hh := Idem.pull_mono (sourceSentenceIso a).inv hs
    simpa only [← Idem.pull_comp,(sourceSentenceIso a).inv_hom_id,Idem.pull_id] using hh
  · intro hext
    have hs := Idem.pull_mono (sourceSentenceIso a).hom hext
    rw [source_theorem_conjugacy a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a),source_theorem_conjugacy a Γ hΓ] at hs
    exact (TheoryDomainApplication.extends_iff_theoremIdem_le a Γ hΓ).mpr hs

theorem theorem_conjugacy (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    chartIdemIso a (theoremIdem a Γ hΓ)=Incompleteness.theoremIdem a Γ hΓ := by
  change Idem.pull ((Incompleteness.splitSentenceIso (P)).inv≫(sourceSentenceIso a).hom)
    (theoremIdem a Γ hΓ)=_
  rw [Idem.pull_comp,source_theorem_conjugacy]
  exact Incompleteness.theorem_conjugacy a Γ hΓ

theorem source_negation_square :
    TheoryDomainApplication.negation a≫(sourceSentenceIso a).hom=
      (sourceSentenceIso a).hom≫nu a :=
  congrArg (fun k : (E).functor.obj (S₁).sentenceObject ⟶ (S₂).sentenceObject => k.hom)
    (CanonicalPresentation.sentenceNegation_comparison a (V) σ π d)

theorem negation_square : nu a≫(sentenceChart a).hom=
    (sentenceChart a).hom≫Incompleteness.nu a := by
  apply (cancel_epi (sourceSentenceIso a).hom).mp
  change (sourceSentenceIso a).hom≫(nu a≫((sourceSentenceIso a).inv≫
      (Incompleteness.splitSentenceIso (P)).hom))=
    (sourceSentenceIso a).hom≫(((sourceSentenceIso a).inv≫
      (Incompleteness.splitSentenceIso (P)).hom)≫Incompleteness.nu a)
  rw [← Category.assoc,← source_negation_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  exact Incompleteness.negation_chart a

theorem inverse_negation_square : (sentenceChart a).inv≫nu a=
    Incompleteness.nu a≫(sentenceChart a).inv := by
  apply (cancel_epi (sentenceChart a).hom).mp
  calc
    (sentenceChart a).hom≫((sentenceChart a).inv≫nu a)=nu a := by
      rw [← Category.assoc,(sentenceChart a).hom_inv_id,Category.id_comp]
    _=((sentenceChart a).hom≫Incompleteness.nu a)≫(sentenceChart a).inv := by
      rw [← negation_square,Category.assoc,(sentenceChart a).hom_inv_id,Category.comp_id]
    _=_ := Category.assoc _ _ _

theorem refutation_conjugacy (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    chartIdemIso a (refutationIdem a Γ hΓ)=Incompleteness.refutationIdem a Γ hΓ := by
  change Idem.pull (sentenceChart a).inv (Idem.pull (nu a) (theoremIdem a Γ hΓ))=
    Idem.pull (Incompleteness.nu a) (Incompleteness.theoremIdem a Γ hΓ)
  rw [← theorem_conjugacy a Γ hΓ]
  change Idem.pull (sentenceChart a).inv (Idem.pull (nu a) (theoremIdem a Γ hΓ))=
    Idem.pull (Incompleteness.nu a) (Idem.pull (sentenceChart a).inv (theoremIdem a Γ hΓ))
  rw [← Idem.pull_comp,← Idem.pull_comp,inverse_negation_square]

theorem theorem_conjugacy_hom (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (Incompleteness.theoremIdem a Γ hΓ).hom=(sentenceChart a).inv≫
      (theoremIdem a Γ hΓ).hom≫(sentenceChart a).hom := by
  rw [← theorem_conjugacy]
  exact Idem.isoEquiv_hom (sentenceChart a) _

theorem refutation_conjugacy_hom (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (Incompleteness.refutationIdem a Γ hΓ).hom=(sentenceChart a).inv≫
      (refutationIdem a Γ hΓ).hom≫(sentenceChart a).hom := by
  rw [← refutation_conjugacy]
  exact Idem.isoEquiv_hom (sentenceChart a) _

/-- The printed canonical consistency hypothesis is exactly closed native
consistency, with no truth assumption on Γ. -/
theorem consistent_iff_canonical_disjoint (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    TheoryDomainApplication.Consistent Γ ↔
      theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥ := by
  rw [Incompleteness.consistent_iff_literal_disjoint a Γ hΓ]
  change Incompleteness.theoremIdem a Γ hΓ⊓Incompleteness.refutationIdem a Γ hΓ=⊥ ↔
    theoremIdem a Γ hΓ⊓refutationIdem a Γ hΓ=⊥
  constructor
  · intro h
    apply (chartIdemIso a).injective
    rw [(chartIdemIso a).map_inf,(chartIdemIso a).map_bot,
      theorem_conjugacy a Γ hΓ,refutation_conjugacy a Γ hΓ]
    exact h
  · intro h
    have hh := congrArg (chartIdemIso a) h
    simpa only [(chartIdemIso a).map_inf,(chartIdemIso a).map_bot,
      theorem_conjugacy a Γ hΓ,refutation_conjugacy a Γ hΓ] using hh

/-- Theorem 8.6 for the actual chosen canonical Γ initial-algebra image.
The top is the identity of the genuine chosen sentence object. -/
theorem printed_essential_incompleteness (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (refutationIdem a Γ hΓ) ∧
      theoremIdem a Γ hΓ⊔refutationIdem a Γ hΓ≠⊤ := by
  have hc := (consistent_iff_canonical_disjoint a Γ hΓ).mpr hcons
  obtain ⟨hi,hn⟩ := Incompleteness.essential_incompleteness a ha Γ hΓ hext hc
  constructor
  · constructor
    · exact hcons
    · rintro ⟨c,e,hce,ht,hr⟩
      apply hi.no_separator
      refine ⟨chartIdemIso a c,chartIdemIso a e,?_,?_,?_⟩
      · constructor
        · rw [← (chartIdemIso a).map_inf,hce.disjoint,(chartIdemIso a).map_bot]
        · rw [← (chartIdemIso a).map_sup,hce.cover,(chartIdemIso a).map_top]
      · simpa only [theorem_conjugacy a Γ hΓ] using (chartIdemIso a).monotone ht
      · simpa only [refutation_conjugacy a Γ hΓ] using (chartIdemIso a).monotone hr
  · intro h
    apply hn
    have hh := congrArg (chartIdemIso a) h
    simpa only [(chartIdemIso a).map_sup,(chartIdemIso a).map_top,
      theorem_conjugacy,refutation_conjugacy] using hh

theorem printed_native_incomplete (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof Γ φ ∧ ¬RealClosedBounds.Proof Γ (.neg φ) :=
  Incompleteness.native_incomplete a ha Γ hΓ hext
    ((consistent_iff_canonical_disjoint a Γ hΓ).mpr hcons)

/-- Noncoverage is on the original canonical sentence pullback, not on
the ambient numerical carrier. -/
theorem printed_noncoverage (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    theoremIdem a Γ hΓ⊔Idem.pull (nu a) (theoremIdem a Γ hΓ)≠(⊤ : Idem (CS)) :=
  (printed_essential_incompleteness a ha Γ hΓ hext hcons).2

/-- The canonical categorical formulation uses actual theory inclusion
and the actual sentence consistency equation. -/
theorem printed_categorical_incompleteness (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a Γ hΓ)
    (hcons : theoremIdem a Γ hΓ⊓Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (refutationIdem a Γ hΓ) ∧
      theoremIdem a Γ hΓ⊔refutationIdem a Γ hΓ≠⊤ :=
  printed_essential_incompleteness a ha Γ hΓ
    ((extends_iff_theoremIdem_le a Γ hΓ).mpr hext) hcons

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalIncompleteness
