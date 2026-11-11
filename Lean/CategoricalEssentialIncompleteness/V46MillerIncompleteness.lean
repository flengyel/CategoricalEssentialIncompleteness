/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTheorySentenceWordRanges
public import CategoricalEssentialIncompleteness.V46MillerTheoryDomainApplication
public import CategoricalEssentialIncompleteness.V46MillerRealClosedConsistency
public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences

/-! # The actual Miller theory in literal recursive sentence coordinates

The source categorical domain argument is transported through the proved
sentence-word isomorphism inside Split(E_a). All complementary candidate
idempotents are recovered through its inverse. The nonlogical extension
condition is derivability, and only T_a has the constructed real model.
The separate canonical S₂ generated-theory comparison is not asserted here.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Incompleteness
attribute [instance 2000] Uniform.nativeRestriction
open OrderedFieldSyntax

def splitTotalFunctor (P : Uniform.Family) :
    Total.TotalCategory P ⥤ SplitObject (Uniform.Object P) :=
  PreservesRestriction.totalInclusion (Total.Carrier P) ⋙ Total.inclusion (P := P)

def splitIdemOrderIso {P : Uniform.Family}
    {X Y : SplitObject (Uniform.Object P)} (i : X ≅ Y) : Idem X ≃o Idem Y where
  toEquiv := Idem.isoEquiv i
  map_rel_iff' := by
    intro c d
    change Idem.pull i.inv c ≤ Idem.pull i.inv d ↔ c ≤ d
    constructor
    · intro h
      have hh := Idem.pull_mono i.hom h
      simpa only [← Idem.pull_comp, i.hom_inv_id, Idem.pull_id] using hh
    · intro h
      exact Idem.pull_mono i.inv h

private theorem map_square {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Z)
    (h : W ⟶ Y) (k : Y ⟶ Z) (w : f ≫ g = h ≫ k) :
    F.map f ≫ F.map g = F.map h ≫ F.map k :=
  (F.map_comp f g).symm.trans ((congrArg F.map w).trans (F.map_comp h k))

private theorem inverse_square {C : Type*} [Category C] {X Y : C}
    (i : X ≅ Y) (f : X ⟶ X) (g : Y ⟶ Y) (h : f ≫ i.hom = i.hom ≫ g) :
    i.inv ≫ f = g ≫ i.inv := by
  apply (cancel_mono i.hom).mp
  calc
    (i.inv ≫ f) ≫ i.hom = i.inv ≫ (f ≫ i.hom) := Category.assoc _ _ _
    _ = i.inv ≫ (i.hom ≫ g) := congrArg (fun k => i.inv ≫ k) h
    _ = g := by rw [← Category.assoc, i.inv_hom_id, Category.id_comp]
    _ = (g ≫ i.inv) ≫ i.hom := by
      rw [Category.assoc, i.inv_hom_id, Category.comp_id]

section Chart
variable (P : Uniform.Family)
local notation "S₁" => NamedProofImage.syntaxData P functionSymbols relationSymbols bound
local notation "SC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (CategoricalSyntax.sentenceObject (S₁)))
local notation "LC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (TheorySentenceWords.literalObject P))

/-- This is the actual restriction isomorphism; both maps are the
underlying maps of the constructed total sentence-word chart. -/
def splitSentenceIso : (SC) ≅ (LC) :=
  (splitTotalFunctor P).mapIso (TheorySentenceWords.sentenceIso P)

/-- The existing restriction-idempotent conjugation, with its actual order. -/
def chartIdemIso : Idem (SC) ≃o Idem (LC) :=
  splitIdemOrderIso (splitSentenceIso P)

theorem chartIdemIso_apply (c : Idem (SC)) :
    chartIdemIso P c=Idem.pull (splitSentenceIso P).inv c := rfl

theorem chartIdemIso_hom (c : Idem (SC)) :
    (chartIdemIso P c).hom=(splitSentenceIso P).inv ≫ c.hom ≫ (splitSentenceIso P).hom :=
  Idem.isoEquiv_hom (splitSentenceIso P) c

/-- Every idempotent on the literal carrier is recovered, with no
assumption that it was originally supplied in chart coordinates. -/
def recoverIdem (c : Idem (LC)) : Idem (SC) := (chartIdemIso P).symm c

theorem recover_chart (c : Idem (SC)) : recoverIdem P (chartIdemIso P c)=c :=
  (chartIdemIso P).symm_apply_apply c

theorem chart_recover (c : Idem (LC)) : chartIdemIso P (recoverIdem P c)=c :=
  (chartIdemIso P).apply_symm_apply c

theorem recover_complementary (c d : Idem (LC)) (h : Complementary c d) :
    Complementary (recoverIdem P c) (recoverIdem P d) := by
  constructor
  · change (chartIdemIso P).symm c ⊓ (chartIdemIso P).symm d=⊥
    rw [← (chartIdemIso P).symm.map_inf,h.disjoint,(chartIdemIso P).symm.map_bot]
  · change (chartIdemIso P).symm c ⊔ (chartIdemIso P).symm d=⊤
    rw [← (chartIdemIso P).symm.map_sup,h.cover,(chartIdemIso P).symm.map_top]

/-- In particular, an arbitrary proposed separator recovers an actual
separator in the original chosen sentence object. -/
theorem recover_separator (a b : Idem (SC)) (c d : Idem (LC))
    (h : Complementary c d) (ha : chartIdemIso P a≤c) (hb : chartIdemIso P b≤d) :
    Complementary (recoverIdem P c) (recoverIdem P d) ∧
      a≤recoverIdem P c ∧ b≤recoverIdem P d := by
  refine ⟨recover_complementary P c d h,?_,?_⟩
  · simpa only [recoverIdem,(chartIdemIso P).symm_apply_apply] using
      (chartIdemIso P).symm.monotone ha
  · simpa only [recoverIdem,(chartIdemIso P).symm_apply_apply] using
      (chartIdemIso P).symm.monotone hb

private theorem chart_inseparable (a b : Idem (SC)) (h : Inseparable a b) :
    Inseparable (chartIdemIso P a) (chartIdemIso P b) := by
  constructor
  · rw [← (chartIdemIso P).map_inf,h.disjoint,(chartIdemIso P).map_bot]
  · rintro ⟨c,d,hc,ha,hb⟩
    obtain ⟨hcomp,hca,hdb⟩ := recover_separator P a b c d hc ha hb
    exact h.no_separator ⟨recoverIdem P c,recoverIdem P d,hcomp,hca,hdb⟩

end Chart

section MillerTheory
variable (a : Point)
local notation "P" => Uniform.Family.ofPoint a
local notation "σ" => functionSymbols
local notation "π" => relationSymbols
local notation "d" => bound
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "SC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (CategoricalSyntax.sentenceObject (S₁)))
local notation "LC" => CarrierIdempotents.SplitCarrier (WideSubcategory.obj (TheorySentenceWords.literalObject (P)))
local notation "N" => CutInseparability.SourceSplit.N a

/-- The actual interpreted Gamma theorem range, on the proper sentence set. -/
def theoremIdem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) : Idem (LC) :=
  Total.toSplitIdem (TheorySentenceWordRanges.theoremIdem (P) Γ hΓ)

def nu : (LC) ⟶ (LC) := Total.inclusion.map (TheorySentenceWords.literalNegation (P)).hom

def refutationIdem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) : Idem (LC) :=
  Idem.pull (nu a) (theoremIdem a Γ hΓ)

def theta : (N) ⟶ (LC) := TheoryDomainApplication.theta a ≫ (splitSentenceIso (P)).hom

theorem theta_total : isTotal (theta a) :=
  isTotal_comp (TheoryDomainApplication.theta_total a) (iso_total (splitSentenceIso (P)))

theorem nu_total : isTotal (nu a) := (TheorySentenceWords.literalNegation (P)).property

theorem theoremIdem_support (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    CarrierIdempotents.support (theoremIdem a Γ hΓ)=
      Total.Subobjects.imageCodes (TheorySentenceWordRanges.literalConclusion (P) Γ hΓ) :=
  TheorySentenceWordRanges.theoremIdem_support (P) Γ hΓ

/-- Exact range conjugacy, proved at the full graph and image level. -/
theorem theorem_conjugacy (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    chartIdemIso (P) (TheoryDomainApplication.theoremIdem a Γ hΓ)=theoremIdem a Γ hΓ := by
  apply CarrierIdempotents.support_injective
  have hpull : CarrierIdempotents.support
      (chartIdemIso (P) (TheoryDomainApplication.theoremIdem a Γ hΓ)) =
      {word | ∃ s, s∈Total.val (TheorySentenceWords.sentenceIso (P)).inv.hom word ∧
        s∈CarrierIdempotents.support (TheoryDomainApplication.theoremIdem a Γ hΓ)} :=
    CarrierIdempotents.support_pull
      (A := (TheorySentenceWords.literalObject (P)).obj)
      (B := (S₁).sentenceObject.obj)
      (TheorySentenceWords.sentenceIso (P)).inv.hom
      (TheoryDomainApplication.theoremIdem a Γ hΓ)
  calc
    CarrierIdempotents.support
        (chartIdemIso (P) (TheoryDomainApplication.theoremIdem a Γ hΓ)) =
        {word | ∃ s, s∈Total.val (TheorySentenceWords.sentenceIso (P)).inv.hom word ∧
          s∈CarrierIdempotents.support (TheoryDomainApplication.theoremIdem a Γ hΓ)} := hpull
    _ = Total.Subobjects.imageCodes (TheorySentenceWordRanges.literalConclusion (P) Γ hΓ) := by
      ext word
      constructor
      · rintro ⟨s, hs, hΓs⟩
        obtain ⟨p, hps⟩ := (TheoryDomainApplication.support_range a Γ hΓ s).mp hΓs
        refine ⟨p, (TheorySentenceWordRanges.literalConclusion_graph (P) Γ hΓ p word).mpr ?_⟩
        exact (Total.mem_val_comp
          (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ).hom
          (NamedProofImage.sentenceWord (P) σ π d).hom p word).mpr
            ⟨s, hps, (TheorySentenceWords.fromLiteral_graph (P) word s).mp hs⟩
      · rintro ⟨p, hp⟩
        have hword := (TheorySentenceWordRanges.literalConclusion_graph (P) Γ hΓ p word).mp hp
        obtain ⟨s, hps, hs⟩ := (Total.mem_val_comp
          (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ).hom
          (NamedProofImage.sentenceWord (P) σ π d).hom p word).mp hword
        exact ⟨s, (TheorySentenceWords.fromLiteral_graph (P) word s).mpr hs,
          (TheoryDomainApplication.support_range a Γ hΓ s).mpr ⟨p, hps⟩⟩
    _ = CarrierIdempotents.support (theoremIdem a Γ hΓ) :=
      (theoremIdem_support a Γ hΓ).symm

theorem negation_chart : TheoryDomainApplication.negation a ≫ (splitSentenceIso (P)).hom=
    (splitSentenceIso (P)).hom ≫ nu a :=
  map_square (splitTotalFunctor (P))
    (TheorySentenceMorphisms.negation (P)) (TheorySentenceWords.sentenceIso (P)).hom
    (TheorySentenceWords.sentenceIso (P)).hom (TheorySentenceWords.literalNegation (P))
    (TheorySentenceWords.negation_square (P))

theorem inverse_negation_chart : (splitSentenceIso (P)).inv ≫ TheoryDomainApplication.negation a=
    nu a ≫ (splitSentenceIso (P)).inv :=
  inverse_square (splitSentenceIso (P)) (TheoryDomainApplication.negation a) (nu a)
    (negation_chart a)

/-- Both restriction idempotents are conjugated through the same chart. -/
theorem refutation_conjugacy (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    chartIdemIso (P) (Idem.pull (TheoryDomainApplication.negation a)
      (TheoryDomainApplication.theoremIdem a Γ hΓ))=refutationIdem a Γ hΓ := by
  rw [refutationIdem,← theorem_conjugacy]
  change Idem.pull (splitSentenceIso (P)).inv
      (Idem.pull (TheoryDomainApplication.negation a) (TheoryDomainApplication.theoremIdem a Γ hΓ))=
    Idem.pull (nu a) (Idem.pull (splitSentenceIso (P)).inv (TheoryDomainApplication.theoremIdem a Γ hΓ))
  rw [← Idem.pull_comp,← Idem.pull_comp,inverse_negation_chart]

theorem theorem_conjugacy_hom (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (theoremIdem a Γ hΓ).hom=(splitSentenceIso (P)).inv ≫
      (TheoryDomainApplication.theoremIdem a Γ hΓ).hom ≫ (splitSentenceIso (P)).hom := by
  rw [← theorem_conjugacy]
  exact chartIdemIso_hom (P) _

theorem refutation_conjugacy_hom (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    (refutationIdem a Γ hΓ).hom=(splitSentenceIso (P)).inv ≫
      (Idem.pull (TheoryDomainApplication.negation a) (TheoryDomainApplication.theoremIdem a Γ hΓ)).hom ≫
        (splitSentenceIso (P)).hom := by
  rw [← refutation_conjugacy]
  exact chartIdemIso_hom (P) _

/-- Closed native consistency agrees exactly with consistency of the
literal sentence theory in the restriction splitting. -/
theorem consistent_iff_literal_disjoint (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    TheoryDomainApplication.Consistent Γ ↔
      theoremIdem a Γ hΓ ⊓ refutationIdem a Γ hΓ=⊥ := by
  constructor
  · intro hc
    have hd := TheoryDomainApplication.consistency_disjoint a Γ hΓ hc
    have hh := congrArg (chartIdemIso (P)) hd
    simpa only [(chartIdemIso (P)).map_inf,(chartIdemIso (P)).map_bot,
      theorem_conjugacy,refutation_conjugacy] using hh
  · intro hd
    apply (TheoryDomainApplication.consistent_iff_disjoint a Γ hΓ).mpr
    apply (chartIdemIso (P)).injective
    rw [(chartIdemIso (P)).map_inf,(chartIdemIso (P)).map_bot,
      theorem_conjugacy,refutation_conjugacy]
    exact hd

/-- The numerical source is the actual included N, and the output is
exactly the original sentence 2*c_n<1. -/
theorem theta_value (n : ℕ) : (theta a).hom.val n=Part.some (OrderedFieldSyntax.theta n) := by
  apply Part.eq_some_iff.mpr
  let s := NamedProofImage.sentencePoint (P) σ π d (thetaSentence n) (thetaSentence_closed n)
  have hpre : s.val∈(TheoryDomainApplication.theta a).hom.val n := by
    rw [TheoryDomainApplication.theta_value]
    exact (TheorySentenceMorphisms.theta_graph (P) n s.val).mpr
      (NamedProofImage.sentencePoint_word (P) σ π d (thetaSentence n) (thetaSentence_closed n))
  have hpost : OrderedFieldSyntax.theta n∈Total.val
      (TheorySentenceWords.sentenceIso (P)).hom.hom s.val :=
    (TheorySentenceWords.toLiteral_graph (P) s.val _).mpr
      (NamedProofImage.sentencePoint_word (P) σ π d (thetaSentence n) (thetaSentence_closed n))
  change OrderedFieldSyntax.theta n∈((TheoryDomainApplication.theta a).hom.val n).bind
    (Total.val (TheorySentenceWords.sentenceIso (P)).hom.hom)
  exact Part.mem_bind_iff.mpr ⟨s.val, hpre, hpost⟩

theorem nu_value (word : ℕ) (hw : word∈TheorySentenceWords.literalSet) :
    (nu a).hom.val word=Part.some (negationWord word) :=
  Part.eq_some_iff.mpr ((TheorySentenceWords.literalNegation_graph (P) word _).mpr ⟨hw,rfl⟩)

theorem recursive_sentences : PrimrecPred (fun word : ℕ => word∈TheorySentenceWords.literalSet) :=
  OrderedFieldSentenceMembership.sentence_membership_primrec

theorem theorem_word_iff (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) (φ : Formula) :
    formulaCode φ∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      RealClosedBounds.Proof Γ φ ∧ φ.freeVariables=[] := by
  rw [theoremIdem_support]
  exact TheorySentenceWordRanges.theorem_word_iff (P) Γ hΓ φ

theorem refutation_word_iff (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) (φ : Formula) :
    formulaCode φ∈CarrierIdempotents.support (refutationIdem a Γ hΓ) ↔
      RealClosedBounds.Proof Γ (.neg φ) ∧ φ.freeVariables=[] := by
  change formulaCode φ∈Total.support (TheorySentenceWordRanges.refutationIdem (P) Γ hΓ) ↔
    RealClosedBounds.Proof Γ (.neg φ) ∧ φ.freeVariables=[]
  exact TheorySentenceWordRanges.refutation_word_iff (P) Γ hΓ φ

def nativeTheoremWords (Γ : Set ℕ) : Set ℕ :=
  {word | ∃ φ : Formula,formulaCode φ=word ∧ φ.freeVariables=[] ∧ RealClosedBounds.Proof Γ φ}

def nativeRefutationWords (Γ : Set ℕ) : Set ℕ :=
  {word | ∃ φ : Formula,formulaCode φ=word ∧ φ.freeVariables=[] ∧ RealClosedBounds.Proof Γ (.neg φ)}

/-- The whole interpreted theorem support is the actual finite native proof set. -/
theorem theorem_wordset (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    CarrierIdempotents.support (theoremIdem a Γ hΓ)=nativeTheoremWords Γ :=
  (theoremIdem_support a Γ hΓ).trans (TheorySentenceWordRanges.theorem_words (P) Γ hΓ)

theorem refutation_wordset (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    CarrierIdempotents.support (refutationIdem a Γ hΓ)=nativeRefutationWords Γ := by
  ext word
  constructor
  · intro hw
    have hs : word∈TheorySentenceWords.literalSet :=
      (TheorySentenceWords.literal_support (P) word).mp
        (CarrierIdempotents.support_subset (refutationIdem a Γ hΓ) hw)
    obtain ⟨φ,hc,rfl⟩ := (TheorySentenceWords.literal_iff_native word).mp hs
    exact ⟨φ,rfl,hc,((refutation_word_iff a Γ hΓ φ).mp hw).1⟩
  · rintro ⟨φ,rfl,hc,hp⟩
    exact (refutation_word_iff a Γ hΓ φ).mpr ⟨hp,hc⟩

/-- The exact source categorical theorem transferred by a restriction
isomorphism, for every derivability extension with ordinary native consistency. -/
theorem essential_incompleteness (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : TheoryDomainApplication.Consistent Γ) :
    Inseparable (theoremIdem a Γ hΓ) (refutationIdem a Γ hΓ) ∧
      theoremIdem a Γ hΓ ⊔ refutationIdem a Γ hΓ≠⊤ := by
  obtain ⟨hi,hnc⟩ := TheoryDomainApplication.categorical_incompleteness a ha Γ hΓ hext hcons
  constructor
  · simpa only [theorem_conjugacy,refutation_conjugacy] using
      chart_inseparable (P) _ _ hi
  · intro hc
    apply hnc
    apply (chartIdemIso (P)).injective
    rw [(chartIdemIso (P)).map_sup,(chartIdemIso (P)).map_top,
      theorem_conjugacy,refutation_conjugacy]
    exact hc

/-- Theorem 8.6 with precisely the printed sentence-idempotent
consistency hypothesis. -/
theorem printed_essential_incompleteness (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : theoremIdem a Γ hΓ ⊓ Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (nu a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (nu a) (theoremIdem a Γ hΓ)≠⊤ :=
  essential_incompleteness a ha Γ hΓ hext
    ((consistent_iff_literal_disjoint a Γ hΓ).mpr hcons)

/-- The top in this statement has precisely the recursive sentence support. -/
theorem literal_noncoverage (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : TheoryDomainApplication.Consistent Γ) :
    CarrierIdempotents.support (theoremIdem a Γ hΓ) ∪
      CarrierIdempotents.support (refutationIdem a Γ hΓ)≠TheorySentenceWords.literalSet := by
  have hn := (CarrierIdempotents.join_ne_top_iff (theoremIdem a Γ hΓ)
    (refutationIdem a Γ hΓ)).mp (essential_incompleteness a ha Γ hΓ hext hcons).2
  have hs : (TheorySentenceWords.literalObject (P)).obj.support=TheorySentenceWords.literalSet :=
    Set.ext (TheorySentenceWords.literal_support (P))
  intro hcover
  exact hn (hcover.trans hs.symm)

theorem native_word_noncoverage (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : TheoryDomainApplication.Consistent Γ) :
    nativeTheoremWords Γ ∪ nativeRefutationWords Γ≠TheorySentenceWords.literalSet := by
  rw [← theorem_wordset a Γ hΓ,← refutation_wordset a Γ hΓ]
  exact literal_noncoverage a ha Γ hΓ hext hcons

/-- A literal closed native sentence is independent of every such Γ. -/
theorem native_incomplete (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : TheoryDomainApplication.Consistent Γ) :
    ∃ φ : Formula,φ.freeVariables=[] ∧ ¬RealClosedBounds.Proof Γ φ ∧
      ¬RealClosedBounds.Proof Γ (.neg φ) := by
  classical
  have hn := literal_noncoverage a ha Γ hΓ hext hcons
  have hex : ∃ word,word∈TheorySentenceWords.literalSet ∧
      word∉CarrierIdempotents.support (theoremIdem a Γ hΓ) ∪
        CarrierIdempotents.support (refutationIdem a Γ hΓ) := by
    by_contra h
    apply hn
    apply Set.Subset.antisymm
    · rintro word (hw | hw)
      · exact (TheorySentenceWords.literal_support (P) word).mp
          (CarrierIdempotents.support_subset (theoremIdem a Γ hΓ) hw)
      · exact (TheorySentenceWords.literal_support (P) word).mp
          (CarrierIdempotents.support_subset (refutationIdem a Γ hΓ) hw)
    · intro word hw
      by_contra hnot
      exact h ⟨word,hw,hnot⟩
  obtain ⟨word,hword,hnot⟩ := hex
  obtain ⟨φ,hc,rfl⟩ := (TheorySentenceWords.literal_iff_native word).mp hword
  refine ⟨φ,hc,?_,?_⟩
  · intro hp
    exact hnot (Or.inl ((theorem_word_iff a Γ hΓ φ).mpr ⟨hp,hc⟩))
  · intro hp
    exact hnot (Or.inr ((refutation_word_iff a Γ hΓ φ).mpr ⟨hp,hc⟩))

theorem printed_native_incomplete (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : theoremIdem a Γ hΓ ⊓ Idem.pull (nu a) (theoremIdem a Γ hΓ)=⊥) :
    ∃ φ : Formula,φ.freeVariables=[] ∧ ¬RealClosedBounds.Proof Γ φ ∧
      ¬RealClosedBounds.Proof Γ (.neg φ) :=
  native_incomplete a ha Γ hΓ hext
    ((consistent_iff_literal_disjoint a Γ hΓ).mpr hcons)

/-- Consistency of T_a itself is supplied by its actual real model. -/
theorem base_native_incomplete (ha : IsMiller a) :
    ∃ φ : Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof (RealClosedAxioms.theoryAxioms a) φ ∧
      ¬RealClosedBounds.Proof (RealClosedAxioms.theoryAxioms a) (.neg φ) :=
  native_incomplete a ha (RealClosedAxioms.theoryAxioms a)
    (RealClosedAxioms.theoryAxioms_enumerable a)
    (RealClosedBounds.extends_of_inclusion a (Set.Subset.refl _))
    (RealClosedConsistency.theoryAxioms_consistent a)

end MillerTheory
end CategoricalEssentialIncompleteness.V46.Miller.Incompleteness
