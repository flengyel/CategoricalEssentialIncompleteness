import CategoricalEssentialIncompleteness.V46MillerTheorySentenceMorphisms
import CategoricalEssentialIncompleteness.V46MillerNamedProofImageReverse
import CategoricalEssentialIncompleteness.V46MillerRealClosedBounds
import CategoricalEssentialIncompleteness.V46MillerCarrierIdempotents
import CategoricalEssentialIncompleteness.V46MillerCutInseparabilitySourceSplit

/-! # The categorical domain argument for the actual Miller theory images

The sentence object is the constructed named syntax. Its proof image is
the range of the constructed finite-derivation conclusion. An extension
proves the original T_a axioms; it need not contain their words literally
or have a model on the real field. The source cut pair and the application
of Corollary 4.3 remain categorical throughout.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.TheoryDomainApplication
attribute [instance 2000] Uniform.nativeRestriction
variable (a : Point)
local notation "P" => Uniform.Family.ofPoint a
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S" => NamedProofImage.syntaxData (P) σ π d
local notation "U" => (Total.underlying («P» := (P)))
local notation "NUM" => TheorySentenceMorphisms.numericalObject (P)
private abbrev sentenceCarrier : SplitObject (Uniform.Object (P)) :=
  CarrierIdempotents.SplitCarrier ((S).sentenceObject.obj)
local notation "SC" => sentenceCarrier a
local notation "N" => CutInseparability.SourceSplit.N a

def theoremIdem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) : Idem (SC) :=
  Total.toSplitIdem (NamedProofImage.sentenceIdem (P) σ π d Γ hΓ)

def baseIdem : Idem (SC) := theoremIdem a (RealClosedAxioms.theoryAxioms a)
  (RealClosedAxioms.theoryAxioms_enumerable a)

theorem support_range (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) (s : ℕ) :
    s∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      s∈Total.Subobjects.imageCodes (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ) := by
  change s∈Total.support (Ranges.range (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ).hom) ↔ _
  rw [Total.support_range]
  rfl

/-- The verified literal proof-image theorem on the actual split carrier. -/
private theorem literal_theorem_mem (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (φ : OrderedFieldSyntax.Formula)
    (hc : φ.freeVariables=[]) :
    (NamedProofImage.sentencePoint (P) σ π d φ hc).val∈
        CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔ RealClosedBounds.Proof Γ φ := by
  change (NamedProofImage.sentencePoint (P) σ π d φ hc).val∈
    Total.support (NamedProofImage.sentenceIdem (P) σ π d Γ hΓ) ↔ RealClosedBounds.Proof Γ φ
  exact NamedProofImage.sentenceIdem_literal (P) σ π d Γ hΓ φ hc

def decodedSentence (s : (U).obj (S).sentenceObject) : OrderedFieldSyntax.Formula :=
  NamedProofImage.decodeFormula (P) σ π d ((U).map (S).sentenceInclusion s)

theorem decodedSentence_closed (s : (U).obj (S).sentenceObject) :
    (decodedSentence a s).freeVariables=[] :=
  NamedProofImage.sentence_inclusion_closed (P) σ π d s

theorem point_eta (s : (U).obj (S).sentenceObject) :
    s=NamedProofImage.sentencePoint (P) σ π d (decodedSentence a s) (decodedSentence_closed a s) := by
  apply TheorySentenceMorphisms.sentence_point_ext (P)
  calc
    (U).map (S).sentenceInclusion s=
        NamedProofImage.formulaPoint (P) σ π d (decodedSentence a s) :=
      (NamedProofImage.formulaPoint_decode (P) σ π d ((U).map (S).sentenceInclusion s)).symm
    _=(U).map (S).sentenceInclusion
        (NamedProofImage.sentencePoint (P) σ π d (decodedSentence a s)
          (decodedSentence_closed a s)) :=
      (NamedProofImage.sentencePoint_inclusion (P) σ π d (decodedSentence a s)
        (decodedSentence_closed a s)).symm

theorem theorem_mem (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (s : (U).obj (S).sentenceObject) :
    s.val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      RealClosedBounds.Proof Γ (decodedSentence a s) := by
  have he := congrArg Subtype.val (point_eta a s)
  have h : (NamedProofImage.sentencePoint (P) σ π d (decodedSentence a s)
      (decodedSentence_closed a s)).val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) ↔
      RealClosedBounds.Proof Γ (decodedSentence a s) :=
    literal_theorem_mem a Γ hΓ
      (decodedSentence a s) (decodedSentence_closed a s)
  exact (Iff.of_eq (congrArg (fun n => n∈CarrierIdempotents.support (theoremIdem a Γ hΓ)) he)).trans h

theorem numerical_domain :
    (CarrierIdempotents.SplitCarrier (NUM).obj).domain=⊤ := by
  apply Idem.ext
  apply Uniform.hom_ext_mem
  intro n m
  change m∈(Uniform.identityOn (Uniform.N (P)) (NUM).obj.support (NUM).obj.enumerable).val n ↔
    m∈Part.some n
  rw [Uniform.mem_identityOn,Part.mem_some_iff]
  exact ⟨fun h => h.2,fun h => ⟨TheorySentenceMorphisms.numerical_support (P) n,h⟩⟩

/-- This is a chart of the actual included source N, with identity values. -/
def numbersIso : (N) ≅ CarrierIdempotents.SplitCarrier (NUM).obj :=
  splitIsoOfComm (Iso.refl (Uniform.N (P))) (by
    change (𝟙 (Uniform.N (P))) ≫ 𝟙 _=
      (𝟙 (Uniform.N (P))) ≫ (CarrierIdempotents.SplitCarrier (NUM).obj).domain.hom
    rw [numerical_domain a]
    rfl)

/-- The numerical chart retains the included identity morphism. -/
private theorem numbersIso_hom :
    (numbersIso a).hom.hom=𝟙 (Uniform.N (P)) := by
  change (N).domain.hom ≫ (Iso.refl (Uniform.N (P))).hom=𝟙 (Uniform.N (P))
  rw [CutInseparability.SourceSplit.N_domain a]
  simp only [Idem.top_hom,Iso.refl_hom,Category.id_comp]

def theta : (N) ⟶ (SC) :=
  (numbersIso a).hom ≫ (TheorySentenceMorphisms.theta (P)).hom

def negation : (SC) ⟶ (SC) := (TheorySentenceMorphisms.negation (P)).hom

theorem theta_total : isTotal (theta a) :=
  isTotal_comp (iso_total (numbersIso a)) (TheorySentenceMorphisms.theta (P)).property

theorem negation_total : isTotal (negation a) := (TheorySentenceMorphisms.negation (P)).property

theorem theta_value (n : ℕ) :
    (theta a).hom.val n=Total.val (TheorySentenceMorphisms.theta (P)).hom n := by
  change ((numbersIso a).hom.hom ≫ (TheorySentenceMorphisms.theta (P)).hom.hom).val n=
    (TheorySentenceMorphisms.theta (P)).hom.hom.val n
  erw [numbersIso_hom,Category.id_comp]

theorem source_pull_support (f : (N) ⟶ (SC)) (c : Idem (SC)) (n : ℕ) :
    n∈CutInseparability.SourceSplit.support a (Idem.pull f c) ↔
      ∃ s,s∈f.hom.val n ∧ s∈CarrierIdempotents.support c := by
  change n∈PartialFunctions.support
    (Idem.pull f.hom.val (Uniform.toPfnIdem (SplitObject.baseIdem c))) ↔ _
  rw [PartialFunctions.support_pull]
  rfl

theorem lower_bound (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    CutInseparability.SourceSplit.lowerIdem a ≤ Idem.pull (theta a) (theoremIdem a Γ hΓ) := by
  apply (CutInseparability.SourceSplit.support_le_iff a _ _).mpr
  intro n hn
  rw [CutInseparability.SourceSplit.lowerIdem_support] at hn
  have hp := RealClosedBounds.lower_cut_gamma_theta a Γ hext n hn
  have ht : (NamedProofImage.sentencePoint (P) σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n)).val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) :=
    (literal_theorem_mem a Γ hΓ
      (OrderedFieldSyntax.thetaSentence n) (OrderedFieldSyntax.thetaSentence_closed n)).mpr hp
  apply (source_pull_support a (theta a) (theoremIdem a Γ hΓ) n).mpr
  refine ⟨_,?_,ht⟩
  rw [theta_value]
  exact (TheorySentenceMorphisms.theta_graph (P) n _).mpr
    (NamedProofImage.sentencePoint_word (P) σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n))

theorem upper_bound (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    CutInseparability.SourceSplit.upperIdem a ≤
      Idem.pull (theta a) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) := by
  apply (CutInseparability.SourceSplit.support_le_iff a _ _).mpr
  intro n hn
  rw [CutInseparability.SourceSplit.upperIdem_support] at hn
  let s := NamedProofImage.sentencePoint (P) σ π d (OrderedFieldSyntax.thetaSentence n)
    (OrderedFieldSyntax.thetaSentence_closed n)
  have hp := RealClosedBounds.upper_cut_gamma_negtheta a Γ hext n hn
  have ht : (NamedProofImage.sentencePoint (P) σ π d (.neg (OrderedFieldSyntax.thetaSentence n))
      (OrderedFieldSyntax.thetaSentence_closed n)).val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) :=
    (literal_theorem_mem a Γ hΓ
      (.neg (OrderedFieldSyntax.thetaSentence n)) (OrderedFieldSyntax.thetaSentence_closed n)).mpr hp
  have hs : s.val∈CarrierIdempotents.support (Idem.pull (negation a) (theoremIdem a Γ hΓ)) := by
    apply (CarrierIdempotents.support_pull_total (TheorySentenceMorphisms.negation (P))
      (theoremIdem a Γ hΓ) s).mpr
    change ((U).map (TheorySentenceMorphisms.negation (P)) s).val∈_
    rw [show s=NamedProofImage.sentencePoint (P) σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n) from rfl,TheorySentenceMorphisms.negation_point]
    exact ht
  apply (source_pull_support a (theta a) _ n).mpr
  refine ⟨s.val,?_,hs⟩
  rw [theta_value]
  exact (TheorySentenceMorphisms.theta_graph (P) n s.val).mpr
    (NamedProofImage.sentencePoint_word (P) σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n))

/-- Derivability extension, using finite replacement of nonlogical leaves.
There is no uniform choice of a proof for each nonlogical sentence of T_a. -/
theorem theoremIdem_mono (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) : baseIdem a ≤ theoremIdem a Γ hΓ := by
  apply (CarrierIdempotents.support_le_iff _ _).mpr
  intro n hn
  let s : (U).obj (S).sentenceObject := ⟨n,CarrierIdempotents.support_subset (baseIdem a) hn⟩
  apply (theorem_mem a Γ hΓ s).mpr
  exact (RealClosedBounds.extends_iff_proof_transport a Γ).mp hext (decodedSentence a s)
    ((theorem_mem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) s).mp hn)

/-- Derivability extension is exactly inclusion of the actual generated
sentence theories, rather than literal inclusion of axiom words. -/
theorem extends_iff_theoremIdem_le (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    RealClosedBounds.Extends a Γ ↔ baseIdem a ≤ theoremIdem a Γ hΓ := by
  constructor
  · exact theoremIdem_mono a Γ hΓ
  · intro hext φ hφ
    have hc := RealClosedBounds.theory_formula_closed a φ hφ
    let s := NamedProofImage.sentencePoint (P) σ π d φ hc
    have hp : RealClosedBounds.Proof (RealClosedAxioms.theoryAxioms a) φ :=
      FiniteAxiomProof.axiom_of_mem σ π d φ hφ hc
    have hs : s.val∈CarrierIdempotents.support (baseIdem a) :=
      (literal_theorem_mem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) φ hc).mpr hp
    exact (literal_theorem_mem a Γ hΓ φ hc).mp
      ((CarrierIdempotents.support_le_iff _ _).mp hext hs)

theorem sentenceTheory_mono (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : RealClosedBounds.Extends a Γ) :
    NamedProofImage.sentenceTheory (P) σ π d (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤
      NamedProofImage.sentenceTheory (P) σ π d Γ hΓ := by
  change imageSubobject
      (NamedProofImage.sentenceConclusion (P) σ π d (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a)) ≤
    imageSubobject (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)
  apply (Total.Subobjects.imageSubobject_le_iff
    (NamedProofImage.sentenceConclusion (P) σ π d (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a))
    (NamedProofImage.sentenceConclusion (P) σ π d Γ hΓ)).mpr
  intro s hs
  exact (support_range a Γ hΓ s).mp ((CarrierIdempotents.support_le_iff _ _).mp
    (theoremIdem_mono a Γ hΓ hext) ((support_range a _ _ s).mpr hs))

def Consistent (Γ : Set ℕ) : Prop :=
  ∀ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] →
    ¬(RealClosedBounds.Proof Γ φ ∧ RealClosedBounds.Proof Γ (.neg φ))

theorem consistency_disjoint (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hcons : Consistent Γ) :
    theoremIdem a Γ hΓ ⊓ Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊥ := by
  apply (CarrierIdempotents.disjoint_iff _ _).mpr
  rw [Set.disjoint_left]
  intro n hn hneg
  let s : (U).obj (S).sentenceObject := ⟨n,CarrierIdempotents.support_subset (theoremIdem a Γ hΓ) hn⟩
  have hp := (theorem_mem a Γ hΓ s).mp hn
  have hns := (CarrierIdempotents.support_pull_total (TheorySentenceMorphisms.negation (P))
    (theoremIdem a Γ hΓ) s).mp hneg
  change ((U).map (TheorySentenceMorphisms.negation (P)) s).val∈_ at hns
  rw [point_eta a s,TheorySentenceMorphisms.negation_point] at hns
  have hnp := (literal_theorem_mem a Γ hΓ
    (.neg (decodedSentence a s)) (decodedSentence_closed a s)).mp hns
  exact hcons (decodedSentence a s) (decodedSentence_closed a s) ⟨hp,hnp⟩

/-- Native consistency is exactly the manuscript's sentence consistency
for the constructed Gamma derivation image. -/
theorem consistent_iff_disjoint (Γ : Set ℕ) (hΓ : Uniform.Enumerable (P) (·∈Γ)) :
    Consistent Γ ↔
      theoremIdem a Γ hΓ ⊓ Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊥ := by
  constructor
  · exact consistency_disjoint a Γ hΓ
  · intro hd φ hc hp
    let s := NamedProofImage.sentencePoint (P) σ π d φ hc
    have ht : s.val∈CarrierIdempotents.support (theoremIdem a Γ hΓ) :=
      (literal_theorem_mem a Γ hΓ φ hc).mpr hp.1
    have hn : s.val∈CarrierIdempotents.support
        (Idem.pull (negation a) (theoremIdem a Γ hΓ)) := by
      apply (CarrierIdempotents.support_pull_total (TheorySentenceMorphisms.negation (P))
        (theoremIdem a Γ hΓ) s).mpr
      change ((U).map (TheorySentenceMorphisms.negation (P)) s).val∈_
      rw [show s=NamedProofImage.sentencePoint (P) σ π d φ hc from rfl,
        TheorySentenceMorphisms.negation_point]
      exact (literal_theorem_mem a Γ hΓ (.neg φ) hc).mpr hp.2
    have hs := (CarrierIdempotents.disjoint_iff _ _).mp hd
    exact Set.disjoint_left.mp hs ht hn

/-- The printed extension and consistency hypotheses discharge all premises
of the categorical Corollary 4.3 on the actual source splitting. -/
theorem categorical_incompleteness (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ)) (hext : RealClosedBounds.Extends a Γ)
    (hcons : Consistent Γ) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (negation a) (theoremIdem a Γ hΓ)≠⊤ := by
  have hb : RealClosedBounds.Extends a (RealClosedAxioms.theoryAxioms a) :=
    RealClosedBounds.extends_of_inclusion a (Set.Subset.refl _)
  exact domain_incompleteness
    (C := CutInseparability.SourceSplit.SplitSource a) («U» := (N)) («S» := (SC))
    (CutInseparability.SourceSplit.printed_cut_inseparability a ha)
    (theta a) (theta_total a) (negation a) (negation_total a) (baseIdem a)
    (lower_bound a _ (RealClosedAxioms.theoryAxioms_enumerable a) hb)
    (upper_bound a _ (RealClosedAxioms.theoryAxioms_enumerable a) hb)
    (theoremIdem a Γ hΓ) (theoremIdem_mono a Γ hΓ hext) (consistency_disjoint a Γ hΓ hcons)

/-- The same Corollary 4.3 application with both hypotheses expressed
on the actual generated restriction idempotents. -/
theorem categorical_incompleteness_of_theory_extension (ha : IsMiller a) (Γ : Set ℕ)
    (hΓ : Uniform.Enumerable (P) (·∈Γ))
    (hext : baseIdem a ≤ theoremIdem a Γ hΓ)
    (hcons : theoremIdem a Γ hΓ ⊓ Idem.pull (negation a) (theoremIdem a Γ hΓ)=⊥) :
    Inseparable (theoremIdem a Γ hΓ) (Idem.pull (negation a) (theoremIdem a Γ hΓ)) ∧
      theoremIdem a Γ hΓ ⊔ Idem.pull (negation a) (theoremIdem a Γ hΓ)≠⊤ :=
  categorical_incompleteness a ha Γ hΓ
    ((extends_iff_theoremIdem_le a Γ hΓ).mpr hext)
    ((consistent_iff_disjoint a Γ hΓ).mpr hcons)

end CategoricalEssentialIncompleteness.V46.Miller.TheoryDomainApplication
