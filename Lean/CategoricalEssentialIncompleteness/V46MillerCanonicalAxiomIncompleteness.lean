import CategoricalEssentialIncompleteness.V46MillerCanonicalIncompleteness
import CategoricalEssentialIncompleteness.V46MillerSentenceAxiomPullbacks

/-! # Incompleteness for the original canonical axiom monomorphism

An arbitrary given axiom mono is recovered from its actual literal image
codes through the genuine point-presentation equivalence. The resulting
axiom isomorphism is used in both directions between the constructed
initial derivation algebras. Thus the final theory range is the range of
the original conclusion, rather than the range of a replacement axiom
object supplied as a new hypothesis.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalAxiomIncompleteness
attribute [instance 2000] Uniform.nativeRestriction

variable (a : Point)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "V" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S₁" => NamedProofImage.syntaxData (P) σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a (V) σ π d
local notation "j" => CanonicalPresentation.mappedSentenceIso a (V) σ π d
variable {A : Total.CanonicalTotal a}

/-- This is a preimage of an actual morphism under the full equivalence E.
It makes no choice in any Γ-proof fiber. -/
def sourceAxioms (m : A ⟶ (S₂).sentenceObject) :
    (E).inverse.obj A ⟶ (S₁).sentenceObject :=
  (E).functor.preimage (((E).counitIso.app A).hom≫m≫(j).inv)

theorem sourceAxioms_map (m : A ⟶ (S₂).sentenceObject) :
    (E).functor.map (sourceAxioms a m)=((E).counitIso.app A).hom≫m≫(j).inv :=
  (E).functor.map_preimage _

instance sourceAxioms_mono (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Mono (sourceAxioms a m) := by
  have hmap : Mono ((E).functor.map (sourceAxioms a m)) := by
    rw [sourceAxioms_map a m]
    infer_instance
  exact (E).functor.mono_of_mono_map hmap

theorem sourceAxioms_square (m : A ⟶ (S₂).sentenceObject) :
    (E).functor.map (sourceAxioms a m)≫(j).hom=((E).counitIso.app A).hom≫m := by
  rw [sourceAxioms_map a m]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- These are literal formula words, reached through the actual source
sentence-word mono; they are not the codes of chosen sentence points. -/
def recoveredCodes (m : A ⟶ (S₂).sentenceObject) : Set ℕ :=
  SentenceAxiomPullbacks.givenCodes (NamedProofImage.sentenceWord (P) σ π d) (sourceAxioms a m)

theorem recoveredCodes_enumerable (m : A ⟶ (S₂).sentenceObject) :
    Uniform.Enumerable (P) (·∈recoveredCodes a m) :=
  SentenceAxiomPullbacks.givenCodes_enumerable (NamedProofImage.sentenceWord (P) σ π d)
    (sourceAxioms a m)

theorem recoveredCodes_sentence (m : A ⟶ (S₂).sentenceObject) :
    recoveredCodes a m ⊆ AxiomSubobjects.imageCodes (NamedProofImage.sentenceWord (P) σ π d) :=
  SentenceAxiomPullbacks.givenCodes_sentence (NamedProofImage.sentenceWord (P) σ π d)
    (sourceAxioms a m)

def sourceAxiomIso (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (E).inverse.obj A ≅ NamedProofImage.axiomCarrier (P) σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m) :=
  SentenceAxiomPullbacks.givenPresentation (NamedProofImage.sentenceWord (P) σ π d)
    (sourceAxioms a m)

theorem sourceAxiomIso_inclusion (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (sourceAxiomIso a m).hom≫NamedProofImage.axioms (P) σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)=sourceAxioms a m :=
  SentenceAxiomPullbacks.givenPresentation_inclusion (NamedProofImage.sentenceWord (P) σ π d)
    (sourceAxioms a m)

theorem source_subobject_recovery (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Subobject.mk (sourceAxioms a m)=Subobject.mk
      (NamedProofImage.axioms (P) σ π d (recoveredCodes a m) (recoveredCodes_enumerable a m)) :=
  SentenceAxiomPullbacks.given_subobject_eq (NamedProofImage.sentenceWord (P) σ π d)
    (sourceAxioms a m)

/-- Recover the original canonical mono itself, including its original
domain, through E's counit and the proved chosen-pullback comparison. -/
def axiomIso (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    A ≅ CanonicalPresentation.chosenAxiomObject a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m) :=
  ((E).counitIso.app A).symm≪≫(E).functor.mapIso (sourceAxiomIso a m)≪≫
    CanonicalPresentation.canonicalAxiomIso a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)

theorem axiomIso_inclusion (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (axiomIso a m).hom≫CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)=m := by
  calc
    (axiomIso a m).hom≫CanonicalPresentation.chosenAxioms a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)=
      ((E).counitIso.app A).inv≫((E).functor.map (sourceAxiomIso a m).hom≫
        CanonicalPresentation.canonicalAxioms a σ π d
          (recoveredCodes a m) (recoveredCodes_enumerable a m)) := by
            simp only [axiomIso,Iso.trans_hom,Iso.symm_hom,CategoryTheory.Functor.mapIso_hom,
              Category.assoc,CanonicalPresentation.canonicalAxiomIso_inclusion]
    _=((E).counitIso.app A).inv≫((E).functor.map
        ((sourceAxiomIso a m).hom≫NamedProofImage.axioms (P) σ π d
          (recoveredCodes a m) (recoveredCodes_enumerable a m))≫(j).hom) := by
            simp only [CanonicalPresentation.canonicalAxioms,CategoryTheory.Functor.map_comp,Category.assoc]
    _=((E).counitIso.app A).inv≫((E).functor.map (sourceAxioms a m)≫(j).hom) := by
      rw [sourceAxiomIso_inclusion]
    _=((E).counitIso.app A).inv≫(((E).counitIso.app A).hom≫m) := by
      rw [sourceAxioms_square]
    _=m := by rw [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

theorem axiomIso_inverse_inclusion (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (axiomIso a m).inv≫m=CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m) := by
  calc
    (axiomIso a m).inv≫m=(axiomIso a m).inv≫
        ((axiomIso a m).hom≫CanonicalPresentation.chosenAxioms a σ π d
          (recoveredCodes a m) (recoveredCodes_enumerable a m)) :=
      congrArg (fun f : A ⟶ (S₂).sentenceObject => (axiomIso a m).inv≫f)
        (axiomIso_inclusion a m).symm
    _=CanonicalPresentation.chosenAxioms a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m) := by
      rw [← Category.assoc,(axiomIso a m).inv_hom_id,Category.id_comp]

/-- The generated chosen presentation recovers the given axiom subobject. -/
theorem axiom_subobject_recovery (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    Subobject.mk m=Subobject.mk (CanonicalPresentation.chosenAxioms a σ π d
      (recoveredCodes a m) (recoveredCodes_enumerable a m)) :=
  Subobject.mk_eq_mk_of_comm _ _ (axiomIso a m) (axiomIso_inclusion a m)

def rules (m : A ⟶ (S₂).sentenceObject) : RulePresentation (S₂).algebra.a.2 2 :=
  (S₂).logicalRules m

def proofAlgebra (m : A ⟶ (S₂).sentenceObject) : Endofunctor.Algebra (rules a m).inference :=
  Derivation.Canonical.derivationAlgebra a (rules a m)

def proofInitial (m : A ⟶ (S₂).sentenceObject) : IsInitial (proofAlgebra a m) :=
  Derivation.Canonical.derivationInitial a (rules a m)

def conclusion (m : A ⟶ (S₂).sentenceObject) :
    (proofAlgebra a m).a.left ⟶ (S₂).algebra.a.2 := (proofAlgebra a m).a.hom

def sentenceProofObject (m : A ⟶ (S₂).sentenceObject) : Total.CanonicalTotal a :=
  pullback (conclusion a m) (S₂).sentenceInclusion

def sentenceConclusion (m : A ⟶ (S₂).sentenceObject) :
    sentenceProofObject a m ⟶ (S₂).sentenceObject :=
  pullback.snd (conclusion a m) (S₂).sentenceInclusion

def theoremIdem (m : A ⟶ (S₂).sentenceObject) : Idem (S₂).sentenceObject.obj :=
  Ranges.range (sentenceConclusion a m).hom

def refutationIdem (m : A ⟶ (S₂).sentenceObject) : Idem (S₂).sentenceObject.obj :=
  Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)

/-- Both image inequalities are obtained from the actual initial algebras
and the actual axiom iso, with no initiality or image equality premise. -/
theorem sentence_image_recovery (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    imageSubobject (sentenceConclusion a m)=imageSubobject
      (CanonicalPresentation.chosenSentenceConclusion a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)) := by
  apply le_antisymm
  · exact firstOrder_sentence_image_monotone (S₂).logicalAxioms (S₂).sentenceInclusion
      m (CanonicalPresentation.chosenAxioms a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m))
      (S₂).quantifierConstructor (S₂).implicationConstructor
      (axiomIso a m).hom (axiomIso_inclusion a m) (proofAlgebra a m) (proofInitial a m)
      (CanonicalPresentation.chosenProofAlgebra a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m))
  · exact firstOrder_sentence_image_monotone (S₂).logicalAxioms (S₂).sentenceInclusion
      (CanonicalPresentation.chosenAxioms a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)) m
      (S₂).quantifierConstructor (S₂).implicationConstructor
      (axiomIso a m).inv (axiomIso_inverse_inclusion a m)
      (CanonicalPresentation.chosenProofAlgebra a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m))
      (CanonicalPresentation.chosenProofInitial a σ π d
        (recoveredCodes a m) (recoveredCodes_enumerable a m)) (proofAlgebra a m)

private theorem range_factor {X I Y : Total.CanonicalTotal a}
    (e : X ⟶ I) (m : I ⟶ Y) [IsRegularEpi e] [Mono m] :
    Ranges.range (e.hom≫m.hom)=Ranges.range m.hom := by
  obtain ⟨r,hmr,hrm⟩ := Total.mono_has_partial_inverse a m
  apply Idem.ext
  have h := LocalConnectedness.V46.range_regularImage e m r hmr hrm
  have hi := LocalConnectedness.V46.range_regularImage (𝟙 I) m r hmr hrm
  have hi' : (Ranges.range m.hom).hom=r≫m.hom := by
    simpa only [show (𝟙 I : I ⟶ I).hom=𝟙 I.obj from rfl,Category.id_comp] using hi
  exact h.trans hi'.symm

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
  have hh := range_factor a e m
  have he : e.hom≫m.hom=f.hom := congrArg (fun k : X ⟶ Y => k.hom) hfac
  rw [he] at hh
  exact hh

/-- Equality of regular image subobjects gives equality of the actual
restriction ranges, using the constructed monic partial inverses. -/
theorem range_recovery (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    theoremIdem a m=CanonicalIncompleteness.theoremIdem a
      (recoveredCodes a m) (recoveredCodes_enumerable a m) := by
  let c := CanonicalPresentation.chosenSentenceConclusion a σ π d
    (recoveredCodes a m) (recoveredCodes_enumerable a m)
  have h := range_of_image_eq a (sentenceConclusion a m) (image.ι c)
    (sentence_image_recovery a m)
  have hc := range_of_image_eq a c (image.ι c) (rfl : imageSubobject c=Subobject.mk (image.ι c))
  exact h.trans hc.symm

/-- The recovered literal extension condition is exactly inclusion of
T_a's chosen theory in the original mono's generated sentence theory. -/
theorem extends_iff_theoremIdem_le (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    RealClosedBounds.Extends a (recoveredCodes a m) ↔
      CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m := by
  rw [range_recovery a m]
  exact CanonicalIncompleteness.extends_iff_theoremIdem_le a
    (recoveredCodes a m) (recoveredCodes_enumerable a m)

/-- The extension condition uses actual finite derivability from T_a,
not literal inclusion of its axiom words or a selected proof of each axiom. -/
theorem finite_proof_transport_iff_theoremIdem_le
    (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    (∀ φ : OrderedFieldSyntax.Formula,
      RealClosedBounds.Proof (RealClosedAxioms.theoryAxioms a) φ →
        RealClosedBounds.Proof (recoveredCodes a m) φ) ↔
      CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
        (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m :=
  (RealClosedBounds.extends_iff_proof_transport a (recoveredCodes a m)).symm.trans
    (extends_iff_theoremIdem_le a m)

theorem refutation_recovery (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    refutationIdem a m=CanonicalIncompleteness.refutationIdem a
      (recoveredCodes a m) (recoveredCodes_enumerable a m) := by
  change Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=_
  rw [range_recovery]
  rfl

theorem literal_range_conjugacy (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    CanonicalIncompleteness.chartIdemIso a (theoremIdem a m)=
      Incompleteness.theoremIdem a (recoveredCodes a m) (recoveredCodes_enumerable a m) := by
  rw [range_recovery]
  exact CanonicalIncompleteness.theorem_conjugacy a (recoveredCodes a m) (recoveredCodes_enumerable a m)

/-- Closed native consistency of the recovered literal Γ is equivalent
to the exact consistency equation for the original categorical theory. -/
theorem consistent_iff_disjoint (m : A ⟶ (S₂).sentenceObject) [Mono m] :
    TheoryDomainApplication.Consistent (recoveredCodes a m) ↔
      theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥ := by
  rw [range_recovery]
  exact CanonicalIncompleteness.consistent_iff_canonical_disjoint a
    (recoveredCodes a m) (recoveredCodes_enumerable a m)

/-- Theorem 8.6 for every original axiom subobject of the actual canonical
sentence object. Enumerability of the recovered Γ is proved above. -/
theorem printed_essential_incompleteness (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a) (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥) :
    Inseparable (theoremIdem a m) (refutationIdem a m) ∧
      theoremIdem a m⊔refutationIdem a m≠⊤ := by
  have hc : CanonicalIncompleteness.theoremIdem a (recoveredCodes a m) (recoveredCodes_enumerable a m)⊓
      Idem.pull (S₂).sentenceNegation.hom
        (CanonicalIncompleteness.theoremIdem a (recoveredCodes a m) (recoveredCodes_enumerable a m))=⊥ := by
    simpa only [range_recovery] using hcons
  have hh := CanonicalIncompleteness.printed_essential_incompleteness a ha
    (recoveredCodes a m) (recoveredCodes_enumerable a m) hext hc
  simpa only [← range_recovery a m,← refutation_recovery a m] using hh

theorem printed_noncoverage (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a) (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥) :
    theoremIdem a m⊔Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)≠
      (⊤ : Idem (S₂).sentenceObject.obj) :=
  (printed_essential_incompleteness a m ha hext hcons).2

theorem printed_native_incomplete (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a) (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) φ ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) (.neg φ) := by
  have hc : CanonicalIncompleteness.theoremIdem a
      (recoveredCodes a m) (recoveredCodes_enumerable a m)⊓
        Idem.pull (S₂).sentenceNegation.hom
          (CanonicalIncompleteness.theoremIdem a
            (recoveredCodes a m) (recoveredCodes_enumerable a m))=⊥ := by
    simpa only [range_recovery a m] using hcons
  exact CanonicalIncompleteness.printed_native_incomplete a ha
    (recoveredCodes a m) (recoveredCodes_enumerable a m) hext hc

/-- Every original axiom subobject, with both extension and consistency
stated directly on its actual generated categorical theory. -/
theorem printed_categorical_incompleteness (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a)
    (hext : CanonicalIncompleteness.theoremIdem a (RealClosedAxioms.theoryAxioms a)
      (RealClosedAxioms.theoryAxioms_enumerable a) ≤ theoremIdem a m)
    (hcons : theoremIdem a m⊓Idem.pull (S₂).sentenceNegation.hom (theoremIdem a m)=⊥) :
    Inseparable (theoremIdem a m) (refutationIdem a m) ∧
      theoremIdem a m⊔refutationIdem a m≠⊤ :=
  printed_essential_incompleteness a m ha
    ((extends_iff_theoremIdem_le a m).mpr hext) hcons

/-- The printed native consistency hypothesis supplies the categorical
consistency equation for the original axiom monomorphism. -/
theorem printed_essential_incompleteness_of_consistent
    (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a) (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : TheoryDomainApplication.Consistent (recoveredCodes a m)) :
    Inseparable (theoremIdem a m) (refutationIdem a m) ∧
      theoremIdem a m⊔refutationIdem a m≠⊤ :=
  printed_essential_incompleteness a m ha hext ((consistent_iff_disjoint a m).mp hcons)

theorem printed_native_incomplete_of_consistent
    (m : A ⟶ (S₂).sentenceObject) [Mono m]
    (ha : IsMiller a) (hext : RealClosedBounds.Extends a (recoveredCodes a m))
    (hcons : TheoryDomainApplication.Consistent (recoveredCodes a m)) :
    ∃ φ : OrderedFieldSyntax.Formula,φ.freeVariables=[] ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) φ ∧
      ¬RealClosedBounds.Proof (recoveredCodes a m) (.neg φ) :=
  printed_native_incomplete a m ha hext ((consistent_iff_disjoint a m).mp hcons)

end CategoricalEssentialIncompleteness.V46.Miller.CanonicalAxiomIncompleteness

