/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompletenessCoordinates
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofComparison
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticPA
public import CategoricalEssentialIncompleteness.V46NamedGammaEvidenceSoundness
public import CategoricalEssentialIncompleteness.V46FirstOrderInference

/-! # The numerical arithmetic application to the theorem range -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness
open NamedArithmeticSignature

abbrev paAxioms : Carrier := ArithmeticIndexedPAEnumeration.axiomCodes

theorem pa_containsPA : ContainsPA paAxioms := fun _ h => h

private theorem coded_range_support {X Y : NumericalTuples.Object} (f : X ⟶ Y)
    (v : NumericalTuples.Point Y → ℕ)
    (hv : ∀ y, NumericalTuples.code Y.dimension y.val = v y) :
    ClassicalPrograms.splitSupport (Ranges.range (numericalQ.map f)) =
      {word : ℕ | ∃ p : NumericalTuples.Point X, v (f.toFun p) = word} := by
  refine (numericalQ_range_support f).trans ?_
  ext word
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,(hv (f.toFun p)).symm.trans hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,(hv (f.toFun p)).trans hp⟩

private def sentenceValue (s : NumericalTuples.Point ProofImage.sentenceObject) : ℕ := s.val

private theorem sentence_code (s : NumericalTuples.Point ProofImage.sentenceObject) :
    NumericalTuples.code ProofImage.sentenceObject.dimension s.val = sentenceValue s := rfl

private theorem range_of_split_factor {X I Y : NumericalTuples.Object}
    (q : X ⟶ I) [IsSplitEpi q] (m : I ⟶ Y) (f : X ⟶ Y) (h : q ≫ m = f) :
    Ranges.range (numericalQ.map f) = Ranges.range (numericalQ.map m) := by
  rw [← h,numericalQ.map_comp]
  apply Ranges.precomp_split_epi (numericalQ.map q) (numericalQ.map (section_ q))
  rw [← numericalQ.map_comp,IsSplitEpi.id,CategoryTheory.Functor.map_id]

/-- This is the range of the numerical finite-proof conclusion, with the manuscript's
named-word sentence presentation. -/
def theoremIdem (Γ : Carrier) : Idem S_rec :=
  Ranges.range (numericalQ.map (ProofComparison.conclusion Γ))

theorem theorem_range (Γ : Carrier) : theoremIdem Γ =
    Ranges.range (numericalQ.map (ProofImage.inclusion Γ)) :=
  range_of_split_factor (ProofComparison.quotient Γ) (ProofImage.inclusion Γ)
    (ProofComparison.conclusion Γ) (ProofComparison.factor Γ)

theorem theorem_support (Γ : Carrier) : ClassicalPrograms.splitSupport (theoremIdem Γ) =
    {word : ℕ | (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word]} := by
  refine (congrArg ClassicalPrograms.splitSupport (theorem_range Γ)).trans ?_
  refine (coded_range_support (ProofImage.inclusion Γ) sentenceValue sentence_code).trans ?_
  ext word
  constructor
  · rintro ⟨p,hp⟩
    have hv : p.val = word := (ProofImage.inclusion_value Γ p).symm.trans hp
    exact hv ▸ p.property
  · intro h
    let p : NumericalTuples.Point (ProofImage.theoryObject Γ) := ⟨word,h⟩
    exact ⟨p,ProofImage.inclusion_value Γ p⟩

section Extension
variable (Γ : Carrier) (hPA : ContainsPA Γ)

/-- The standard axiom inclusion is a total numerical morphism. Its graph need not have a
PA proof of the inclusion of enumerations. -/
def axiomExtension : Rules.axiomObject paAxioms ⟶ Rules.axiomObject Γ where
  toFun a := ⟨a.val,(Rules.axiom_membership Γ a.val).mpr
    ⟨hPA a.val ((Rules.axiom_membership paAxioms a.val).mp a.property).1,
      ((Rules.axiom_membership paAxioms a.val).mp a.property).2⟩⟩
  represented := ⟨Part.some,Partrec.some,fun _ => rfl⟩

theorem axiomExtension_square : axiomExtension Γ hPA ≫ Rules.axioms Γ = Rules.axioms paAxioms := by
  apply (cancel_mono Coordinates.numericalSyntax.sentenceInclusion).1
  apply (cancel_mono Coordinates.formulaIso.hom).1
  apply NumericalTuples.Map.ext
  funext a
  apply Subtype.ext
  change (Coordinates.formulaIso.hom.toFun
    (Coordinates.numericalSyntax.sentenceInclusion.toFun
      ((Rules.axioms Γ).toFun ((axiomExtension Γ hPA).toFun a)))).val =
    (Coordinates.formulaIso.hom.toFun
      (Coordinates.numericalSyntax.sentenceInclusion.toFun ((Rules.axioms paAxioms).toFun a))).val
  exact (Rules.axioms_word Γ ((axiomExtension Γ hPA).toFun a)).trans (Rules.axioms_word paAxioms a).symm

def ruleExtension : RulePresentation.Hom (Rules.rules paAxioms) (Rules.rules Γ) :=
  firstOrderAxiomMap Coordinates.numericalSyntax.logicalAxioms Coordinates.numericalSyntax.sentenceInclusion
    (Rules.axioms paAxioms) (Rules.axioms Γ) Coordinates.numericalSyntax.quantifierConstructor
    Coordinates.numericalSyntax.implicationConstructor (axiomExtension Γ hPA) (axiomExtension_square Γ hPA)

def pulledRuleAlgebra {F : NumericalTuples.Object} {N : ℕ}
    {R R' : RulePresentation F N} (ι : RulePresentation.Hom R R')
    (P' : Endofunctor.Algebra R'.inference) : Endofunctor.Algebra R.inference where
  a := P'.a
  str := ι.inferenceTransformation.app P'.a ≫ P'.str

def initialRuleMap {F : NumericalTuples.Object} {N : ℕ}
    {R R' : RulePresentation F N} (ι : RulePresentation.Hom R R')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (P' : Endofunctor.Algebra R'.inference) : P.a ⟶ P'.a :=
  (hP.to (pulledRuleAlgebra ι P')).f

theorem initialRuleMap_conclusion {F : NumericalTuples.Object} {N : ℕ}
    {R R' : RulePresentation F N} (ι : RulePresentation.Hom R R')
    (P : Endofunctor.Algebra R.inference) (hP : IsInitial P)
    (P' : Endofunctor.Algebra R'.inference) :
    (initialRuleMap ι P hP P').left ≫ P'.a.hom = P.a.hom :=
  Over.w (initialRuleMap ι P hP P')

/-- Initiality transforms ordered finite derivations, changing only the enumerated nullary
labels and retaining every conclusion. -/
def proofExtension :=
  (initialRuleMap (ruleExtension Γ hPA) (SentenceProofCodes.allAlgebra paAxioms)
    (SentenceProofCodes.allInitial paAxioms) (SentenceProofCodes.allAlgebra Γ)).left

abbrev proofExtension_conclusion :=
  initialRuleMap_conclusion (ruleExtension Γ hPA) (SentenceProofCodes.allAlgebra paAxioms)
    (SentenceProofCodes.allInitial paAxioms) (SentenceProofCodes.allAlgebra Γ)

def sentenceMap {P P' F S : NumericalTuples.Object}
    (c : P ⟶ F) (c' : P' ⟶ F) (j : S ⟶ F) (f : P ⟶ P') (hf : f ≫ c' = c) :
    pullback c j ⟶ pullback c' j :=
  pullback.lift (pullback.fst c j ≫ f) (pullback.snd c j)
    (by rw [Category.assoc,hf,pullback.condition])

private theorem sentenceMap_conclusion {P P' F S : NumericalTuples.Object}
    (c : P ⟶ F) (c' : P' ⟶ F) (j : S ⟶ F) (f : P ⟶ P') (hf : f ≫ c' = c) :
    sentenceMap c c' j f hf ≫ pullback.snd c' j = pullback.snd c j :=
  pullback.lift_snd (pullback.fst c j ≫ f) (pullback.snd c j)
    (by rw [Category.assoc,hf,pullback.condition])

def sentencePullbackExtension :=
  sentenceMap (SentenceProofCodes.allConclusion paAxioms) (SentenceProofCodes.allConclusion Γ)
    Coordinates.numericalSyntax.sentenceInclusion (proofExtension Γ hPA) (proofExtension_conclusion Γ hPA)

def sentenceExtension : SentenceProofCodes.object paAxioms ⟶ SentenceProofCodes.object Γ :=
  (SentenceProofCodes.pullbackIso paAxioms).inv ≫ sentencePullbackExtension Γ hPA ≫
    (SentenceProofCodes.pullbackIso Γ).hom

theorem sentenceExtension_conclusion :
    sentenceExtension Γ hPA ≫ SentenceProofCodes.conclusion Γ = SentenceProofCodes.conclusion paAxioms := by
  simp only [sentenceExtension,SentenceProofCodes.conclusion,Category.assoc,Iso.hom_inv_id_assoc,
    sentencePullbackExtension,sentenceMap_conclusion]

theorem sentenceExtension_literal : sentenceExtension Γ hPA ≫ ProofComparison.conclusion Γ =
    ProofComparison.conclusion paAxioms := by
  change sentenceExtension Γ hPA ≫ (SentenceProofCodes.conclusion Γ ≫ Coordinates.literalSentence) = _
  rw [← Category.assoc,sentenceExtension_conclusion]
  rfl

include hPA in
/-- The third inequality follows from finite-proof extension in the numerical category,
not PA-provability of Gamma's consistency. -/
theorem pa_theorems_le : theoremIdem paAxioms ≤ theoremIdem Γ := by
  have h : numericalQ.map (ProofComparison.conclusion paAxioms) =
      numericalQ.map (sentenceExtension Γ hPA) ≫ numericalQ.map (ProofComparison.conclusion Γ) :=
    (congrArg numericalQ.map (sentenceExtension_literal Γ hPA)).symm.trans (numericalQ.map_comp _ _)
  rw [theoremIdem,h]
  exact Ranges.precomp_le _ _
end Extension

private theorem pull_bound_from_sets (X Y : SplitObject ClassicalPrograms.Rec)
    (a : Idem X) (f : X ⟶ Y) (b : Idem Y)
    (sx : Idem X → Set ℕ) (sy : Idem Y → Set ℕ) (G : ℕ → ℕ → Prop)
    (hle : ∀ a b, a ≤ b ↔ sx a ⊆ sx b)
    (hpull : ∀ b, sx (Idem.pull f b) = {n | ∃ w, G n w ∧ w ∈ sy b})
    (A B : Set ℕ) (v : ℕ → ℕ)
    (ha : sx a = A) (hb : sy b = B)
    (hf : ∀ n, G n (v n)) (hv : ∀ n, n ∈ A → v n ∈ B) : a ≤ Idem.pull f b := by
  apply (hle _ _).mpr
  intro n hn
  rw [hpull]
  exact ⟨v n,hf n,hb.symm ▸ hv n (ha ▸ hn)⟩

private theorem pull_twice_bound_from_sets (X Y Z : SplitObject ClassicalPrograms.Rec)
    (a : Idem X) (f : X ⟶ Y) (g : Y ⟶ Z) (b : Idem Z)
    (sx : Idem X → Set ℕ) (sy : Idem Y → Set ℕ) (sz : Idem Z → Set ℕ)
    (G H : ℕ → ℕ → Prop)
    (hle : ∀ a b, a ≤ b ↔ sx a ⊆ sx b)
    (hpull : ∀ b, sx (Idem.pull f b) = {n | ∃ w, G n w ∧ w ∈ sy b})
    (gpull : ∀ b, sy (Idem.pull g b) = {n | ∃ w, H n w ∧ w ∈ sz b})
    (A B : Set ℕ) (v w : ℕ → ℕ)
    (ha : sx a = A) (hb : sz b = B)
    (hf : ∀ n, G n (v n)) (hg : ∀ n, H (v n) (w n))
    (hv : ∀ n, n ∈ A → w n ∈ B) : a ≤ Idem.pull f (Idem.pull g b) := by
  apply (hle _ _).mpr
  intro n hn
  rw [hpull,gpull]
  exact ⟨v n,hf n,w n,hg n,hb.symm ▸ hv n (ha ▸ hn)⟩

private def positiveValue (n : ℕ) : ℕ :=
  NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val n

private theorem theta_hits (n : ℕ) :
    positiveValue n ∈
      ClassicalPrograms.J.map theta.hom n :=
  (theta_graph n (positiveValue n)).mpr rfl

private theorem semantic_positive_target (Γ : Carrier) (hExt : ArithmeticNamedAxiomComparison.ExtendsPA Γ)
    (n : ℕ) (ha : ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n]) :
    (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ)
      ![positiveValue n] :=
  (NamedArithmeticDiagonalBounds.semantic_bounds ℕ Γ hExt).1 n ha

private theorem support_order (a b : Idem ClassicalPrograms.parameterObject) :
    a ≤ b ↔ ClassicalPrograms.splitSupport a ⊆ ClassicalPrograms.splitSupport b :=
  ClassicalPrograms.splitSupport_le_iff a b

private theorem theta_support (b : Idem S_rec) :
    ClassicalPrograms.splitSupport (Idem.pull theta b) =
      {n : ℕ | ∃ w, w ∈ ClassicalPrograms.J.map theta.hom n ∧ w ∈ ClassicalPrograms.splitSupport b} :=
  ClassicalPrograms.splitSupport_pull theta b

private def negativeValue (n : ℕ) : ℕ :=
  NamedArithmeticProofSearch.negationWord ℕ
    (positiveValue n)

private theorem nu_hits (n : ℕ) : negativeValue n ∈
    ClassicalPrograms.J.map nu.hom
      (positiveValue n) :=
  (nu_graph _ _).mpr ⟨theta_sentence_supported n,rfl⟩

private theorem semantic_negative_target (Γ : Carrier) (hExt : ArithmeticNamedAxiomComparison.ExtendsPA Γ)
    (n : ℕ) (ha : ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n]) :
    (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![negativeValue n] :=
  (NamedArithmeticDiagonalBounds.semantic_bounds ℕ Γ hExt).2 n ha

private theorem nu_support (b : Idem S_rec) :
    ClassicalPrograms.splitSupport (Idem.pull nu b) =
      {n : ℕ | ∃ w, w ∈ ClassicalPrograms.J.map nu.hom n ∧ w ∈ ClassicalPrograms.splitSupport b} :=
  ClassicalPrograms.splitSupport_pull nu b

/-- The source arithmetic bound is transported to the numerical range with the axiom
predicate kept opaque during the support comparison. -/
theorem support_positive (Γ : Carrier) (hExt : ArithmeticNamedAxiomComparison.ExtendsPA Γ) :
    includedA ≤ Idem.pull theta (theoremIdem Γ) :=
  pull_bound_from_sets ClassicalPrograms.parameterObject S_rec includedA theta (theoremIdem Γ)
    (fun a => ClassicalPrograms.splitSupport a) (fun a => ClassicalPrograms.splitSupport a)
    (fun n w => w ∈ ClassicalPrograms.J.map theta.hom n) support_order theta_support
    {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb (M := ℕ) ![n]}
    {word : ℕ | (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word]}
    positiveValue
    includedA_support (theorem_support Γ) theta_hits (semantic_positive_target Γ hExt)

/-- The negative bound uses literal Neg after the same Theta. -/
theorem support_negative (Γ : Carrier) (hExt : ArithmeticNamedAxiomComparison.ExtendsPA Γ) :
    includedB ≤ Idem.pull theta (Idem.pull nu (theoremIdem Γ)) :=
  pull_twice_bound_from_sets ClassicalPrograms.parameterObject S_rec S_rec includedB theta nu (theoremIdem Γ)
    (fun a => ClassicalPrograms.splitSupport a) (fun a => ClassicalPrograms.splitSupport a)
    (fun a => ClassicalPrograms.splitSupport a)
    (fun n w => w ∈ ClassicalPrograms.J.map theta.hom n)
    (fun n w => w ∈ ClassicalPrograms.J.map nu.hom n) support_order theta_support nu_support
    {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb (M := ℕ) ![n]}
    {word : ℕ | (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word]}
    positiveValue
    negativeValue
    includedB_support (theorem_support Γ) theta_hits nu_hits (semantic_negative_target Γ hExt)

/-- First inequality for the chosen PA sentence-axiom presentation. -/
theorem positive_bound : includedA ≤ Idem.pull theta (theoremIdem paAxioms) :=
  support_positive paAxioms (extendsPA paAxioms pa_containsPA)

/-- Second inequality for the same literal PA presentation. -/
theorem negative_bound : includedB ≤ Idem.pull theta (Idem.pull nu (theoremIdem paAxioms)) :=
  support_negative paAxioms (extendsPA paAxioms pa_containsPA)

/-- The three inequalities in the numerical arithmetic application, on their
restriction-idempotent objects. -/
theorem domain_inclusions (Γ : Carrier) (hPA : ContainsPA Γ) :
    includedA ≤ Idem.pull theta (theoremIdem paAxioms) ∧
      includedB ≤ Idem.pull theta (Idem.pull nu (theoremIdem paAxioms)) ∧
        theoremIdem paAxioms ≤ theoremIdem Γ :=
  ⟨positive_bound,negative_bound,pa_theorems_le Γ hPA⟩

private theorem disjoint_from_support (X : SplitObject ClassicalPrograms.Rec)
    (a : Idem X) (f : X ⟶ X) (s : Idem X → Set ℕ) (G : ℕ → ℕ → Prop)
    (hinj : Function.Injective s)
    (hinf : ∀ a b, s (a ⊓ b) = s a ∩ s b) (hbot : s ⊥ = ∅)
    (hpull : ∀ b, s (Idem.pull f b) = {n | ∃ w, G n w ∧ w ∈ s b})
    (A : Set ℕ) (ha : s a = A)
    (hdisj : ∀ n w, n ∈ A → G n w → w ∈ A → False) : a ⊓ Idem.pull f a = ⊥ := by
  apply hinj
  rw [hinf,hpull,hbot]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro n ⟨hn,w,hw,hm⟩
  exact hdisj n w (ha ▸ hn) hw (ha ▸ hm)

private theorem sentence_support_injective :
    Function.Injective (fun a : Idem S_rec => ClassicalPrograms.splitSupport a) :=
  ClassicalPrograms.splitSupport_injective

private theorem sentence_support_inf (a b : Idem S_rec) :
    ClassicalPrograms.splitSupport (a ⊓ b) =
      ClassicalPrograms.splitSupport a ∩ ClassicalPrograms.splitSupport b :=
  ClassicalPrograms.splitSupport_inf a b

private theorem sentence_support_bot :
    ClassicalPrograms.splitSupport (⊥ : Idem S_rec) = ∅ := ClassicalPrograms.splitSupport_bot

private theorem support_no_both (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) (word w : ℕ)
    (ht : (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word])
    (hw : w ∈ ClassicalPrograms.J.map nu.hom word)
    (hn : (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![w]) : False := by
  obtain ⟨hs,rfl⟩ := (nu_graph word w).mp hw
  exact NamedGammaEvidenceSoundness.standard_sentence_evidence_disjoint Γ
    (extendsPA Γ hPA) hc word hs ⟨ht,hn⟩

theorem theorem_refutation_disjoint (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    theoremIdem Γ ⊓ Idem.pull nu (theoremIdem Γ) = ⊥ :=
  disjoint_from_support S_rec (theoremIdem Γ) nu
    (fun a => ClassicalPrograms.splitSupport a)
    (fun n w => w ∈ ClassicalPrograms.J.map nu.hom n)
    sentence_support_injective sentence_support_inf sentence_support_bot nu_support
    {word : ℕ | (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![word]}
    (theorem_support Γ) (support_no_both Γ hPA hc)

/-- Corollary 4.3 is applied to the numerical proof-conclusion range in Split(Rec), after
all three bounds are proved. -/
theorem categorical_incompleteness (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    Inseparable (theoremIdem Γ) (Idem.pull nu (theoremIdem Γ)) ∧
      theoremIdem Γ ⊔ Idem.pull nu (theoremIdem Γ) ≠ ⊤ :=
  domain_incompleteness included_inseparable theta theta_total nu nu_total (theoremIdem paAxioms)
    positive_bound negative_bound (theoremIdem Γ) (pa_theorems_le Γ hPA)
    (theorem_refutation_disjoint Γ hPA hc)

/-- The chosen categorical-syntax presentation has the same range after the proved
sentence chart. -/
def syntaxTheoremIdem (Γ : Carrier) : Idem (numericalQ.obj Coordinates.numericalSyntax.sentenceObject) :=
  Ranges.range (numericalQ.map (SentenceProofCodes.conclusion Γ))

theorem syntax_theorem_range (Γ : Carrier) :
    Idem.pull syntaxSentenceIso.hom (theoremIdem Γ) = syntaxTheoremIdem Γ := by
  exact numericalQ_range_iso (SentenceProofCodes.conclusion Γ) (asIso Coordinates.literalSentence)

private theorem syntax_negation_pull (Γ : Carrier) :
    Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ) =
      Idem.pull syntaxSentenceIso.hom (Idem.pull nu (theoremIdem Γ)) := by
  rw [← syntax_theorem_range,← Idem.pull_comp,syntax_negation_square,Idem.pull_comp]

/-- The same 4.3 application is obtained on the constructed syntax
sentence object; the word presentation is related by the proved chart. -/
theorem syntax_categorical_incompleteness (Γ : Carrier) (hPA : ContainsPA Γ)
    (hc : Consistent (ArithmeticNamedProofConnectives.system Γ)) :
    Inseparable (syntaxTheoremIdem Γ)
      (Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ)) ∧
      syntaxTheoremIdem Γ ⊔
        Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ) ≠ ⊤ := by
  have hθ : isTotal syntaxTheta :=
    isTotal_comp (iso_total omegaIso) (isTotal_comp (numericalQ_total _) (numericalQ_total _))
  have ha : includedA ≤ Idem.pull syntaxTheta (syntaxTheoremIdem paAxioms) := by
    rw [← syntax_theorem_range,← Idem.pull_comp,syntax_theta_square]
    exact positive_bound
  have hb : includedB ≤ Idem.pull syntaxTheta
      (Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem paAxioms)) := by
    rw [syntax_negation_pull,← Idem.pull_comp,syntax_theta_square]
    exact negative_bound
  have hm : syntaxTheoremIdem paAxioms ≤ syntaxTheoremIdem Γ := by
    rw [← syntax_theorem_range,← syntax_theorem_range]
    exact Idem.pull_mono syntaxSentenceIso.hom (pa_theorems_le Γ hPA)
  have hd : syntaxTheoremIdem Γ ⊓
      Idem.pull (numericalQ.map Coordinates.numericalSyntax.sentenceNegation) (syntaxTheoremIdem Γ) = ⊥ := by
    rw [syntax_negation_pull,← syntax_theorem_range,← Idem.pull_inf,
      theorem_refutation_disjoint Γ hPA hc,Idem.pull_bot]
  exact domain_incompleteness included_inseparable syntaxTheta hθ _ (numericalQ_total _)
    (syntaxTheoremIdem paAxioms) ha hb (syntaxTheoremIdem Γ) hm hd

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness
