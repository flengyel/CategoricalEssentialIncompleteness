/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersTransport
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibers

/-! # Comparison with the existing literal Gamma theorem presentation

The sentence guard is eliminated by a proved identity-graph isomorphism.
The binder syntax and all seven logical constructors remain unchanged.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
open NamedArithmeticSignature
variable (AxPA : Carrier) (e : ℕ)

abbrev gamma : Carrier := ArithmeticIndexedAxioms.fiberAxioms AxPA e
abbrev oldAxiomCarrier : PredicateCategory 𝗣𝗔 := ArithmeticLiteralModel.axiomObject (gamma AxPA e)

theorem guardToFiberProof : 𝗣𝗔 ⊢ inclusionSentence (oldAxiomCarrier AxPA e) (gamma AxPA e) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro z hz
  exact ((SyntacticAxiomPredicates.axiomCarrier_literal 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M (gamma AxPA e) z).mp hz).1

theorem fiberToGuardProof : 𝗣𝗔 ⊢ inclusionSentence (gamma AxPA e) (oldAxiomCarrier AxPA e) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff,inclusionSentence_eval]
  intro z hz
  apply (SyntacticAxiomPredicates.axiomCarrier_literal 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M (gamma AxPA e) z).mpr
  exact ⟨hz,((ArithmeticIndexedAxioms.fiberAxioms_eval M AxPA e z).mp hz).1⟩

/-- Both morphisms retain the original formula word. PA proves both
predicate implications, including at nonstandard formula words. -/
def guardIso : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    (oldAxiomCarrier AxPA e) (gamma AxPA e) where
  hom := representedArrow 𝗣𝗔 (GraphMorphism.inclusion (guardToFiberProof AxPA e))
  inv := representedArrow 𝗣𝗔 (GraphMorphism.inclusion (fiberToGuardProof AxPA e))
  hom_inv_id := by
    apply PredicateInterpretation.jointly_faithful 𝗣𝗔
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    simp only [Functor.map_comp_apply,PredicateInterpretation.map_inclusion_val,Functor.map_id_apply]
  inv_hom_id := by
    apply PredicateInterpretation.jointly_faithful 𝗣𝗔
    intro M _ _
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    simp only [Functor.map_comp_apply,PredicateInterpretation.map_inclusion_val,Functor.map_id_apply]

/-- The old chosen-sentence axiom morphism and the literal-sentence one
are identified over the actual formula object. -/
@[reassoc] theorem guard_axioms :
    ArithmeticLiteralModel.axioms (gamma AxPA e) =
      (guardIso AxPA e).hom ≫ fiberSentencePredicate AxPA e ≫ ArithmeticLiteralModel.sentenceChart.hom := by
  apply (cancel_mono ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion).mp
  apply PredicateInterpretation.jointly_faithful 𝗣𝗔
  intro M _ _
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  have hl := SyntacticAxiomPredicates.axioms_formula_value 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M (gamma AxPA e) x
  have hr := ArithmeticLiteralModel.chart_value M
    ((F 𝗣𝗔 M).map (fiberSentencePredicate AxPA e) ((F 𝗣𝗔 M).map (guardIso AxPA e).hom x))
  have hr' : ((F 𝗣𝗔 M).map ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion
      ((F 𝗣𝗔 M).map ArithmeticLiteralModel.sentenceChart.hom
        ((F 𝗣𝗔 M).map (fiberSentencePredicate AxPA e) ((F 𝗣𝗔 M).map (guardIso AxPA e).hom x)))).val = x.val := by
    simpa only [fiberSentence_value,guardIso,PredicateInterpretation.map_inclusion_val] using hr
  simpa only [Functor.map_comp_apply] using hl.trans hr'.symm

abbrev oldRules : RulePresentation ArithmeticLiteralModel.sentenceSyntax.algebra.a.2 2 :=
  ArithmeticLiteralModel.sentenceSyntax.logicalRules (ArithmeticLiteralModel.axioms (gamma AxPA e))

namespace FirstOrderRuleTransport
universe u₁ u₂ v₁ v₂
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (E : C ≌ D) {L V F S S' A A' : C}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
variable (literalSentence : S' ⟶ F) (literalAxioms : A' ⟶ S') (a : A ≅ A')

def sourceRules := firstOrderRules logical sentence axioms all imp

def targetRules := firstOrderRules (E.functor.map logical)
  (E.functor.map literalSentence) (E.functor.map literalAxioms)
  (inv (prodComparison E.functor V F) ≫ E.functor.map all)
  (inv (prodComparison E.functor F F) ≫ E.functor.map imp)

def coefficient : ∀ i : Fin 3,
    E.functor.obj ((sourceRules logical sentence axioms all imp).instances i) ≅
      (targetRules E logical all imp literalSentence literalAxioms).instances i :=
  Fin.cases
    ((asIso (coprodComparison E.functor L A)).symm ≪≫
      coprod.mapIso (Iso.refl _) (E.functor.mapIso a))
    (Fin.cases (asIso (prodComparison E.functor V F))
      (Fin.cases (asIso (prodComparison E.functor F F)) (fun i => Fin.elim0 i)))

/-- The target's operations are transported arbitrary morphisms. Only
an original source-category axiom conclusion equation is required. -/
def data (h : axioms ≫ sentence = a.hom ≫ literalAxioms ≫ literalSentence) :
    InferenceTransport.Data E (sourceRules logical sentence axioms all imp)
      (targetRules E logical all imp literalSentence literalAxioms) where
  coefficient := coefficient E logical sentence axioms all imp literalSentence literalAxioms a
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change E.functor.map (prod.snd : V ⨯ F ⟶ F) ≫ (InferenceTransport.power E F 1).hom =
        (asIso (prodComparison E.functor V F)).hom ≫ prod.snd
      simpa only [InferenceTransport.power,finitePower,Iso.refl_hom,asIso_hom,Category.comp_id] using
        (prodComparison_snd E.functor V F).symm
    · change E.functor.map (prod.lift (prod.fst : F ⨯ F ⟶ F) imp) ≫
          (InferenceTransport.power E F 2).hom =
        (asIso (prodComparison E.functor F F)).hom ≫
          prod.lift prod.fst (inv (prodComparison E.functor F F) ≫ E.functor.map imp)
      simp only [InferenceTransport.power,finitePower,Iso.trans_hom,asIso_hom,prod.mapIso_hom,
        Iso.refl_hom,prod.map_id_id,Category.comp_id]
      apply prod.hom_ext
      · simp only [Category.assoc,prodComparison_fst,prod.lift_fst,
          ← Functor.map_comp,prod.lift_fst]
      · simp only [Category.assoc,prodComparison_snd,prod.lift_snd,
          ← Functor.map_comp,prod.lift_snd]
        simp only [IsIso.hom_inv_id_assoc]
  conclusion i := by
    fin_cases i
    · change E.functor.map (coprod.desc logical (axioms ≫ sentence)) =
        ((asIso (coprodComparison E.functor L A)).symm ≪≫
          coprod.mapIso (Iso.refl _) (E.functor.mapIso a)).hom ≫
            coprod.desc (E.functor.map logical) (E.functor.map literalAxioms ≫ E.functor.map literalSentence)
      simp only [Iso.trans_hom,Iso.symm_hom,asIso_inv,coprod.mapIso_hom,
        Iso.refl_hom,Functor.mapIso_hom,Category.assoc]
      apply (cancel_epi (coprodComparison E.functor L A)).mp
      apply coprod.hom_ext
      · simp only [coprod.inl_desc_assoc,coprodComparison,coprod.inl_desc,
          IsIso.hom_inv_id_assoc,coprod.inl_map_assoc,coprod.inl_desc,
          Category.id_comp,← Functor.map_comp]
      · simp only [coprod.inr_desc_assoc,coprodComparison,coprod.inr_desc,
          IsIso.hom_inv_id_assoc,coprod.inr_map_assoc,coprod.inr_desc]
        rw [← Functor.map_comp,← Functor.map_comp,h,coprod.inr_desc]
        simp only [Functor.map_comp]
    · change E.functor.map all = (asIso (prodComparison E.functor V F)).hom ≫
        (inv (prodComparison E.functor V F) ≫ E.functor.map all)
      simp only [asIso_hom,IsIso.hom_inv_id_assoc]
    · change E.functor.map (prod.snd : F ⨯ F ⟶ F) =
        (prodComparison E.functor F F) ≫ prod.snd
      exact (prodComparison_snd E.functor F F).symm
end FirstOrderRuleTransport

/-- The coefficient comparison retains all logical labels and uses the
proved source sentence-guard isomorphism on the nonlogical component. -/
def oldRuleData : InferenceTransport.Data (predicateEquivalence 𝗣𝗔)
    (oldRules AxPA e) (singleRules AxPA e) :=
  FirstOrderRuleTransport.data (predicateEquivalence 𝗣𝗔)
    ArithmeticLiteralModel.sentenceSyntax.logicalAxioms
    ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion
    (ArithmeticLiteralModel.axioms (gamma AxPA e))
    ArithmeticLiteralModel.sentenceSyntax.quantifierConstructor
    ArithmeticLiteralModel.sentenceSyntax.implicationConstructor
    (ArithmeticLiteralModel.sentenceChart.hom ≫ ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion)
    (fiberSentencePredicate AxPA e) (guardIso AxPA e)
    (by simpa only [Category.assoc] using
      congrArg (fun f => f ≫ ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion) (guard_axioms AxPA e))

abbrev oldCoefficientIso := (oldRuleData AxPA e).coefficient

/-- The old concrete Gamma algebra is transported with its actual
constructors into the individual literal-sentence inference signature. -/
def oldMappedAlgebra : Endofunctor.Algebra (singleRules AxPA e).inference :=
  (InferenceTransport.algebraEquivalence (predicateEquivalence 𝗣𝗔)
    (oldRules AxPA e) (singleRules AxPA e) (oldRuleData AxPA e)).functor.obj
      (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound (gamma AxPA e))

def oldMappedInitial : IsInitial (oldMappedAlgebra AxPA e) :=
  InferenceTransport.mappedInitial (predicateEquivalence 𝗣𝗔)
    (oldRules AxPA e) (singleRules AxPA e) (oldRuleData AxPA e) _
    (SyntacticGeneratedTheory.proofInitial 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound
      (ArithmeticLiteralModel.axioms (gamma AxPA e)))

/-- The required comparison is an actual algebra isomorphism, preserving
all inference constructors and the original named formula conclusion. -/
def individual_oldGamma_comparison : individualAlgebra AxPA e ≅ oldMappedAlgebra AxPA e :=
  (individualInitial AxPA e).uniqueUpToIso (oldMappedInitial AxPA e)

def individual_oldGamma_formulaIso : (individualAlgebra AxPA e).a.left ≅
    (realization 𝗣𝗔).obj (SyntacticGeneratedAxioms.proofs 𝗣𝗔
      variableSymbols functionSymbols relationSymbols bound (gamma AxPA e)).a.left :=
  InferenceTransport.carrierIso (predicateEquivalence 𝗣𝗔)
    (oldRules AxPA e) (singleRules AxPA e) (oldRuleData AxPA e) _ _
    (individual_oldGamma_comparison AxPA e)

@[reassoc] theorem individual_oldGamma_formula_conclusion :
    (individual_oldGamma_formulaIso AxPA e).hom ≫
      (realization 𝗣𝗔).map (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e)) =
        (individualAlgebra AxPA e).a.hom :=
  InferenceTransport.carrierIso_conclusion (predicateEquivalence 𝗣𝗔)
    (oldRules AxPA e) (singleRules AxPA e) (oldRuleData AxPA e) _ _
    (individual_oldGamma_comparison AxPA e)

theorem old_literal_sentence_pullback :
    IsPullback
      (pullback.fst (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e))
        ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion)
      (ArithmeticLiteralModel.conclusion (gamma AxPA e))
      (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e))
      (ArithmeticLiteralModel.sentenceChart.hom ≫ ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion) := by
  apply (IsPullback.of_hasPullback (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e))
    ArithmeticLiteralModel.sentenceSyntax.sentenceInclusion).of_iso
      (Iso.refl _) (Iso.refl _) ArithmeticLiteralModel.sentenceChart.symm (Iso.refl _)
  · simp
  · simp [ArithmeticLiteralModel.conclusion,SyntacticGeneratedTheory.sentenceConclusion]
  · simp
  · simp

theorem individual_sentence_over_old :
    IsPullback
      (pullback.fst (individualAlgebra AxPA e).a.hom ArithmeticIndexedFamily.sentenceInclusion ≫
        (individual_oldGamma_formulaIso AxPA e).hom)
      (individualSentenceConclusion AxPA e)
      ((realization 𝗣𝗔).map (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e)))
      ArithmeticIndexedFamily.sentenceInclusion := by
  apply (IsPullback.of_hasPullback (individualAlgebra AxPA e).a.hom
    ArithmeticIndexedFamily.sentenceInclusion).of_iso
      (Iso.refl _) (individual_oldGamma_formulaIso AxPA e) (Iso.refl _) (Iso.refl _)
  · simp
  · simp [individualSentenceConclusion]
  · simpa only [Iso.refl_hom,Category.comp_id] using
      (individual_oldGamma_formula_conclusion AxPA e).symm
  · simp

section DiagramLaws
universe u₃ v₃
theorem pullback_compare_snd {D : Type u₃} [Category.{v₃} D] [HasPullbacks D]
    {A B X Y Z : D} {a : A ⟶ X} {b : A ⟶ Y} {c : B ⟶ X} {d : B ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (p : IsPullback a b f g) (q : IsPullback c d f g) :
    (p.isoPullback ≪≫ q.isoPullback.symm).hom ≫ d = b := by
  have hd : q.isoPullback.inv ≫ d = pullback.snd f g := by
    have hh := congrArg (fun k => q.isoPullback.inv ≫ k) q.isoPullback_hom_snd
    simpa only [Iso.inv_hom_id_assoc] using hh.symm
  calc
    _ = p.isoPullback.hom ≫ (q.isoPullback.inv ≫ d) := by
      simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc]
    _ = p.isoPullback.hom ≫ pullback.snd f g := congrArg (fun k => p.isoPullback.hom ≫ k) hd
    _ = b := p.isoPullback_hom_snd

theorem model_iso_conclusion {C : Type u₃} {D : Type v₃}
    [Category C] [Category D] (E : C ⥤ D) (H : D ⥤ Type) (G : C ⥤ Type)
    (pc : E ⋙ H ≅ G) {P S : C} {I : D} (c : I ≅ E.obj P)
    (f : P ⟶ S) (b : I ⟶ E.obj S) (h : c.hom ≫ E.map f = b) :
    (H.mapIso c ≪≫ pc.app P).hom ≫ G.map f = H.map b ≫ pc.hom.app S := by
  simp only [Iso.trans_hom,Functor.mapIso_hom,Category.assoc]
  change H.map c.hom ≫ pc.hom.app P ≫ G.map f = _
  rw [← pc.hom.naturality f]
  change H.map c.hom ≫ H.map (E.map f) ≫ pc.hom.app S = _
  rw [← Functor.map_comp_assoc,h]

private theorem iso_range_iff {A B X Y : Type} (i : A ≅ B) (j : X ≅ Y)
    (f : A ⟶ X) (g : B ⟶ Y) (h : i.hom ≫ g = f ≫ j.hom) (x : X) :
    (∃ b : B, g b = j.hom x) ↔ ∃ a : A, f a = x := by
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨i.inv b,?_⟩
    apply (mono_iff_injective j.hom).mp inferInstance
    calc
      j.hom (f (i.inv b)) = g (i.hom (i.inv b)) := (ConcreteCategory.congr_hom h _).symm
      _ = g b := congrArg (fun z => g z) (Iso.inv_hom_id_apply i b)
      _ = j.hom x := hb
  · rintro ⟨a,ha⟩
    exact ⟨i.hom a,(ConcreteCategory.congr_hom h a).trans (congrArg (fun z => j.hom z) ha)⟩
end DiagramLaws

/-- The sentence comparison is over the chosen literal sentence object,
including the actual independent and old finite-derivation carriers. -/
def individual_oldGamma_sentenceIso : individualSentenceProof AxPA e ≅
    (realization 𝗣𝗔).obj (ArithmeticLiteralModel.proofObject (gamma AxPA e)) :=
  (individual_sentence_over_old AxPA e).isoPullback ≪≫
    ((old_literal_sentence_pullback AxPA e).map (realization 𝗣𝗔)).isoPullback.symm

@[reassoc] theorem individual_oldGamma_sentence_conclusion :
    (individual_oldGamma_sentenceIso AxPA e).hom ≫
      (realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion (gamma AxPA e)) =
        individualSentenceConclusion AxPA e := by
  exact pullback_compare_snd (individual_sentence_over_old AxPA e)
    ((old_literal_sentence_pullback AxPA e).map (realization 𝗣𝗔))

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

def oldGammaModelIso :
    (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj (individualSentenceProof AxPA e) ≅
      Obj 𝗣𝗔 M (ArithmeticLiteralModel.proofObject (gamma AxPA e)) :=
  (PredicateInterpretation.totalFunctor 𝗣𝗔 M).mapIso (individual_oldGamma_sentenceIso AxPA e) ≪≫
    (PredicateInterpretation.predicateComparison 𝗣𝗔 M).app
      (ArithmeticLiteralModel.proofObject (gamma AxPA e))

@[reassoc] theorem oldGammaModelIso_conclusion :
    (oldGammaModelIso AxPA e M).hom ≫
        (F 𝗣𝗔 M).map (ArithmeticLiteralModel.conclusion (gamma AxPA e)) =
      (PredicateInterpretation.totalFunctor 𝗣𝗔 M).map (individualSentenceConclusion AxPA e) ≫
        (PredicateInterpretation.predicateComparison 𝗣𝗔 M).hom.app ArithmeticIndexedAxioms.sentencePredicate := by
  exact model_iso_conclusion (realization 𝗣𝗔) (PredicateInterpretation.totalFunctor 𝗣𝗔 M)
    (F 𝗣𝗔 M) (PredicateInterpretation.predicateComparison 𝗣𝗔 M)
    (individual_oldGamma_sentenceIso AxPA e) (ArithmeticLiteralModel.conclusion (gamma AxPA e))
    (individualSentenceConclusion AxPA e) (individual_oldGamma_sentence_conclusion AxPA e)

/-- Uniformly in every PA model, the individual derivation range is
exactly the existing literal Gamma_e theorem predicate. -/
theorem individual_oldGamma_model (s : (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj
    ArithmeticIndexedAxioms.sentence) :
    (ArithmeticLiteralModel.theoremPredicate (gamma AxPA e)).val.Evalb
        ![((PredicateInterpretation.predicateComparison 𝗣𝗔 M).hom.app
          ArithmeticIndexedAxioms.sentencePredicate s).val] ↔
      ∃ p : (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj (individualSentenceProof AxPA e),
        (PredicateInterpretation.totalFunctor 𝗣𝗔 M).map (individualSentenceConclusion AxPA e) p = s := by
  let pc := (PredicateInterpretation.predicateComparison 𝗣𝗔 M).app ArithmeticIndexedAxioms.sentencePredicate
  apply (ArithmeticLiteralModel.theorem_iff_image M (gamma AxPA e) (pc.hom s)).trans
  exact iso_range_iff (oldGammaModelIso AxPA e M) pc
    ((PredicateInterpretation.totalFunctor 𝗣𝗔 M).map (individualSentenceConclusion AxPA e))
    ((F 𝗣𝗔 M).map (ArithmeticLiteralModel.conclusion (gamma AxPA e)))
    (oldGammaModelIso_conclusion AxPA e M) s
end Models

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
