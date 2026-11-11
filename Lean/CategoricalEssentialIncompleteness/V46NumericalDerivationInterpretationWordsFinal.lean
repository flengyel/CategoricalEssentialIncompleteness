/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretation
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationIndexAlgebra
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationStandardCoherence
public import CategoricalEssentialIncompleteness.V46NumericalRuleRebaseWords

/-! # Literal word identity of the constructed PA derivation comparison

The chosen comparison is retained. A separately constructed full ordinary
word algebra isomorphism is compared with it by algebra-morphism
uniqueness. The resulting inclusion square proves equality of the
original scalar proof words, in both directions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordsFinal
open SyntacticSyntax SyntacticDerivation
open NumericalSyntaxTreeChart (wordPresentationIso)

theorem scalar_comp {C : PredicateCategory 𝗣𝗔} {D H : PredicateCategory 𝗧𝗔}
    (a : K.obj C ≅ NumericalSyntaxTreeChart.E.functor.obj D)
    (b : NumericalSyntaxTreeChart.E.functor.obj D ≅ NumericalSyntaxTreeChart.E.functor.obj H)
    (ha : CarrierScalarIdentity C D a) (hb : IndexAlgebra.WordValue D H b.hom) :
    CarrierScalarIdentity C H (a ≪≫ b) := by
  intro x
  exact (hb (a.hom.toFun x)).trans (ha x)

theorem scalar_arrow {X Y Z : NumericalTuples.Object}
    (f : X ⟶ Z) (g : X ⟶ Y) (h : Y ⟶ Z) (he : f = g ≫ h)
    (vX : NumericalTuples.Point X → ℕ) (vZ : NumericalTuples.Point Z → ℕ)
    (hv : ∀ x, vZ (h.toFun (g.toFun x)) = vX x) (x : NumericalTuples.Point X) :
    vZ (f.toFun x) = vX x :=
  (congrArg (fun k => vZ (k.toFun x)) he).trans
    ((congrArg vZ (NumericalTuples.composition_apply g h x)).trans (hv x))

theorem scalar_change {C D : NumericalTuples.Object} (f g : C ⟶ D) (he : f = g)
    (vC : NumericalTuples.Point C → ℕ) (vD : NumericalTuples.Point D → ℕ)
    (hg : ∀ x, vD (g.toFun x) = vC x) (x : NumericalTuples.Point C) :
    vD (f.toFun x) = vC x := by
  rw [he]
  exact hg x

theorem scalar_composition {C D H : NumericalTuples.Object} (f : C ⟶ D) (g : D ⟶ H)
    (vC : NumericalTuples.Point C → ℕ) (vD : NumericalTuples.Point D → ℕ)
    (vH : NumericalTuples.Point H → ℕ)
    (hf : ∀ x, vD (f.toFun x) = vC x) (hg : ∀ x, vH (g.toFun x) = vD x)
    (x : NumericalTuples.Point C) : vH ((f ≫ g).toFun x) = vC x :=
  (congrArg vH (NumericalTuples.composition_apply f g x)).trans
    ((hg (f.toFun x)).trans (hf x))

variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)
local notation "σ" => PolynomialComparison.coefficients R
local notation "τ" => PolynomialComparison.coefficients (interpretedRules R)
local notation "p" => SyntaxPolynomial.constructors σ N
local notation "pN" => SyntaxPolynomial.constructors τ N
local notation "hp" => WordCoherence.interpreted_constructor_polynomial R
local notation "S" => postfixAlgebra 𝗣𝗔 p SyntaxPolynomial.unit
local notation "B" => plainPostfixAlgebra 𝗧𝗔
  (SyntaxPolynomial.mapCoefficients labelMap p) SyntaxPolynomial.unit
local notation "j₀" => realizedWordIso false p SyntaxPolynomial.unit
local notation "j₁" => realizedWordIso true p SyntaxPolynomial.unit
local notation "c" => fun C : PredicateCategory 𝗣𝗔 => Iso.symm (NumericalSyntaxTreeChart.E.counitIso.app (K.obj C))
local notation "I" => IndexAlgebra.normalizedTemplateIsoTo p SyntaxPolynomial.unit pN SyntaxPolynomial.unit hp rfl

/-- Both branches commute by the actual postfix and coefficient-index
comparisons, before projecting to the ordinary tree algebra. -/
def storedJointWordIso : WordCoherence.mappedJointAlgebraTo σ τ N hp S ≅
    NumericalSyntaxTreeChart.normalizedPair pN .unit :=
  (WordCoherence.sourceMappedPairIsoTo σ τ N hp S).symm ≪≫
    Initial.mappedPairIso id labelMap c p .unit p .unit ((p).mapCoefficients labelMap) .unit pN .unit
      (mapCoefficients_id _) rfl rfl rfl hp rfl S B j₀ j₁
      (normalized_mixed_term_constructor id labelMap c p .unit p .unit
        ((p).mapCoefficients labelMap) .unit (mapCoefficients_id _) rfl rfl rfl j₀ j₁
        (realizedWordIso_value false p .unit) (realizedWordIso_value true p .unit)
        NumericalPolynomialRepresentation.canonical_coefficient_value)
      (normalized_mixed_formula_constructor id labelMap c p .unit p .unit
        ((p).mapCoefficients labelMap) .unit (mapCoefficients_id _) rfl rfl rfl j₀ j₁
        (realizedWordIso_value false p .unit) (realizedWordIso_value true p .unit)
        NumericalPolynomialRepresentation.canonical_coefficient_value) ≪≫ (I).symm

theorem storedJointWordIso_first : IndexAlgebra.firstCarrierIso (storedJointWordIso R) =
    j₀ ≪≫ (IndexAlgebra.firstCarrierIso I).symm := by
  apply Iso.ext
  simp only [storedJointWordIso,IndexAlgebra.firstCarrierIso,Iso.trans_hom,Iso.symm_hom,
    Endofunctor.Algebra.comp_f,WordCoherence.sourceMappedPairIsoTo_inv_f,Initial.mappedPairIso_hom_f,
    Iso.prod_hom]
  change 𝟙 (K.obj (SyntacticDerivation.ordinaryTree 𝗣𝗔 R).a) ≫ ((j₀).hom ≫ (I).inv.f.1) = (j₀).hom ≫ (I).inv.f.1
  exact CategoryTheory.Category.id_comp _

/-- The complete joint algebra comparison fixes the raw postfix word. -/
abbrev storedJointWordIso_value :
    CarrierScalarIdentity (S).a.1 (NumericalSyntaxTreeChart.rawPairAlgebra pN .unit).a.1
      (IndexAlgebra.firstCarrierIso (storedJointWordIso R)) := by
  have h := scalar_comp j₀ (IndexAlgebra.firstCarrierIso I).symm
    (realizedWordIso_value false p .unit) (IndexAlgebra.normalizedTemplateIsoTo_inverse_word p .unit pN .unit hp rfl)
  rw [← storedJointWordIso_first R] at h
  exact h

def storedOneSortWordIso :
    WordCoherence.mappedOneSortAlgebraTo σ τ N hp (oneSortAlgebra 𝗣𝗔 σ N) ≅
      NumericalSyntaxTreeChart.literalOneSort τ N :=
  WordCoherence.projectedMappingIsoTo σ τ N hp S ≪≫
    NumericalSyntaxTreeChart.projectIso τ N (storedJointWordIso R) ≪≫
      NumericalSyntaxTreeChart.literalNormalizedIso τ N

theorem storedOneSortWordIso_first : (storedOneSortWordIso R).hom.f =
    (IndexAlgebra.firstCarrierIso (storedJointWordIso R)).hom ≫
      (wordPresentationIso (NumericalDerivation.rawTreePredicate (interpretedRules R))).hom := by
  simp only [storedOneSortWordIso,Iso.trans_hom,Endofunctor.Algebra.comp_f,
    WordCoherence.projectedMappingIsoTo_hom_f,
    NumericalSyntaxTreeChart.projectIso,NumericalSyntaxTreeChart.literalNormalizedIso,
    Endofunctor.Algebra.isoMk_hom_f,
    IndexAlgebra.firstCarrierIso]
  change 𝟙 (K.obj (SyntacticDerivation.ordinaryTree 𝗣𝗔 R).a) ≫ ((storedJointWordIso R).hom.f.1 ≫
      (wordPresentationIso (NumericalDerivation.rawTreePredicate (interpretedRules R))).hom) =
    (storedJointWordIso R).hom.f.1 ≫
      (wordPresentationIso (NumericalDerivation.rawTreePredicate (interpretedRules R))).hom
  exact CategoryTheory.Category.id_comp _

abbrev storedOneSortWordIso_value := scalar_arrow
  (storedOneSortWordIso R).hom.f (IndexAlgebra.firstCarrierIso (storedJointWordIso R)).hom
  (wordPresentationIso (NumericalDerivation.rawTreePredicate (interpretedRules R))).hom
  (storedOneSortWordIso_first R) (fun x => x.val) (fun x => x.val) (storedJointWordIso_value R)

/-- The ordinary comparison uses the manuscript's actual finite rule
coproduct and the original coefficient objects at each used arity. -/
def ordinaryWordIso : mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R) ≅
    NumericalDerivation.literalOrdinaryTree (interpretedRules R) :=
  StandardCoherence.mappedAlgebraIso R (oneSortAlgebra 𝗣𝗔 σ N) ≪≫
    (AlgebraTransport.functor
      (CategoryTheory.Equivalence.refl : NumericalTuples.Object ≌ NumericalTuples.Object)
      (PolynomialComparison.endofunctorComparison (interpretedRules R))).mapIso (storedOneSortWordIso R)

theorem ordinaryWordIso_first : (ordinaryWordIso R).hom.f = (storedOneSortWordIso R).hom.f := by
  simp only [ordinaryWordIso,Iso.trans_hom,Endofunctor.Algebra.comp_f,CategoryTheory.Functor.mapIso_hom,
    StandardCoherence.mappedAlgebraIso_hom_f,
    AlgebraTransport.functor]
  change 𝟙 (K.obj (SyntacticDerivation.ordinaryTree 𝗣𝗔 R).a) ≫ (storedOneSortWordIso R).hom.f =
    (storedOneSortWordIso R).hom.f
  exact CategoryTheory.Category.id_comp _

abbrev ordinaryWordIso_value := scalar_change (ordinaryWordIso R).hom.f
  (storedOneSortWordIso R).hom.f (ordinaryWordIso_first R)
  (fun x => x.val) (fun x => x.val) (storedOneSortWordIso_value R)

def sourceProofWord : K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left ⟶
    (NumericalDerivation.literalOrdinaryTree (interpretedRules R)).a :=
  K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R) ≫ (ordinaryWordIso R).hom.f

theorem success_inclusion_value {W F : PredicateCategory 𝗣𝗔}
    (v : W ⟶ OptionSyntax.obj F) (x : NumericalTuples.Point (K.obj (SuccessCarrier.carrier v))) :
    ((K.map (representedArrow 𝗣𝗔 (SuccessCarrier.inclusion v))).toFun x).val = x.val := by
  have h := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 ℕ (SuccessCarrier.inclusion v) x
    ((SyntacticLists.F 𝗣𝗔 ℕ).map (representedArrow 𝗣𝗔 (SuccessCarrier.inclusion v)) x)).mp rfl
  exact (congrArg Subtype.val
    (NumericalArithmetic.numericalInterpretation_value (representedArrow 𝗣𝗔 (SuccessCarrier.inclusion v)) x)).trans
      (((SuccessCarrier.inclusionGraph_eval v ℕ _ _).mp h).2.symm)

abbrev sourceProofWord_value := scalar_composition
  (K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R)) (ordinaryWordIso R).hom.f
  (fun x => x.val) (fun x => x.val) (fun x => x.val)
  (success_inclusion_value (SyntacticDerivation.validatorFold 𝗣𝗔 R).f) (ordinaryWordIso_value R)

/-- The word-preserving morphism is the SAME unique algebra morphism as
that used in the already constructed successful pullback comparison. -/
theorem ordinaryWordIso_unique :
    (sourceOrdinaryIso R).hom.f ≫ (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom.f =
      (ordinaryWordIso R).hom.f :=
  congrArg Endofunctor.Algebra.Hom.f
    ((mappedOrdinaryInitial R).hom_ext
      ((sourceOrdinaryIso R).hom ≫ (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom)
      (ordinaryWordIso R).hom)

/-- The original chosen code comparison commutes with the literal word
inclusions. It is not replaced by another carrier bijection. -/
theorem word_square : (interpretationCodeIso R).hom ≫ sourceProofWord R =
    NumericalDerivation.codeWordInclusion (interpretedRules R) := by
  have h := congrArg (fun k => k ≫
      (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom.f)
    (interpretationCarrierIso_tree R)
  have hu := congrArg (fun k => (interpretationCodeIso R).hom ≫
      K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R) ≫ k) (ordinaryWordIso_unique R)
  have ht : (interpretationCodeIso R).hom ≫ K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R) ≫
      (sourceOrdinaryIso R).hom.f ≫ (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom.f =
    NumericalDerivation.codeTreeInclusion (interpretedRules R) ≫
      (NumericalDerivation.ordinaryWordAlgebraIso (interpretedRules R)).hom.f := by
    simpa only [interpretationCodeIso,sourceTreeMap,CategoryTheory.Category.assoc] using h
  exact hu.symm.trans (ht.trans (NumericalDerivation.codeWordInclusion_tree (interpretedRules R)))

private def wordIdentityData (C D W : PredicateCategory 𝗧𝗔)
    (source : NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D)
    (i : NumericalCoordinates.predicateObject C ⟶ NumericalCoordinates.predicateObject W)
    (j : NumericalCoordinates.predicateObject D ⟶ NumericalCoordinates.predicateObject W)
    (hi : ∀ x, (i.toFun x).val = x.val) (hj : ∀ x, (j.toFun x).val = x.val)
    (he : source.hom ≫ j = i) : NumericalRuleRebase.WordIdentityData C D source := by
  have h : ∀ x, (source.hom.toFun x).val = x.val := by
    intro x
    have hh := congrArg (fun k => (k.toFun x).val) he
    exact (hj (source.hom.toFun x)).symm.trans (hh.trans (hi x))
  refine ⟨source,rfl,h,?_⟩
  intro x
  have hh := h (source.inv.toFun x)
  have hinv := congrArg (fun k => (k.toFun x).val) source.inv_hom_id
  exact hh.symm.trans hinv

/-- The checked packet retains the exact original isomorphism and its
proved word laws; opacity prevents normalization of its chosen fold. -/
opaque interpretationWordData : NumericalRuleRebase.WordIdentityData
    (NumericalDerivation.successfulCodes (interpretedRules R))
    ((SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left : PredicateCategory 𝗧𝗔)
    (interpretationCodeIso R) :=
  wordIdentityData (NumericalDerivation.successfulCodes (interpretedRules R))
    ((SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left : PredicateCategory 𝗧𝗔)
    (NumericalDerivation.rawTreePredicate (interpretedRules R)) (interpretationCodeIso R)
    (NumericalDerivation.codeWordInclusion (interpretedRules R)) (sourceProofWord R)
    (NumericalDerivation.codeWordInclusion_value (interpretedRules R)) (sourceProofWord_value R) (word_square R)

abbrev interpretationCodeIso_word_coded := NumericalRuleRebase.WordIdentityData.source_hom_coded
  (NumericalDerivation.successfulCodes (interpretedRules R))
  ((SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left : PredicateCategory 𝗧𝗔)
  (interpretationCodeIso R) (interpretationWordData R)

abbrev interpretationCodeIso_inverse_word_coded := NumericalRuleRebase.WordIdentityData.source_inv_coded
  (NumericalDerivation.successfulCodes (interpretedRules R))
  ((SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left : PredicateCategory 𝗧𝗔)
  (interpretationCodeIso R) (interpretationWordData R)

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.WordsFinal
