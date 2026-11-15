/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerAssociatedCategories

/-! # Independent checks of every printed clause of Corollary 9.8 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory RecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46 Miller AssociatedData AssociatedTheories
open AssociatedIncompleteness AssociatedStructure
variable (a : Point)
local instance (P : Total.CanonicalTotal a) : Regular (Over P) := RegularSlices.regular P
local instance (P : Total.CanonicalTotal a) : FinitaryExtensive (Over P) :=
  RegularSlices.finitaryExtensive P
local instance (P : Total.CanonicalTotal a) : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P
local instance (P : Total.CanonicalTotal a) : Regular (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.regular (Over P)
local instance (P : Total.CanonicalTotal a) : FinitaryExtensive (PartialMaps.Tot (Over P)) :=
  SliceInseparability.PartialTotals.extensive (Over P)

example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) : AssociatedCategories.Conclusions a U hc :=
  AssociatedCategories.printed_statement a ha U hExt hc

/-- The universal object covers every actual slice object; the products,
restriction terminal object and splittings belong to that same category. -/
example (U : Theory a) :
    ∃ (products : PCategoryStruct (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))))
      (laws : @PCategory (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))) inferInstance products),
    @PCategory.inducedRestriction (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))) inferInstance products laws =
      (inferInstance : RestrictionCategory (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a)))) ∧
    ∃ (Q : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a)))
      (τ : @PCategoryStruct.nearProd (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))) inferInstance products Q Q ⟶ Q),
    @IsTuringMorphism (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))) inferInstance products laws Q Q Q τ ∧
    (∀ X : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a)), ∃ (j : X ⟶ Q) (s : Q ⟶ X),
      isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = CategoryTheory.RestrictionCategory.rst s) ∧
    (∃ (Z : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))) (toTerminal : ∀ X : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a)), X ⟶ Z),
      (∀ X, isTotal (toTerminal X)) ∧ toTerminal Z = 𝟙 Z ∧
      (∀ {X Y : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))} (f : X ⟶ Y),
        f ≫ toTerminal Y = CategoryTheory.RestrictionCategory.rst f ≫ toTerminal X) ∧
      (∀ {X : PartialMaps.Par (Over (U.val : Total.CanonicalTotal a))} (f : X ⟶ Z), isTotal f → f = toTerminal X)) ∧
    Nonempty (Splits (PartialMaps.Par (Over (U.val : Total.CanonicalTotal a)))) := by
  let d := turingData a U
  exact ⟨d.products, d.laws, d.restriction_eq, d.Q, d.evaluator, d.turing,
    d.universal, ⟨d.terminal, d.terminate, d.terminate_total, d.terminate_self,
      d.terminate_naturality, d.terminate_unique⟩, ⟨d.splittings⟩⟩

example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ (Subobject.pullback (syntaxData a).sentenceNegation).obj U.val = ⊥) :
    (constantTheory a U).val =
      Subobject.mk ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map U.val.arrow) ∧
    ((constantTheory a U).val ⊓ (Subobject.pullback
      ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj (constantTheory a U).val = ⊥) ∧
    ∀ W : FirstOrderReflection.Theory (sliceProofs a (U.val : Total.CanonicalTotal a)),
      (constantTheory a U).val ≤ W.val →
      W.val ⊓ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj W.val = ⊥ →
      W.val ⊔ (Subobject.pullback ((constantFamilyFunctor (U.val : Total.CanonicalTotal a)).map
        (syntaxData a).sentenceNegation)).obj W.val ≠ ⊤ :=
  ⟨constantTheory_value a U, essentially_incomplete a U ha hExt hc⟩

/-- All subobjects of the actual associated total category are quantified;
there is no constant-family or presentation restriction on W. -/
example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) :
    (actualTheoryDomain a U ⊓ (Subobject.pullback (actualNegation a U)).obj
      (actualTheoryDomain a U) = ⊥) ∧
    (∀ W : Subobject ((PartialMaps.totalEquivalence
        (D := Over (U.val : Total.CanonicalTotal a))).functor.obj
          (constantFamily (U.val : Total.CanonicalTotal a) (syntaxData a).sentenceObject)),
      actualTheoryDomain a U ≤ W →
      W ⊓ (Subobject.pullback (actualNegation a U)).obj W = ⊥ →
      W ⊔ (Subobject.pullback (actualNegation a U)).obj W ≠ ⊤) ∧
    SubobjectInseparable (actualTheoryDomain a U)
      ((Subobject.pullback (actualNegation a U)).obj (actualTheoryDomain a U)) :=
  ⟨(actual_essentially_incomplete a U ha hExt hc).1,
    (actual_essentially_incomplete a U ha hExt hc).2,
    actual_domains_inseparable a U ha hExt hc⟩

example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) :
    rst (decision a U hc) =
      (RestrictionSubobjects.domain (inverses a) (U.val ⊔ refutation a U)).hom ∧
    (U.val.arrow.hom ≫ decision a U hc =
      (CategoricalEssentialIncompleteness.Two.constant (U.val : Total.CanonicalTotal a) true).hom) ∧
    ((refutation a U).arrow.hom ≫ decision a U hc =
      (CategoricalEssentialIncompleteness.Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom) ∧
    (rst ((constantFunctor a U).map (decision a U hc)) =
      (constantFunctor a U).map (RestrictionSubobjects.domain (inverses a)
        (U.val ⊔ refutation a U)).hom) ∧
    ((constantFunctor a U).map U.val.arrow.hom ≫
      (constantFunctor a U).map (decision a U hc) =
        (constantFunctor a U).map (CategoricalEssentialIncompleteness.Two.constant (U.val : Total.CanonicalTotal a) true).hom) ∧
    ((constantFunctor a U).map (refutation a U).arrow.hom ≫
      (constantFunctor a U).map (decision a U hc) = (constantFunctor a U).map
        (CategoricalEssentialIncompleteness.Two.constant ((refutation a U) : Total.CanonicalTotal a) false).hom) ∧
    ¬ RestrictionRetraction.HasTotalExtension
      ((constantFunctor a U).map (decision a U hc)) :=
  ⟨decision_domain a U hc, decision_true a U hc, decision_false a U hc,
    family_domain a U hc, family_true a U hc, family_false a U hc,
    no_total_extension a U ha hExt hc⟩

/-- The target theory need only satisfy the printed consistency and
factorization hypotheses; no essential-surjectivity conclusion is assumed. -/
example (ha : IsMiller a) (U : Theory a) (hExt : base a ≤ U.val)
    (hc : U.val ⊓ refutation a U = ⊥) :
    ∀ (U' : Theory a)
      (i : (U.val : Total.CanonicalTotal a) ⟶ (U'.val : Total.CanonicalTotal a)) [Mono i],
      i ≫ U'.val.arrow = U.val.arrow → U'.val ⊓ refutation a U' = ⊥ →
      (postcompose a i).Full ∧ (postcompose a i).Faithful ∧
        PreservesRestriction (postcompose a i) ∧
          (¬ IsIso i → ¬ (postcompose a i).EssSurj) :=
  (AssociatedCategories.printed_statement a ha U hExt hc).comparisons

#print axioms SliceInseparability.underlying_separator
#print axioms SliceInseparability.constant
#print axioms SliceInseparability.noncoverage
#print axioms SliceInseparability.PartialTotals.regular
#print axioms SliceInseparability.PartialTotals.extensive
#print axioms SliceInseparability.PartialTotals.inseparable
#print axioms CompatiblePartialSlices.postcompose_restriction
#print axioms NativeSplitSlices.restriction_ext
#print axioms NativeSplitSlices.constantData
#print axioms NativeSplitSlices.postcomposeData
#print axioms NativeSplitSlices.turingData
#print axioms AssociatedIncompleteness.sliceInitial
#print axioms AssociatedIncompleteness.constantTheory_value
#print axioms AssociatedIncompleteness.evaluatedTheory
#print axioms AssociatedIncompleteness.every_consistent_extension_incomplete
#print axioms AssociatedIncompleteness.essentially_incomplete
#print axioms AssociatedIncompleteness.constant_inseparable
#print axioms AssociatedIncompleteness.actual_domains_inseparable
#print axioms AssociatedIncompleteness.actual_essentially_incomplete
#print axioms AssociatedStructure.source_restriction_eq
#print axioms AssociatedStructure.constantData
#print axioms AssociatedStructure.turingData
#print axioms AssociatedStructure.decision_domain
#print axioms AssociatedStructure.decision_true
#print axioms AssociatedStructure.decision_false
#print axioms AssociatedStructure.family_domain
#print axioms AssociatedStructure.family_true
#print axioms AssociatedStructure.family_false
#print axioms AssociatedStructure.no_total_extension
#print axioms AssociatedStructure.postcompose_full
#print axioms AssociatedStructure.postcompose_faithful
#print axioms AssociatedStructure.postcompose_restriction
#print axioms AssociatedStructure.postcompose_not_essSurj
#print axioms AssociatedCategories.printed_statement
