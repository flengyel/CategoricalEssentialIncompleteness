module

import CategoricalEssentialIncompleteness.V46UltrapowerComparisonChecks
import CategoricalEssentialIncompleteness.V46SignedFirstOrderIncompleteness
import CategoricalEssentialIncompleteness.V46AssociatedClosedTheories
import CategoricalEssentialIncompleteness.V46OracleSeparatorLift
import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46MillerCutReduction
import CategoricalEssentialIncompleteness.V46MillerCanonicalAxiomIncompleteness

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace ReaderTwo

/-- Two arbitrary complementary subobjects in the ambient regular, extensive category. -/
theorem signedClassification {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
    {V X : D} (F : NullaryPresentations V) (A B : Subobject X) (h₀ : A ⊓ B = ⊥)
    (hT : (F.presentation X).Consistent (SignedFirstOrder.theory F A B).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F A B) ↔
    ¬ ∃ C D' : Subobject X, IsCompl C D' ∧ A ≤ C ∧ B ≤ D' := by
  rw [SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F A B h₀ hT]
  constructor
  · rintro ⟨_, hs⟩ ⟨C, D', hcd, hac, hbd⟩
    exact hs ⟨⟨C, D', hcd⟩, hac, hbd⟩
  · intro hs
    refine ⟨h₀, ?_⟩
    rintro ⟨p, hp, hn⟩
    exact hs ⟨p.positive, p.negative, p.complementary, hp, hn⟩

open RestrictionSubobjects RecursionCategory

/-- The separator condition on arbitrary split restriction categories, with the induced bottom and join written out. -/
theorem allSplitDomains {S : Type u} [Category.{v} S] [RestrictionCategory S] [Splits S]
    [Regular (Tot S)] [FinitaryExtensive (Tot S)] (inv : MonoInverses S)
    {V X : Tot S} (F : NullaryPresentations V) (A B : Subobject X) (hAB : A ⊓ B = ⊥)
    (hT : (F.presentation X).Consistent (SignedFirstOrder.theory F A B).val) :
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F A B) ↔
    ¬ ∃ p n : Idem X.obj, (p ⊓ n = orderIso inv X ⊥ ∧ (domainJoins inv).join p n = ⊤) ∧
      domain inv A ≤ p ∧ domain inv B ≤ n :=
  SignedFirstOrder.essential_incomplete_iff_no_complementary_domains inv F A B hAB hT

theorem agreesWithNative {S : Type u} [Category.{v} S] [RestrictionCategory S] [Splits S]
    [Regular (Tot S)] [FinitaryExtensive (Tot S)] [HasZeroMorphisms S] [RestrictionZero S]
    [BinaryJoins S] (inv : MonoInverses S) (X : Tot S) (p n : Idem X.obj) :
    (p ⊓ n = orderIso inv X ⊥ ∧ (domainJoins inv).join p n = ⊤) ↔ Complementary p n :=
  complementaryDomains_iff_complementary inv X p n

/-- Transport of joins only uses the printed standing structures. -/
theorem signedDomains {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
    [HasZeroMorphisms R] [Prodominical R] [Isotype R] (t : PRecursionCategory R)
    [Regular (Tot (SplitObject R))] [FinitaryExtensive (Tot (SplitObject R))]
    (inv : MonoInverses (SplitObject R)) {V X : Tot (SplitObject R)}
    (F : NullaryPresentations V) (A B : Subobject X) (hAB : A ⊓ B = ⊥)
    (hT : (F.presentation X).Consistent (SignedFirstOrder.theory F A B).val) :
    letI := domainJoins inv
    (F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F A B) ↔
    ¬ ∃ P N : Idem X.obj, Complementary P N ∧ domain inv A ≤ P ∧ domain inv B ≤ N :=
  SignedFirstOrder.essential_incomplete_iff_no_domain_separator t inv F A B hAB hT

section Slice
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
local instance (U : D) : Regular (Over U) := RegularSlices.regular U
local instance (U : D) : FinitaryExtensive (Over U) := RegularSlices.finitaryExtensive U
local instance (U : D) : PreservesFiniteLimits (constantFamilyFunctor U) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits U
variable {V U Z : D} (P : FirstOrderPresentation V) (Q : AssociatedClosedTheories.SliceProofs P U)
    (hQ : ∀ C, IsInitial (Q C)) (t : Z ⟶ U) (hz : IsTerminal Z)

include hQ t hz

/-- An arbitrary closed slice extension yields a closed base theory with the evaluated underlying subobject. -/
theorem closedEvaluation (W : FirstOrderReflection.Theory Q) :
    ∃ B : P.Theories, B.val = SliceSubobjectPredicates.evaluate t hz W.val :=
  ⟨AssociatedClosedTheories.evaluationTheory P U Q hQ t hz W, rfl⟩

/-- Essential incompleteness quantifies over every closed extension in the slice. -/
theorem sliceExtensions (T : P.Theories) (h : P.EssentiallyIncomplete T)
    (W : FirstOrderReflection.Theory Q)
    (hw : (AssociatedClosedTheories.constantTheory P U Q hQ T).val ≤ W.val)
    (cw : AssociatedClosedTheories.Consistent P U W.val) :
    ¬ AssociatedClosedTheories.Complete P U W.val :=
  ((AssociatedClosedTheories.essential_incomplete_iff P U Q hQ t hz T h.1).mp h).2 W hw cw
end Slice

open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open OracleComputation OracleComputation.Restricted

/-- Fixing a second component still gives the reduction, and the diagonal law holds for every component. -/
theorem arbitrarySecond (n : ℕ) : ∀ a : ℕ,
    (ordinaryDiagonal (Nat.pair (Encodable.encode (simulationCode n)) a) =
      (ordinaryEval n n).map (fun _ => 0)) ∧
    (n ∈ K ↔ Nat.pair (Encodable.encode (simulationCode n)) a ∈ A) :=
  fun a => ⟨ordinaryDiagonal_simulation n a, K_iff_simulation_mem_A n a⟩

/-- The right tag detects membership even when either summand carries arbitrary values. -/
theorem conditionalConsequences (s : ℕ →. (ℕ ⊕ ℕ))
    (left : ∀ n, (∃ y : ℕ, Sum.inl y ∈ s n) ↔ n ∉ A)
    (right : ∀ n, (∃ y : ℕ, Sum.inr y ∈ s n) ↔ n ∈ A) :
    (∀ n, (s n).Dom) ∧ (¬ ∃ f : ℕ → ℕ ⊕ ℕ, Computable f ∧ s = fun n => Part.some (f n)) ∧
      ¬ ∃ f : N K ⟶ coprod (N K) (N K), (inclusion K).map f = s := by
  obtain ⟨ht, hc⟩ := total_and_noncomputable_of_output_summands s left right
  exact ⟨ht, hc, no_lift_of_output_summands s left right⟩

/-- The target endomorphism in the earlier comparison has no source preimage. -/
theorem absentEndomorphism (f : N K ⟶ N K) : (inclusion K).map f ≠
    missingSection ≫ ((inclusion K).mapIso (parityIso K)).inv :=
  fun h => missingSection_endomorphism_has_no_lift ⟨f, h⟩

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open ArithmeticUniformIndependent NamedArithmeticSignature

/-- Choose the uniform morphism before the index and before the consistency hypothesis. -/
theorem oneSentenceMorphism :
    ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
      ∀ e, Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e)) →
      ∃ φ : Formula, φ.freeVariables = [] ∧
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val = formulaCode φ ∧
        ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) φ ∧
        ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) (.neg φ) := by
  obtain ⟨q, hq⟩ := uniform_independent_sentences
  refine ⟨q, fun e hc => ?_⟩
  obtain ⟨φ, hφ, he, hp, hn⟩ := hq e hc
  exact ⟨φ, hφ, he.symm, hp, hn⟩

open Filter ArithmeticUltrapower

/-- Łoś at a unary object predicate, a chosen binary graph, and each PA axiom. -/
theorem losApplications {I : Type} (U : Ultrafilter I) {C D : SyntacticPredicates.Carrier}
    (f : GraphMorphism 𝗣𝗔 C D) (x : I → PredicateInterpretation.Obj ℕ C)
    (r : I → ℕ) (φ : ArithmeticSentence) (hφ : φ ∈ 𝗣𝗔) :
    (C.val.Evalb (M := Model U) ![Germ.ofFun r] ↔ ∀ᶠ i in (U : Filter I), C.val.Evalb ![r i]) ∧
    f.graph.val.Evalb (M := Model U) ![Germ.ofFun (fun i => (x i).val),
      Germ.ofFun (fun i => (PredicateInterpretation.value 𝗣𝗔 ℕ f (x i)).val)] ∧
    (Model U)↓[ℒₒᵣ] ⊧ φ :=
  ⟨ArithmeticUltrapower.Checks.unary_predicate U C r, ArithmeticUltrapower.Checks.graph_value U f x,
    ArithmeticUltrapower.Checks.pa_axiom U φ hφ⟩

open Miller

/-- The existence witness meets each oracle-name condition and admits both cuts by one computable map. -/
theorem witnessedCuts : ∃ (a : ℕ → Set.Icc (0 : ℝ) 1) (h : ℕ → ℕ),
    (∀ (d : ℕ) (r : Set.Icc (0 : ℝ) 1),
      (∀ p : ℕ → Fin 2, rho p = a → ∀ k : ℕ, ∃ i : ℕ,
        i ∈ OracleProgram.numberedEval d p k ∧ |(Rationals.q i : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) →
      a d = r) ∧ Computable h ∧
    (∀ e, h e ∈ CutDigits.lowerCut a ↔ ∃ m, m ∈ Unanimity.tau a e e ∧ m % 2 = 0) ∧
    (∀ e, h e ∈ CutDigits.upperCut a ↔ ∃ m, m ∈ Unanimity.tau a e e ∧ m % 2 = 1) := by
  obtain ⟨a, ha⟩ := exists_isMiller
  obtain ⟨h, hc, hl, hr⟩ := Cut.printed_cut_reduction a ha
  exact ⟨a, h, ha, hc, fun e => Set.ext_iff.mp hl e, fun e => Set.ext_iff.mp hr e⟩

section EveryAxiomSubobject
attribute [local instance 2000] Uniform.nativeRestriction
open CanonicalAxiomIncompleteness
local notation "PVar" => (NamedPostfixEncoding.variableCarrier : PredicateCategory 𝗣𝗔)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d₀" => OrderedFieldSyntax.bound

theorem witnessedAxiomTheories : ∃ a : Point, IsMiller a ∧
    ∀ {Y : Total.CanonicalTotal a} (m : Y ⟶ (NamedSyntaxComparison.canonicalPresentedSyntax a PVar σ π d₀).sentenceObject) [Mono m],
      RealClosedBounds.Extends a (recoveredCodes a m) →
      TheoryDomainApplication.Consistent (recoveredCodes a m) →
      Inseparable (theoremIdem a m) (refutationIdem a m) ∧ theoremIdem a m ⊔ refutationIdem a m ≠ ⊤ := by
  obtain ⟨a, ha⟩ := exists_isMiller
  refine ⟨a, ha, ?_⟩
  intro Y m _ he hc
  exact printed_essential_incompleteness_of_consistent a m ha he hc
end EveryAxiomSubobject

#print axioms signedClassification
#print axioms allSplitDomains
#print axioms agreesWithNative
#print axioms losApplications
#print axioms signedDomains
#print axioms closedEvaluation
#print axioms sliceExtensions
#print axioms arbitrarySecond
#print axioms conditionalConsequences
#print axioms absentEndomorphism
#print axioms oneSentenceMorphism
#print axioms witnessedCuts
#print axioms witnessedAxiomTheories

end ReaderTwo
