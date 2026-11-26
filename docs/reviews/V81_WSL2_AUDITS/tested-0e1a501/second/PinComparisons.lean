module

import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory
import CategoricalEssentialIncompleteness.V46TuringObjectRecognition
import CategoricalEssentialIncompleteness.V46Comparison
import CategoricalEssentialIncompleteness.V46SignedSubobjectIncompleteness
import CategoricalEssentialIncompleteness.V46SliceUnitFactorization
import CategoricalEssentialIncompleteness.V46SelectorGraph
import CategoricalEssentialIncompleteness.V46ArithmeticUltrapower
import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
import CategoricalEssentialIncompleteness.V46MillerFixedPoint
import CategoricalEssentialIncompleteness.V46ForkUndecidedAtoms
import CategoricalEssentialIncompleteness.V46FiniteBooleanPowers
import CategoricalEssentialIncompleteness.V46ForkDiagonalObstructionTuples
import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46SyntacticNonLocalConnectedness
import CategoricalEssentialIncompleteness.V46ArithmeticSignedConsistencyPA

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.LocalConnectedness
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
universe v u w
namespace SecondReading.Tested

-- The deciding predicate takes native proof words in the fixed equivalence-relation language.
example {P N : Set ℕ} (h : Disjoint P N) :
    (∀ U : Theory Janiczak.FOL.L, Janiczak.FOL.theory (Janiczak.Signed P N) ⊆ U →
      Entailment.Consistent U → ¬ ComputablePred (fun w : ℕ =>
        ∃ φ : Sentence Janiczak.FOL.L, Encodable.encode φ = w ∧ U ⊢ φ)) ↔
      (Disjoint P N ∧ ¬ ∃ C : Set ℕ, ComputablePred (· ∈ C) ∧ P ⊆ C ∧ Disjoint C N) :=
  Janiczak.FOL.signed_essentiallyUndecidable_iff h

-- §4's Visser comparison at an arbitrary recursively encoded first-order language.
open FFL.Entailment in
theorem undecidable_extensions_of_reduction {L : FFL.FirstOrder.Language} [Encodable (Sentence L)]
    (T : Theory L) (P N : Set ℕ) (hs : Numerical.RecursivelyInseparable P N)
    (f : ℕ → Sentence L) (hf : Computable fun n => Encodable.encode (f n))
    (hp : ∀ n ∈ P, T ⊢ f n) (hn : ∀ n ∈ N, T ⊢ ∼(f n)) :
    ∀ U : Theory L, T ⊆ U → Entailment.Consistent U →
      ¬ ComputablePred (fun w : ℕ => ∃ φ : Sentence L, Encodable.encode φ = w ∧ U ⊢ φ) := by
  intro U inc hc dec
  let D : Set ℕ := {n | U ⊢ f n}
  have decidableD : ComputablePred (· ∈ D) := by
    apply ComputablePred.computable_of_manyOneReducible _ dec
    refine ⟨_,hf,?_⟩
    intro n
    constructor
    · exact fun h => ⟨f n,rfl,h⟩
    · rintro ⟨φ,e,h⟩
      change U ⊢ f n
      exact Encodable.encode_inj.mp e ▸ h
  have grows := Theory.Proof.weakerThan_of_le inc
  exact hs.2 ⟨D,decidableD,(fun n h => grows.wk (hp n h)),Set.disjoint_left.mpr
    (fun n hd he => (consistent_iff_unprovable_bot.mp hc)
      (neg_mdp (grows.wk (hn n he)) (show U ⊢ f n from hd)))⟩

section Evaluators
open PCategoryStruct
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
example (U : C) (τ : nearProd U U ⟶ U) (universal : RecursionCategory.IsTuringMorphism τ)
    (embeddings : ∀ A : C, ∃ (m : A ⟶ U) (r : U ⟶ A), isTotal m ∧ m ≫ r = 𝟙 A) :
    ∀ A B : C, ∃ t : nearProd U A ⟶ B, RecursionCategory.IsTuringMorphism t :=
  (turingObject_iff U).mpr ⟨⟨τ, universal⟩, embeddings⟩
end Evaluators

section Comparison
open PCategoryStruct CategoryTheory.CoprodStruct
variable {R : Type u} {A : Type w} [Category R] [Category A]
variable [PCategoryStruct R] [PCategory R] [RestrictionCategory A]
variable [HasZeroMorphisms R] [RestrictionZero R] [HasZeroMorphisms A] [RestrictionZero A]
variable [CoprodStruct R] [CategoryTheory.HasCoproducts R] [RestrictionCoproducts R]
variable [CoprodStruct A] [CategoryTheory.HasCoproducts A] [RestrictionCoproducts A] [Ranges R] [Ranges A]
example {U : R} (τ : nearProd U U ⟶ U) (univ : RecursionCategory.IsTuringMorphism τ)
    (b : U ≅ coprod U U) (F : RangeFunctor R A) (P N : Idem (F.toFunctor.obj U))
    (p : F.mapIdem (diagonal0 τ b) ≤ P) (n : F.mapIdem (diagonal1 τ b) ≤ N)
    (hd : P ⊓ N = ⊥) (ℓ : U ⟶ coprod U U)
    (s : F.toFunctor.obj U ⟶ coprod (F.toFunctor.obj U) (F.toFunctor.obj U))
    (left : Idem.pull s (summand0 _ _) = N) (right : Idem.pull s (summand1 _ _) = P)
    (lift : F.toFunctor.map ℓ = s ≫ (F.comparison U U).hom) :
    ∃ g : U ⟶ U, isTotal g ∧ Idem.pull (F.toFunctor.map g) P = ⊥ ∧
      Idem.pull (F.toFunctor.map g) N = ⊥ :=
  comparison_zero_inverse_images F τ univ b P N hd p n s left right ℓ lift
end Comparison

section Signed
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D] {X V : D}
example (F : NullaryPresentations V) (a b : Subobject X)
    (h : a ⊓ b = ⊥) (hc : (F.presentation X).Consistent (SignedFirstOrder.theory F a b).val) :
    ((F.presentation X).EssentiallyIncomplete (SignedFirstOrder.theory F a b)) ↔
        ¬ HasSubobjectSeparator a b := by
  rw [SignedFirstOrder.essential_incomplete_iff_subobject_inseparable F a b h hc]
  exact ⟨fun k => k.2, fun k => ⟨h,k⟩⟩
end Signed

section Slices
open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U : Tot C}
example (i : T ⟶ U) [Mono i] (r : MonoInverses C) (Y : PartialMaps.Par (Over U)) :
    (∃ k : Y.obj.left ⟶ T, k ≫ i = Y.obj.hom) ↔
      isTotal ((PartialSliceChangeBase.rightAdjunction i r).unit.app Y) :=
  (PartialSliceChangeBase.right_unit_total_iff i r Y).symm
end Slices

section Selector
open FiniteSigmaOne SyntacticPredicates
example {s : ℕ} (L : 𝚺₁.Semisentence 2) (D : Fin s → FiniteSigmaOne.Carrier)
    {M : Type u} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (w : M) :
    (∀ i < len w, ∃ j : Fin s, L.val.Evalb ![nth w i, ORingStructure.numeral j.val] ∧
       (D j).val.Evalb ![nth w i]) ↔ (finiteMembership (selectedEntry L D)).val.Evalb ![w] :=
  (selected_entries_model L D w).symm
end Selector

example {I : Type} (U : Ultrafilter I) :
    (ArithmeticUltrapower.Model U)↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ArithmeticUltrapower.modelsPA U

section UniformArithmetic
open ArithmeticUniformIndependent NamedArithmeticSignature
example : ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
    ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system (gamma e)) →
    ∃ φ : NamedArithmeticSignature.Formula,
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val = formulaCode φ ∧
      φ.freeVariables = [] ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) (.neg φ) ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound (gamma e) φ := by
  obtain ⟨q,h⟩ := uniform_independent_sentences
  exact ⟨q, fun e he => by obtain ⟨φ,closed,coded,positive,negative⟩ := h e he
                           exact ⟨φ,coded.symm,closed,negative,positive⟩⟩
end UniformArithmetic

-- The existential sequence is required before the oracle, the index and the real are supplied.
example : ∃ a : ℕ → Set.Icc (0 : ℝ) 1, ∀ (d : ℕ) (r : Set.Icc (0 : ℝ) 1),
    (∀ p : ℕ → Fin 2, Miller.rho p = a → ∀ k : ℕ, ∃ i : ℕ,
      i ∈ Miller.OracleProgram.numberedEval d p k ∧
      |((Miller.Rationals.q i : ℚ) : ℝ) - (r : ℝ)| < ((2 : ℝ)^k)⁻¹) → a d = r :=
  Miller.exists_isMiller

section Fork
open ForkSyntax ForkAxiomClosure EnumerableCarriers
example (i : Bool) (A : Set ℕ) (hA : REPred (· ∈ A))
    (ext : support (endpointTheory i categoricalTheory) ⊆ theoremCodes A)
    (c : ∀ φ : ForkSyntax.Formula, ¬(Derives A φ ∧ Derives A (.neg φ))) :
    ∃ k : ℕ, ¬ Derives A (.neg (.atom k)) ∧ ¬ Derives A (.atom k) := by
  obtain ⟨k,hp,hn⟩ := axioms_undecided_atom i A hA ext c
  exact ⟨k,hn,hp⟩
end Fork

example {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D] :
    ∀ n : ℕ, IsColimit (Cofan.mk (finitePower (Two D) n) (BooleanPowers.vertex n)) :=
  fun n => BooleanPowers.isColimit n

open ForkDiagonalObstruction in
example (d : tupleDiagram ⨯ tupleDiagram ⟶ Two NumericalForkPartialMaps.Diagram) :
    ¬ IsPullback (prod.lift (𝟙 tupleDiagram) (𝟙 tupleDiagram)) (terminal.from tupleDiagram)
      d (coprod.inr : ⊤_ NumericalForkPartialMaps.Diagram ⟶ Two NumericalForkPartialMaps.Diagram) :=
  no_diagonal_pullback d

open OracleComputation OracleComputation.Restricted in
example : ∃ s : ℕ → ℕ → ℕ, Computable₂ s ∧ ∀ (A : Set ℕ) e z x,
    (Miller.OracleProgram.numberedEval (s e z) (bits A) x).Dom ↔
    (Miller.OracleProgram.numberedEval e (bits A) (Nat.pair z x)).Dom :=
  ⟨sectionIndex,sectionIndex_computable,machine_section⟩

open FailureOfComposition FFL.Entailment in
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T]
    (h : REPred (FailureOfComposition.AxiomCodes T)) :
    ¬ LocallyConnected (PrintedObjectCoding.NormalizedCategory T) :=
  ConnectedNumeralDomains.normalized_not_locallyConnected T h

example {V : SyntacticPredicates.PredicateCategory 𝗣𝗔}
    (S : CategoricalSyntax V (fun _ => ⊥_ _) (fun _ => PrintedObjectCoding.Number) 0) :
    𝗣𝗔 ⊢ ArithmeticSignedTheoryTruth.consistencySentence S :=
  ArithmeticSignedTheoryTruth.consistency_PA S

end SecondReading.Tested
