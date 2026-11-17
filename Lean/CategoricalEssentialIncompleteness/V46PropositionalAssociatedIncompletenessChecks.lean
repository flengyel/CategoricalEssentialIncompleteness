/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PropositionalAssociatedIncompleteness
public import CategoricalEssentialIncompleteness.V46AssociatedSliceCoordinates

/-! # Independent checks of Theorem 5.3 for the standalone Appendix A.6 calculus -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.PropositionalAssociatedIncompletenessChecks
open RestrictionSubobjects PropositionalRuleComparison PropositionalClosureTransfer
open PropositionalAssociatedIncompleteness
universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
  [Regular (Tot C)] [FinitaryExtensive (Tot C)] (m : MonoInverses C)
  {S Z : Tot C} (n : S ⟶ S) (i : S ⨯ S ⟶ S)

example (A : Subobject S) :
    (rules n i A).instances 0 = ((((S ⨯ S) ⨿ ((S ⨯ S) ⨯ S)) ⨿ (S ⨯ S)) ⨿ (A : Tot C)) ∧
    (rules n i A).conclusion 0 = coprod.desc
      (coprod.desc (coprod.desc (ErasureLogicalSchemes.one i) (ErasureLogicalSchemes.two i))
        (ErasureLogicalSchemes.three n i)) A.arrow ∧
    (rules n i A).instances 1 = (⊥_ (Tot C)) ∧
    (rules n i A).premises 2 = prod.lift prod.fst i ∧ (rules n i A).conclusion 2 = prod.snd :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

variable (P : (A : Subobject S) → Endofunctor.Algebra (rules n i A).inference)
  (hP : ∀ A, IsInitial (P A))
  (Q : (U : Tot C) → SliceProofs n i U) (hQ : ∀ U W, IsInitial (Q U W))
  (logicalTheorem : Z ⟶ S) (hZ : IsTerminal Z)
  (factors : ∀ U : Theory n i P, U.val ⊓ (Subobject.pullback n).obj U.val = ⊥ →
    ∃ z : Z ⟶ (U.val : Tot C), z ≫ U.val.arrow = logicalTheorem)
  (U : Theory n i P) (hc : U.val ⊓ (Subobject.pullback n).obj U.val = ⊥)

example {X : Tot C} (a : X ⟶ S) :
    generateFrom n i P a = imageSubobject (P (imageSubobject a)).a.hom := rfl

local notation "Bᵤ" => constantFamilyFunctor (U.val : Tot C)
local notation "b" => FiniteLimitSubobjects.object (Bᵤ) U.val
local instance (T : Tot C) : Regular (Over T) := RegularSlices.regular T
local instance (T : Tot C) : FinitaryExtensive (Over T) := RegularSlices.finitaryExtensive T
local instance (T : Tot C) : PreservesFiniteLimits (constantFamilyFunctor T) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits T

include hP hQ in
example (z : Z ⟶ (U.val : Tot C)) (hZ : IsTerminal Z) :
    imageSubobject (Q _ b).a.hom = b ∧
    ∀ W : Subobject ((Bᵤ).obj S), imageSubobject (Q _ W).a.hom = W →
      let T := SliceSubobjectPredicates.evaluate z hZ W
      imageSubobject (P T).a.hom = T := by
  refine ⟨(constantTheory n i P _ (Q _) (hQ _) U).property, ?_⟩
  intro W hW
  exact (evaluationTheory n i P hP _ z hZ (Q _) ⟨W, hW⟩).property

example (z : Z ⟶ (U.val : Tot C)) (hZ : IsTerminal Z) (A : Subobject S)
    (W : Subobject ((Bᵤ).obj S)) :
    let A' := FiniteLimitSubobjects.object (Bᵤ) A
    let W' := SliceSubobjectPredicates.evaluate z hZ W
    (Consistent n A → Consistent ((Bᵤ).map n) A') ∧
    (Complete n A → Complete ((Bᵤ).map n) A') ∧
    (Consistent ((Bᵤ).map n) W → Consistent n W') ∧
    (Complete ((Bᵤ).map n) W → Complete n W') :=
  ⟨SliceSubobjectPredicates.constant_consistency _ n A,
    SliceSubobjectPredicates.constant_completeness _ n A,
    SliceSubobjectPredicates.evaluate_consistency z hZ n W,
    SliceSubobjectPredicates.evaluate_completeness z hZ n W⟩

section RestrictionDomains
variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

include hP hQ hZ factors hc in
example :
    let δ := (PartialSliceTheoryFamilies.constantFunctor m (U.val : Tot C)).map
      (BooleanPartialDecision.decision m U.val ((Subobject.pullback n).obj U.val) hc)
    ((U.val ⊓ (Subobject.pullback n).obj U.val = ⊥ ∧
      ∀ T : Subobject S, imageSubobject (P T).a.hom = T → U.val ≤ T →
        T ⊓ (Subobject.pullback n).obj T = ⊥ → T ⊔ (Subobject.pullback n).obj T ≠ ⊤) ↔
     (b ⊓ (Subobject.pullback ((Bᵤ).map n)).obj b = ⊥ ∧
      ∀ W : Subobject ((Bᵤ).obj S), imageSubobject (Q _ W).a.hom = W → b ≤ W →
        W ⊓ (Subobject.pullback ((Bᵤ).map n)).obj W = ⊥ →
        W ⊔ (Subobject.pullback ((Bᵤ).map n)).obj W ≠ ⊤)) ∧
    (U.val ⊔ (Subobject.pullback n).obj U.val ≠ ⊤ ↔ ¬ isTotal δ) ∧
    (Inseparable (domain m U.val) (domain m ((Subobject.pullback n).obj U.val)) ↔
      ¬ RestrictionRetraction.HasTotalExtension δ) := by
  let h := associated_incompleteness m n i P hP Q hQ logicalTheorem hZ factors U hc
  refine ⟨?_, h.2.1, (RestrictionSubobjects.inseparable_iff m _ _).trans h.2.2⟩
  constructor
  · rintro ⟨hcons, hbase⟩
    have hs := h.1.mp ⟨hcons, fun T => hbase T.val T.property⟩
    exact ⟨hs.1, fun W hW => hs.2 ⟨W, hW⟩⟩
  · rintro ⟨hcons, hslice⟩
    have hs := h.1.mpr ⟨hcons, fun W => hslice W.val W.property⟩
    exact ⟨hs.1, fun T hT => hs.2 ⟨T, hT⟩⟩

end RestrictionDomains

include hP hQ hZ factors hc in
example {X : Tot C} (a b' : Subobject X) (hab : SubobjectInseparable a b')
    (θ : X ⟶ S) (t : Theory n i P) (ha : a ≤ (Subobject.pullback θ).obj t.val)
    (hb : b' ≤ (Subobject.pullback θ).obj ((Subobject.pullback n).obj t.val)) (ht : t.val ≤ U.val) :
    (b ⊓ (Subobject.pullback ((Bᵤ).map n)).obj b = ⊥ ∧
      ∀ W : Subobject ((Bᵤ).obj S), imageSubobject (Q _ W).a.hom = W → b ≤ W →
        W ⊓ (Subobject.pullback ((Bᵤ).map n)).obj W = ⊥ →
        W ⊔ (Subobject.pullback ((Bᵤ).map n)).obj W ≠ ⊤) ∧
    ¬ RestrictionRetraction.HasTotalExtension
      ((PartialSliceTheoryFamilies.constantFunctor m (U.val : Tot C)).map
        (BooleanPartialDecision.decision m U.val ((Subobject.pullback n).obj U.val) hc)) := by
  have h := associated_reduction m n i P hP Q hQ logicalTheorem hZ factors U hc
    a b' hab θ t ha hb ht
  exact ⟨⟨h.1.1, fun W hW => h.1.2 ⟨W, hW⟩⟩, h.2⟩

local instance (T : Tot C) : PreservesFiniteLimits (AssociatedSliceCoordinates.actualConstant T) :=
  preservesFiniteLimits_of_natIso (AssociatedSliceCoordinates.comparison T)

example :
    (Subobject.map ((AssociatedSliceCoordinates.comparison (U.val : Tot C)).hom.app S)).obj
      (constantTheory n i P _ (Q _) (hQ _) U).val =
        FiniteLimitSubobjects.object (AssociatedSliceCoordinates.actualConstant (U.val : Tot C))
          U.val :=
  AssociatedSliceCoordinates.theory_value _ _

example :
    (PartialSliceTheoryFamilies.constantFunctor m (U.val : Tot C)).map U.val.arrow.hom =
      PartialMaps.ofTotal ((AssociatedSliceCoordinates.actualConstant (U.val : Tot C)).map
        U.val.arrow) :=
  AssociatedSliceCoordinates.actual_map m _ _

#print axioms PropositionalRuleComparison.rules
#print axioms generateFrom
#print axioms extensive
#print axioms logicalMap_law
#print axioms translation
#print axioms generated_le
#print axioms forward_closed
#print axioms backward_closed
#print axioms constantTheory
#print axioms evaluationTheory
#print axioms essential_iff
#print axioms familyDecision
#print axioms associated_incompleteness
#print axioms associated_reduction

end CategoricalEssentialIncompleteness.V46.PropositionalAssociatedIncompletenessChecks
