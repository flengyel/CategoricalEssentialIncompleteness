/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticObservations
public import CategoricalEssentialIncompleteness.SyntacticExtension
public import CategoricalEssentialIncompleteness.V46PartialMapTheory

/-! # Validity subobjects and observations in arithmetic models -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type*} [Category* D] [Regular D]
variable {C : Type*} [Category* C] [RestrictionCategory C] [Ranges C]
variable [CoprodStruct C] [CategoryTheory.HasCoproducts C] [HasZeroMorphisms C]
variable [CoprodStruct (Par D)] [CategoryTheory.HasCoproducts (Par D)] [HasZeroMorphisms (Par D)]

/-- The interpreted sentence theory in Proposition 4.1 factors uniquely through any
validity subobject through which the interpreted conclusion factors. -/
theorem interpreted_theory_unique_factor (G : RangeFunctor C (Par D)) {P T S : C}
    (c : P ⟶ S) (hc : isTotal c) (m : T ⟶ S) (hm : isTotal m)
    (r : S ⟶ T) (t : Idem S) (ht : t = Ranges.range c)
    (hmr : m ≫ r = 𝟙 T) (hrm : r ≫ m = t.hom)
    {V : D} (v : V ⟶ (G.toFunctor.obj S).obj) [Mono v] (k : (G.toFunctor.obj P).obj ⟶ V)
    (hfac : k ≫ v = totalValue (G.toFunctor.map c) (G.map_total c hc)) :
    ∃! w : (G.toFunctor.obj T).obj ⟶ V,
      w ≫ v = totalValue (G.toFunctor.map m) (G.map_total m hm) := by
  obtain ⟨w, hw⟩ := (interpreted_theory_subobject G c hc m hm r t ht hmr hrm v k hfac).2
  exact ⟨w, hw, fun z hz => (cancel_mono v).mp (hz.trans hw.symm)⟩

end CategoricalEssentialIncompleteness.V46.PartialMaps

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

private def objectPoint : (X : STObjectCode) → interpretedType ℕ X
  | .omega => (0 : ℕ)
  | .product X Y => (objectPoint X, objectPoint Y)
  | .coproduct X _ => Sum.inl (objectPoint X)

/-- The faithful family in Theorem D.1 sends each object identity to a nonzero morphism. -/
theorem family_identity_ne_zero (hT : Consistent T) (X : CodedProgramCategory T) :
    (familyFunctor T).map (𝟙 X) ≠ 0 := by
  obtain ⟨s⟩ := modelIndex_nonempty T hT
  rw [(familyFunctor T).map_id]
  intro he
  let x := objectPoint (objectCode X)
  have h := congrFun (congrFun he s) x
  change Part.some x = Part.none at h
  exact Part.notMem_none x (h ▸ Part.mem_some x)

/-- Each numeral observation of a restriction idempotent in Appendix D is still an
observation of its image under extension of the arithmetic theory. -/
theorem observation_extension (T' : ArithmeticTheory) [𝗣𝗔 ⪯ T'] [T ⪯ T']
    (c : Idem (omegaObject T)) :
    observation T c ⊆ observation T' ((SyntacticExtension.rangeFunctor T T').mapIdem c) := by
  intro n hn
  change kappa T n ≫ c.hom = kappa T n at hn
  have h := congrArg (SyntacticExtension.functor T T').map hn
  rw [Functor.map_comp] at h
  have hk : (SyntacticExtension.functor T T').map (kappa T n) = kappa T' n :=
    SyntacticExtension.map_index T T' .omega .omega (UniformRange.rangeConstantIndex n)
  rw [hk] at h
  exact h

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.interpreted_theory_unique_factor
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel.family_identity_ne_zero
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel.observation_extension
