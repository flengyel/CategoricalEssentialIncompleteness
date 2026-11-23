/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleTuring

/-! # Specialization of the fork evaluator on tuple parameter carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open FailureOfComposition.Kleene (eval)
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

universe u v u' v'
section
variable {A : Type u} [Category.{v} A] [RestrictionCategory A]
variable {B : Type u'} [Category.{v'} B] [RestrictionCategory B]
variable (F : A ⥤ B) [F.Full] [F.Faithful] (hF : PreservesRestriction F)
variable (D : RestrictionProducts.ProductData B) (P : A → A → A)
variable (i : ∀ X Y, F.obj (P X Y) ≅ D.prod (F.obj X) (F.obj Y))

private theorem parameterizes {X Q : A} {V : B} (e : F.obj Q ≅ V) (t : D.prod V V ⟶ V)
    (f : P X Q ⟶ Q) (p : F.obj X ⟶ V)
    (h : D.map p (𝟙 V) ≫ t = D.map (𝟙 (F.obj X)) e.inv ≫ (i X Q).inv ≫ F.map f ≫ e.hom) :
    (FullRestrictionProducts.restrictionProducts F hF D P i).map (F.preimage (p ≫ e.inv)) (𝟙 Q) ≫
      FullRestrictionProducts.evaluator F D P i Q (TuringRestrictionEquivalence.conjugate D e t) = f := by
  let E := FullRestrictionProducts.restrictionProducts F hF D P i
  have hp : D.map (p ≫ e.inv) (𝟙 (F.obj Q)) ≫ D.map e.hom e.hom =
      D.map (𝟙 (F.obj X)) e.hom ≫ D.map p (𝟙 V) := by
    rw [D.map_comp, D.map_comp]
    simp
  have he : D.map (𝟙 (F.obj X)) e.hom ≫ D.map (𝟙 (F.obj X)) e.inv = 𝟙 _ := by
    rw [D.map_comp]
    simp [D.map_id]
  apply F.map_injective
  rw [F.map_comp]
  change F.map (E.map (F.preimage (p ≫ e.inv)) (𝟙 Q)) ≫
    F.map (F.preimage ((i Q Q).hom ≫ D.map e.hom e.hom ≫ t ≫ e.inv)) = F.map f
  rw [F.map_preimage, ← Category.assoc, FullRestrictionProducts.map_comparison,
    F.map_preimage, F.map_id, Category.assoc, ← Category.assoc (D.map _ _), hp,
    Category.assoc, ← Category.assoc (D.map p _), h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc (D.map _ _), he, Category.id_comp, Iso.hom_inv_id_assoc]
end

theorem endpoint_parameterizes {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint) :
    tupleProducts.map (endpointParameter f) (𝟙 endpoint) ≫ endpointTau = f :=
  parameterizes tupleCode tupleCode_restriction codedTupleProducts tupleProduct tupleProductIso
    endpointIso EffectiveFork.endpointEvaluator f _ (EffectiveFork.endpoint_parameterization (endpointProgram f))

theorem endpointIndex_value {Z : TupleSpans} (f : tupleProduct Z endpoint ⟶ endpoint)
    (z : NumericalTuples.Point Z.obj) (x : ℕ) :
    eval (endpointIndex f (NumericalTuples.code _ z.val)) x = binaryValue f (NumericalTuples.code _ z.val) x := by
  let n := NumericalTuples.code _ z.val
  have hs : n ∈ (tupleCode.obj Z).support := (NumericalTuples.code_mem_codedSupport Z.obj z.val).mpr z.property
  have hi : EnumerableCarriers.val (EnumerableCarriers.partialProdMap (𝟙 (tupleCode.obj Z)) endpointIso.inv)
        (Nat.pair n x) = Part.some (Nat.pair n x) := by
    apply Part.eq_some_iff.mpr
    rw [EnumerableCarriers.mem_partialProdMap_iff]
    simp [EnumerableCarriers.val_id, mem_supportIdentity, labelCode_inv, hs]
  rw [endpointIndex, EffectiveFork.eval_specialize, EffectiveFork.eval_program]
  apply Part.ext
  intro y
  unfold endpointProgram
  rw [← Category.assoc (tupleProductIso Z endpoint).inv]
  change y ∈ EnumerableCarriers.val
      (EnumerableCarriers.partialProdMap (𝟙 (tupleCode.obj Z)) endpointIso.inv ≫
        ((tupleProductIso Z endpoint).inv ≫ tupleCode.map f) ≫ endpointIso.hom) (Nat.pair n x) ↔ _
  simp only [binaryValue, EnumerableCarriers.mem_val_comp, hi, Part.mem_some_iff, labelCode_hom,
    exists_eq_left, exists_eq_right']
  rfl

def forkProgram {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) :
    EffectiveFork.product (forkCode.obj Y) EffectiveFork.V ⟶ EffectiveFork.V :=
  EffectiveFork.productMap (𝟙 _) labelIso.inv ≫ (forkProductIso Y universal).inv ≫ forkCode.map f ≫ labelIso.hom

def forkParameter {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) : Y ⟶ universal :=
  forkCode.preimage (EffectiveFork.parameter (forkProgram f) ≫ labelIso.inv)

theorem forkParameter_total {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) :
    isTotal (forkParameter f) := by
  apply PreservesRestriction.reflects_total (F := forkCode) forkCode_restriction
  rw [forkParameter, forkCode.map_preimage]
  exact isTotal_comp (EffectiveFork.parameter_total _) (iso_total labelIso.symm)

theorem fork_parameterizes {Y : ForkSpans} (f : forkProduct Y universal ⟶ universal) :
    forkProducts.map (forkParameter f) (𝟙 universal) ≫ tau = f :=
  parameterizes forkCode forkCode_restriction codedForkProducts forkProduct forkProductIso
    labelIso EffectiveFork.tau f _ (EffectiveFork.tau_parameterization (forkProgram f))

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
