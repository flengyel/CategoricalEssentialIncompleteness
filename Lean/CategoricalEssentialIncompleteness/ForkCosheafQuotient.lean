/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkActualCosheaves
public import CategoricalEssentialIncompleteness.EnumerableUnderlying
public import CategoricalEssentialIncompleteness.EffectiveForkTotal
public import CategoricalEssentialIncompleteness.EnumerableRelationPaths

/-! # The whole-space value is the tagged-carrier quotient by finite paths -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology

def pushoutQuotientIso {C A B : Type} (r : C ⟶ A) (s : C ⟶ B) :
    pushout r s ≅ Types.Pushout r s :=
  (IsPushout.of_isColimit (c := Types.Pushout.cocone r s)
    (Types.Pushout.isColimitCocone r s)).isoPushout.symm

theorem quotient_eq_iff_paths {C A B : Type} (r : C ⟶ A) (s : C ⟶ B)
    (x y : A ⊕ B) :
    (Quot.mk _ x : Types.Pushout r s)=Quot.mk _ y ↔
      Relation.EqvGen (Types.Pushout.Rel r s) x y :=
  ⟨Quot.eqvGen_exact,Quot.eqvGen_sound⟩

def underlyingDiagram (Y : EffectiveFork.Object) : WalkingSpan ⥤ Type :=
  EffectiveFork.totalDiagram Y ⋙ EnumerableCarriers.underlying

def associatedCosheaf (Y : EffectiveFork.Object) : ActualCoSh :=
  actualCosheafEquivalence.inverse.obj (underlyingDiagram Y)

def associatedWholeIso (Y : EffectiveFork.Object) :
    (associatedCosheaf Y).obj.obj ⊤ ≅
      Types.Pushout ((underlyingDiagram Y).map WalkingSpan.Hom.fst)
        ((underlyingDiagram Y).map WalkingSpan.Hom.snd) :=
  eqToIso (actual_inverse_whole _) ≪≫ pushoutQuotientIso _ _

def taggedCode {A B : EnumerableCarriers.Carrier} :
    {n // n ∈ A.support} ⊕ {n // n ∈ B.support} → ℕ
  | .inl x => 2*x.val
  | .inr y => 2*y.val+1

theorem taggedCode_injective {A B : EnumerableCarriers.Carrier} :
    Function.Injective (taggedCode (A := A) (B := B)) := by
  rintro (x|x) (y|y) h
  · have he : x.val=y.val := by change 2*x.val=2*y.val at h; omega
    exact congrArg Sum.inl (Subtype.ext he)
  · change 2*x.val=2*y.val+1 at h
    omega
  · change 2*x.val+1=2*y.val at h
    omega
  · have he : x.val=y.val := by change 2*x.val+1=2*y.val+1 at h; omega
    exact congrArg Sum.inr (Subtype.ext he)

/-- The ambient numerical edge relation has exactly the manuscript's
tagged pairs; the partial graphs include membership in the c.e. center. -/
def numericEdge (Y : EffectiveFork.Object) (x y : ℕ) : Prop :=
  ∃ z,x%2=0 ∧ y%2=1 ∧
    x/2 ∈ EnumerableCarriers.val Y.leftMap z ∧
    y/2 ∈ EnumerableCarriers.val Y.rightMap z

theorem numericEdge_re (Y : EffectiveFork.Object) :
    REPred (fun p : ℕ × ℕ => numericEdge Y p.1 p.2) := by
  have hl := ClassicalRecursion.partrec_graph_enumerable
    (EnumerableCarriers.val_partrec Y.leftMap)
  have hr := ClassicalRecursion.partrec_graph_enumerable
    (EnumerableCarriers.val_partrec Y.rightMap)
  have hd : Computable (fun x : ℕ => x/2) := Primrec.nat_div.to_comp.comp .id (.const 2)
  have h1 : REPred (fun p : (ℕ × ℕ) × ℕ =>
      p.1.1/2 ∈ EnumerableCarriers.val Y.leftMap p.2) :=
    REPred.comp (Computable.pair (hd.comp (Computable.fst.comp Computable.fst)) Computable.snd) hl
  have h2 : REPred (fun p : (ℕ × ℕ) × ℕ =>
      p.1.2/2 ∈ EnumerableCarriers.val Y.rightMap p.2) :=
    REPred.comp (Computable.pair (hd.comp (Computable.snd.comp Computable.fst)) Computable.snd) hr
  have hm : ComputablePred (fun p : (ℕ × ℕ) × ℕ => p.1.1%2=0 ∧ p.1.2%2=1) :=
    ((Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp Primrec.fst) (.const 2))
      (.const 0)).and
      (Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.fst) (.const 2))
      (.const 1))).computablePred
  exact (hm.to_re.and (h1.and h2)).projection.of_eq
    (fun _ => by simp only [numericEdge,and_assoc])

theorem numeric_paths_re (Y : EffectiveFork.Object) :
    REPred (fun p : ℕ × ℕ => Relation.EqvGen (numericEdge Y) p.1 p.2) :=
  EnumerableRelationPaths.eqvGen_re (numericEdge_re Y)

theorem numericEdge_iff_generators (Y : EffectiveFork.Object) (x y : ℕ) :
    numericEdge Y x y ↔ ∃ c : {n // n ∈ Y.center.support},
      x=taggedCode (A := Y.left) (B := Y.right)
        (.inl ((underlyingDiagram Y).map WalkingSpan.Hom.fst c)) ∧
      y=taggedCode (A := Y.left) (B := Y.right)
        (.inr ((underlyingDiagram Y).map WalkingSpan.Hom.snd c)) := by
  let l : (⟨Y.center⟩ : EnumerableCarriers.Total) ⟶ ⟨Y.left⟩ :=
    ⟨Y.leftMap,Y.left_total⟩
  let r : (⟨Y.center⟩ : EnumerableCarriers.Total) ⟶ ⟨Y.right⟩ :=
    ⟨Y.rightMap,Y.right_total⟩
  change numericEdge Y x y ↔ ∃ c : {n // n ∈ Y.center.support},
    x=2*(EnumerableCarriers.totalFunction l c).val ∧
    y=2*(EnumerableCarriers.totalFunction r c).val+1
  constructor
  · rintro ⟨z,hx,hy,hl,hr⟩
    let c : {n // n ∈ Y.center.support} :=
      ⟨z,EnumerableCarriers.val_source Y.leftMap z _ hl⟩
    have hl' := EnumerableCarriers.totalFunction_mem l c
    have hr' := EnumerableCarriers.totalFunction_mem r c
    have hel := Part.mem_unique hl hl'
    have her := Part.mem_unique hr hr'
    refine ⟨c,?_,?_⟩
    · omega
    · omega
  · rintro ⟨c,rfl,rfl⟩
    refine ⟨c.val,?_,?_,?_,?_⟩
    · omega
    · omega
    · rw [show 2*(EnumerableCarriers.totalFunction l c).val/2=
          (EnumerableCarriers.totalFunction l c).val by omega]
      exact EnumerableCarriers.totalFunction_mem l c
    · rw [show (2*(EnumerableCarriers.totalFunction r c).val+1)/2=
          (EnumerableCarriers.totalFunction r c).val by omega]
      exact EnumerableCarriers.totalFunction_mem r c

theorem numericEdge_iff_image (Y : EffectiveFork.Object) (x y : ℕ) :
    numericEdge Y x y ↔ ∃ u v,
      taggedCode (A := Y.left) (B := Y.right) u=x ∧ taggedCode v=y ∧
      Types.Pushout.Rel ((underlyingDiagram Y).map WalkingSpan.Hom.fst)
        ((underlyingDiagram Y).map WalkingSpan.Hom.snd) u v := by
  rw [numericEdge_iff_generators]
  constructor
  · rintro ⟨c,rfl,rfl⟩
    exact ⟨_,_,rfl,rfl,Types.Pushout.Rel.inl_inr c⟩
  · rintro ⟨_,_,rfl,rfl,⟨c⟩⟩
    exact ⟨c,rfl,rfl⟩

theorem eqvGen_image_iff {α β : Type} (f : α → β) (hf : Function.Injective f)
    (R : α → α → Prop) (x y : α) :
    Relation.EqvGen (fun a b => ∃ u v,f u=a ∧ f v=b ∧ R u v) (f x) (f y) ↔
      Relation.EqvGen R x y := by
  constructor
  · intro h
    letI : Nonempty α := ⟨x⟩
    have hi := Function.leftInverse_invFun hf
    have hm {a b : β} (h : Relation.EqvGen
        (fun a b => ∃ u v,f u=a ∧ f v=b ∧ R u v) a b) :
        Relation.EqvGen R (Function.invFun f a) (Function.invFun f b) := by
      induction h with
      | rel a b h =>
        obtain ⟨u,v,rfl,rfl,h⟩ := h
        rw [hi u,hi v]
        exact Relation.EqvGen.rel u v h
      | refl => exact .refl _
      | symm _ _ _ ih => exact .symm _ _ ih
      | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2
    simpa only [hi x,hi y] using hm h
  · intro h
    induction h with
    | rel a b h => exact .rel _ _ ⟨a,b,rfl,rfl,h⟩
    | refl => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- Equality in the whole-space quotient is exactly the c.e. finite-path relation on its
tagged numerical representatives. -/
theorem quotient_eq_iff_numeric_paths (Y : EffectiveFork.Object)
    (u v : {n // n ∈ Y.left.support} ⊕ {n // n ∈ Y.right.support}) :
    (Quot.mk _ u : Types.Pushout
      ((underlyingDiagram Y).map WalkingSpan.Hom.fst)
      ((underlyingDiagram Y).map WalkingSpan.Hom.snd))=Quot.mk _ v ↔
      Relation.EqvGen (numericEdge Y) (taggedCode u) (taggedCode v) := by
  rw [quotient_eq_iff_paths]
  have he : numericEdge Y=(fun a b => ∃ u v,
      taggedCode (A := Y.left) (B := Y.right) u=a ∧ taggedCode v=b ∧
      Types.Pushout.Rel ((underlyingDiagram Y).map WalkingSpan.Hom.fst)
        ((underlyingDiagram Y).map WalkingSpan.Hom.snd) u v) :=
    funext (fun x => funext (fun y => propext (numericEdge_iff_image Y x y)))
  rw [he]
  exact (eqvGen_image_iff _ taggedCode_injective _ u v).symm

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkTopology
