/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.BooleanQuotients

/-!
# Consistency and completeness of Boolean presentations

The bound fibers are subobjects, whereas the bound copairing is an arrow.
This module proves the categorical comparison between these two descriptions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness
namespace PresentationLemmas

variable {C : Type u} [Category.{v} C]

@[simp]
theorem desc_coprod [HasBinaryCoproducts C] {A B X : C} (f : A ⟶ X) (g : B ⟶ X) :
    BinaryCofan.IsColimit.desc (coprodIsCoprod A B) f g = coprod.desc f g := by
  apply BinaryCofan.IsColimit.hom_ext (coprodIsCoprod A B)
  · rw [BinaryCofan.IsColimit.inl_desc]; simp
  · rw [BinaryCofan.IsColimit.inr_desc]; simp

/-- The image of a copairing is the join of the two images. -/
theorem image_copair [HasImages C] [HasBinaryCoproducts C]
    {A B X : C} (f : A ⟶ X) (g : B ⟶ X) :
    imageSubobject (coprod.desc f g) = imageSubobject f ⊔ imageSubobject g := by
  apply le_antisymm
  · apply imageSubobject_le _ (coprod.desc
      (factorThruImageSubobject f ≫ Subobject.ofLE _ _ le_sup_left)
      (factorThruImageSubobject g ≫ Subobject.ofLE _ _ le_sup_right))
    apply coprod.hom_ext <;> simp
  · apply sup_le
    · simpa using imageSubobject_comp_le (coprod.inl : A ⟶ A ⨿ B) (coprod.desc f g)
    · simpa using imageSubobject_comp_le (coprod.inr : B ⟶ A ⨿ B) (coprod.desc f g)

/-- In a regular category, an arrow has full image exactly when it is a regular epimorphism. -/
theorem image_eq_top_iff_regularEpi [Regular C] {X Y : C} (f : X ⟶ Y) :
    imageSubobject f = ⊤ ↔ IsRegularEpi f := by
  constructor
  · intro h
    have : IsIso (image.ι f) := (Subobject.isIso_iff_mk_eq_top _).mpr h
    have : IsRegularEpi (factorThruImage f) := inferInstance
    rw [← image.fac f]
    infer_instance
  · intro h
    exact ExtremalEpi.subobject_eq_top f
      (by simpa using imageSubobject_factors_comp_self f (𝟙 X))

/-- If a composite is a regular epimorphism, its second arrow is a regular epimorphism. -/
theorem regularEpi_of_comp [Regular C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsRegularEpi (f ≫ g)] : IsRegularEpi g := by
  have : ExtremalEpi g := ExtremalEpi.mk_of_hasEqualizers g (by
    intro W p i hi _
    exact ExtremalEpi.isIso (f ≫ g) (f ≫ p) i (by simp [Category.assoc, hi]))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Pullback distributes over a binary coproduct in a pre-extensive category. -/
theorem copair_isPullback [FinitaryPreExtensive C] [HasPullbacks C]
    {A B X S P Q : C} (f : A ⟶ S) (g : B ⟶ S) (v : X ⟶ S)
    (p₁ : P ⟶ X) (p₂ : P ⟶ A) (q₁ : Q ⟶ X) (q₂ : Q ⟶ B)
    (hp : IsPullback p₁ p₂ v f) (hq : IsPullback q₁ q₂ v g)
    {d : BinaryCofan P Q} (hd : IsColimit d) :
    IsPullback (BinaryCofan.IsColimit.desc hd p₁ q₁)
      (BinaryCofan.IsColimit.desc hd (p₂ ≫ coprod.inl) (q₂ ≫ coprod.inr))
      v (coprod.desc f g) := by
  let fs : ∀ i, pairFunction A B i ⟶ S := fun i ↦
    match i with | .left => f | .right => g
  let ps : ∀ i, pairFunction P Q i ⟶ X := fun i ↦
    match i with | .left => p₁ | .right => q₁
  let qs : ∀ i, pairFunction P Q i ⟶ pairFunction A B i := fun i ↦
    match i with | .left => p₂ | .right => q₂
  have h := (FinitaryPreExtensive.universal' _ (coprodIsCoprod A B)).isPullback_of_isColimit_left
    fs (coprod.desc f g) v ps qs (fun i ↦ by cases i <;> assumption) hd
    (fun i ↦ by cases i <;> simp [fs, Cofan.inj])
  convert h using 1 <;> first | rfl | apply BinaryCofan.IsColimit.hom_ext hd <;>
    simp [Cofan.IsColimit.desc, qs, Cofan.inj]

set_option backward.isDefEq.respectTransparency false in
/-- Direct image after inverse image is the identity along a regular epimorphism. -/
theorem exists_pullback [Regular C] {X Y : C} (f : X ⟶ Y) [IsRegularEpi f]
    (A : Subobject Y) : (Subobject.«exists» f).obj ((Subobject.pullback f).obj A) = A := by
  have ht : (Subobject.«exists» f).obj ⊤ = ⊤ := by
    apply ExtremalEpi.subobject_eq_top f
    apply (Subobject.factors_iff _ _).mpr
    refine ⟨inv (⊤ : Subobject X).arrow ≫ (Subobject.imageFactorisation f ⊤).F.e, ?_⟩
    change (inv (⊤ : Subobject X).arrow ≫ (Subobject.imageFactorisation f ⊤).F.e) ≫
      (Subobject.imageFactorisation f ⊤).F.m = f
    rw [Category.assoc, (Subobject.imageFactorisation f ⊤).F.fac, IsIso.inv_hom_id_assoc]
  simpa only [top_inf_eq, ht] using
    Regular.exists_inf_pullback_eq_exists_inf f ⊤ A

/-- Inverse image along a regular epimorphism reflects the subobject order. -/
theorem pullback_le_iff [Regular C] {X Y : C} (f : X ⟶ Y) [IsRegularEpi f]
    (A B : Subobject Y) :
    (Subobject.pullback f).obj A ≤ (Subobject.pullback f).obj B ↔ A ≤ B := by
  constructor
  · intro h
    have h' := ((Subobject.«exists» f).map h.hom).le
    simpa only [exists_pullback] using h'
  · intro h
    exact ((Subobject.pullback f).map h.hom).le

/-- Inverse image along a regular epimorphism is injective on subobjects. -/
theorem pullback_injective [Regular C] {X Y : C} (f : X ⟶ Y) [IsRegularEpi f] :
    Function.Injective (Subobject.pullback f).obj := by
  intro A B h
  exact le_antisymm ((pullback_le_iff f A B).mp h.le) ((pullback_le_iff f B A).mp h.ge)

/-- The equalizer defining a bound fiber also gives its pullback square. -/
theorem bound_isPullback [HasFiniteLimits C] {X B : C}
    (q : X ⟶ B) (b : ⊤_ C ⟶ B) :
    IsPullback (equalizer.ι q (terminal.from X ≫ b))
      (terminal.from _) q b := by
  refine ⟨⟨?_⟩, ⟨PullbackCone.isLimitAux' _ (fun s ↦ ?_)⟩⟩
  · simpa using equalizer.condition q (terminal.from X ≫ b)
  · have h : s.fst ≫ q = s.fst ≫ (terminal.from X ≫ b) := by
      simpa [terminalIsTerminal.hom_ext s.snd (terminal.from s.pt)] using s.condition
    refine ⟨equalizer.lift s.fst h, ?_, ?_, ?_⟩
    · simp
    · exact terminalIsTerminal.hom_ext _ _
    · intro m hm _
      apply equalizer.hom_ext
      simpa using hm

/-- Bound fibers are inverse images of the corresponding point subobjects. -/
theorem boundFiber_eq_pullback [HasFiniteLimits C] {X B : C}
    (q : X ⟶ B) (b : ⊤_ C ⟶ B) :
    boundFiber q b = (Subobject.pullback q).obj (Subobject.mk b) :=
  (Subobject.pullback_obj_mk (bound_isPullback q b).flip).symm

/-- An inverse image of the empty subobject is empty when initial objects are strict. -/
theorem pullback_bot [HasPullbacks C] [HasInitial C] [HasStrictInitialObjects C]
    {X Y : C} (f : X ⟶ Y) : (Subobject.pullback f).obj ⊥ = ⊥ := by
  rw [Subobject.bot_eq_initial_to, Subobject.pullback_obj_mk (IsPullback.of_hasPullback _ _)]
  exact Subobject.mk_eq_mk_of_comm _ _ (asIso (pullback.fst (initial.to Y) f))
    ((initialIsInitial.ofStrict (pullback.fst (initial.to Y) f)).hom_ext _ _)

/-- The two fibers cover the presenting object exactly when the bound copairing
is a regular epimorphism. The argument applies to any two global points. -/
theorem complete_iff_regularEpi [Regular C] [FinitaryExtensive C]
    {X B : C} (q : X ⟶ B) [IsRegularEpi q] (b₀ b₁ : ⊤_ C ⟶ B) :
    boundFiber q b₀ ⊔ boundFiber q b₁ = ⊤ ↔ IsRegularEpi (coprod.desc b₀ b₁) := by
  let e₀ := equalizer.ι q (terminal.from X ≫ b₀)
  let e₁ := equalizer.ι q (terminal.from X ≫ b₁)
  let k : equalizer q (terminal.from X ≫ b₀) ⨿ equalizer q (terminal.from X ≫ b₁) ⟶
      (⊤_ C) ⨿ (⊤_ C) :=
    coprod.desc (terminal.from _ ≫ coprod.inl) (terminal.from _ ≫ coprod.inr)
  have hp : IsPullback (coprod.desc e₀ e₁) k q (coprod.desc b₀ b₁) := by
    simpa only [desc_coprod] using
      copair_isPullback b₀ b₁ q e₀ (terminal.from _) e₁ (terminal.from _)
      (bound_isPullback q b₀) (bound_isPullback q b₁) (coprodIsCoprod _ _)
  have hi : imageSubobject (coprod.desc e₀ e₁) = boundFiber q b₀ ⊔ boundFiber q b₁ := by
    rw [image_copair, imageSubobject_mono, imageSubobject_mono]
    rfl
  rw [← hi, image_eq_top_iff_regularEpi]
  constructor
  · intro h
    have hcomp : IsRegularEpi (k ≫ coprod.desc b₀ b₁) := by
      rw [← hp.w]
      infer_instance
    exact regularEpi_of_comp k (coprod.desc b₀ b₁)
  · intro h
    exact Regular.regularEpiIsStableUnderBaseChange.of_isPullback hp.flip h

/-- Intersection of two subobjects is represented by their pullback. -/
theorem inf_eq_pullback [HasPullbacks C] {A B X : C} (f : A ⟶ X) (g : B ⟶ X)
    [Mono f] [Mono g] :
    Subobject.mk f ⊓ Subobject.mk g = Subobject.mk (pullback.fst f g ≫ f) := by
  apply le_antisymm
  · apply Subobject.le_mk_of_comm (pullback.lift
      (Subobject.ofLEMk _ f inf_le_left) (Subobject.ofLEMk _ g inf_le_right) (by simp))
    simp
  · exact le_inf (Subobject.mk_le_mk_of_comm (pullback.fst f g) rfl)
      (Subobject.mk_le_mk_of_comm (pullback.snd f g) pullback.condition.symm)

/-- Disjoint monomorphisms have the initial object as their pullback. -/
theorem initial_isPullback_of_inf_eq_bot [HasPullbacks C] [HasInitial C]
    [HasStrictInitialObjects C] {A B X : C} (f : A ⟶ X) (g : B ⟶ X)
    [Mono f] [Mono g] (h : Subobject.mk f ⊓ Subobject.mk g = ⊥) :
    IsPullback (initial.to A) (initial.to B) f g := by
  rw [inf_eq_pullback, Subobject.bot_eq_initial_to] at h
  let e := Subobject.isoOfMkEqMk (pullback.fst f g ≫ f) (initial.to X) h
  have hI := initialIsInitial.ofStrict e.hom
  exact (IsPullback.of_hasPullback f g).of_iso e (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (hI.hom_ext _ _) (hI.hom_ext _ _)
    (by simp) (by simp)

/-- A pullback with initial vertex represents an empty intersection. -/
theorem inf_eq_bot_of_initial_isPullback [HasPullbacks C] [HasInitial C]
    [InitialMonoClass C] {A B X : C} (f : A ⟶ X) (g : B ⟶ X)
    [Mono f] [Mono g] (h : IsPullback (initial.to A) (initial.to B) f g) :
    Subobject.mk f ⊓ Subobject.mk g = ⊥ := by
  apply bot_unique
  let l := h.lift (Subobject.ofLEMk _ f inf_le_left)
    (Subobject.ofLEMk _ g inf_le_right) (by simp)
  apply Subobject.le_mk_of_comm l
  calc
    l ≫ initial.to X = (l ≫ initial.to A) ≫ f := by simp
    _ = (Subobject.mk f ⊓ Subobject.mk g).arrow := by
      dsimp [l]
      rw [h.lift_fst]
      exact Subobject.ofLEMk_comp inf_le_left

set_option backward.isDefEq.respectTransparency false in
/-- The copairing of two disjoint monomorphisms is a monomorphism. -/
theorem mono_copair_of_disjoint [FinitaryExtensive C] [HasPullbacks C]
    {A B X : C} (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g]
    (h : IsPullback (initial.to A) (initial.to B) f g) :
    Mono (coprod.desc f g) := by
  let dl : BinaryCofan A (⊥_ C) := BinaryCofan.mk (𝟙 A) (initial.to A)
  let dr : BinaryCofan (⊥_ C) B := BinaryCofan.mk (initial.to B) (𝟙 B)
  have hdl : IsColimit dl :=
    ((BinaryCofan.isColimit_iff_isIso_inl initialIsInitial dl).mpr (by
      dsimp [dl]; infer_instance)).some
  have hdr : IsColimit dr :=
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial dr).mpr (by
      dsimp [dr]; infer_instance)).some
  have hl := copair_isPullback f g f (𝟙 A) (𝟙 A) (initial.to A) (initial.to B)
    (IsPullback.of_isLimit (PullbackCone.isLimitMkIdId f)) h hdl
  have hr := copair_isPullback f g g (initial.to B) (initial.to A) (𝟙 B) (𝟙 B)
    h.flip (IsPullback.of_isLimit (PullbackCone.isLimitMkIdId g)) hdr
  have hli : BinaryCofan.IsColimit.desc hdl (𝟙 A) (initial.to A) = 𝟙 A := by
    apply BinaryCofan.IsColimit.hom_ext hdl
    · rw [BinaryCofan.IsColimit.inl_desc]; simp [dl]
    · rw [BinaryCofan.IsColimit.inr_desc]; simp [dl]
  have hri : BinaryCofan.IsColimit.desc hdr (initial.to B) (𝟙 B) = 𝟙 B := by
    apply BinaryCofan.IsColimit.hom_ext hdr
    · rw [BinaryCofan.IsColimit.inl_desc]; simp [dr]
    · rw [BinaryCofan.IsColimit.inr_desc]; simp [dr]
  have hll : BinaryCofan.IsColimit.desc hdl ((𝟙 A) ≫ coprod.inl)
      (initial.to B ≫ coprod.inr) = coprod.inl := by
    apply BinaryCofan.IsColimit.hom_ext hdl
    · rw [BinaryCofan.IsColimit.inl_desc]; simp [dl]
    · rw [BinaryCofan.IsColimit.inr_desc]; simp [dl]
  have hrr : BinaryCofan.IsColimit.desc hdr (initial.to A ≫ coprod.inl)
      ((𝟙 B) ≫ coprod.inr) = coprod.inr := by
    apply BinaryCofan.IsColimit.hom_ext hdr
    · rw [BinaryCofan.IsColimit.inl_desc]; simp [dr]
    · rw [BinaryCofan.IsColimit.inr_desc]; simp [dr]
  rw [hli, hll] at hl
  rw [hri, hrr] at hr
  have hh := copair_isPullback f g (coprod.desc f g) coprod.inl (𝟙 A) coprod.inr (𝟙 B)
    hl.flip hr.flip (coprodIsCoprod A B)
  have hi : BinaryCofan.IsColimit.desc (coprodIsCoprod A B) coprod.inl coprod.inr = 𝟙 (A ⨿ B) := by
    rw [desc_coprod]
    apply coprod.hom_ext <;> simp
  simp only [Category.id_comp, hi] at hh
  exact PullbackCone.mono_of_isLimitMkIdId _ hh.isLimit

set_option backward.isDefEq.respectTransparency false in
/-- In an extensive category, a copairing of monomorphisms is monic exactly when
the corresponding subobjects are disjoint. -/
theorem mono_copair_iff [FinitaryExtensive C] [HasPullbacks C]
    {A B X : C} (f : A ⟶ X) (g : B ⟶ X) [Mono f] [Mono g] :
    Mono (coprod.desc f g) ↔ Subobject.mk f ⊓ Subobject.mk g = ⊥ := by
  constructor
  · intro hm
    have hp := FinitaryExtensive.isPullback_initial_to_binaryCofan (coprodIsCoprod A B)
    apply inf_eq_bot_of_initial_isPullback f g
    simpa only [IsPullback.cone, CommSq.cone, PullbackCone.mk_pt,
      PullbackCone.mk_fst, PullbackCone.mk_snd, pair_obj_left, pair_obj_right,
      coprod.inl_desc, coprod.inr_desc] using
      IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono
      (coprod.inl : A ⟶ A ⨿ B) coprod.inr (coprod.desc f g) hp.cone hp.isLimit)
  · intro h
    exact mono_copair_of_disjoint f g (initial_isPullback_of_inf_eq_bot f g h)

/-- The bound fibers are disjoint exactly when their bound copairing is monic. -/
theorem consistent_iff_mono [Regular C] [FinitaryExtensive C]
    {X B : C} (q : X ⟶ B) [IsRegularEpi q] (b₀ b₁ : ⊤_ C ⟶ B) :
    boundFiber q b₀ ⊓ boundFiber q b₁ = ⊥ ↔ Mono (coprod.desc b₀ b₁) := by
  rw [boundFiber_eq_pullback, boundFiber_eq_pullback, ← Subobject.inf_pullback, mono_copair_iff]
  constructor
  · intro h
    exact pullback_injective q (h.trans (pullback_bot q).symm)
  · intro h
    rw [h, pullback_bot]

end PresentationLemmas

variable {C : Type u} [Category.{v} C]

/-- The copairing of the two Boolean bounds, in the order bottom, top. -/
def BooleanObject.boundCopair [HasTerminal C] [HasBinaryCoproducts C] (B : BooleanObject C) :
    (⊤_ C) ⨿ (⊤_ C) ⟶ B.obj := coprod.desc ⊥ ⊤

namespace BooleanPresentation

variable [Regular C] [FinitaryExtensive C] {X : C}

/-- A presentation is consistent if its two bound fibers are disjoint. -/
def Consistent (q : BooleanPresentation X) : Prop := q.positive ⊓ q.negative = ⊥

/-- A presentation is complete if its two bound fibers cover the presenting object. -/
def Complete (q : BooleanPresentation X) : Prop := q.positive ⊔ q.negative = ⊤

/-- The consistency clause of manuscript Lemma `lem:complete-boolean-presentation`. -/
theorem consistent_iff_mono (q : BooleanPresentation X) :
    q.Consistent ↔ Mono q.algebra.boundCopair := by
  simpa only [Consistent, positive, negative, inf_comm, BooleanObject.boundCopair] using
    PresentationLemmas.consistent_iff_mono q.q ⊥ ⊤

/-- The completeness clause of manuscript Lemma `lem:complete-boolean-presentation`. -/
theorem complete_iff_regularEpi (q : BooleanPresentation X) :
    q.Complete ↔ IsRegularEpi q.algebra.boundCopair := by
  simpa only [Complete, positive, negative, sup_comm, BooleanObject.boundCopair] using
    PresentationLemmas.complete_iff_regularEpi q.q ⊥ ⊤

/-- The isomorphism clause of manuscript Lemma `lem:complete-boolean-presentation`. -/
theorem consistent_complete_iff_isIso (q : BooleanPresentation X) :
    q.Consistent ∧ q.Complete ↔ IsIso q.algebra.boundCopair := by
  rw [consistent_iff_mono, complete_iff_regularEpi]
  constructor
  · rintro ⟨hm, he⟩
    exact isIso_of_regularEpi_of_mono _ (IsRegularEpi.getStruct _)
  · intro h
    exact ⟨inferInstance, inferInstance⟩

end BooleanPresentation

section Incompleteness

universe vA uA w w'

variable {A : Type uA} [Category.{vA} A] [HasBinaryProducts A]
variable {E : PredicateLattice.{vA, uA, w} A} {P : PredicateLattice.{vA, uA, w'} A}
variable [Regular C] [FinitaryExtensive C]

/-- The equivalent bound-copairing conclusion of categorical essential incompleteness,
with the same explicit external representation data as `boolean_quotient_incomplete`. -/
theorem boolean_quotient_boundCopair_not_regularEpi (D : DiagonalData E P)
    (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (represent : ∀ a : ComplementaryPair (E.obj D.U), ∃ g, D.Represents a g)
    {X : C} (identify : P.obj D.S ≃o Subobject X)
    (q : BooleanPresentation X)
    (hpos : identify D.positive = q.positive)
    (hneg : identify D.negative = q.negative)
    (r : BooleanQuotient q.algebra)
    (a b : E.obj D.S)
    (ha : identify (D.embedding.app D.S a) = boundFiber (q.q ≫ r.morphism.hom) ⊤)
    (hb : identify (D.embedding.app D.S b) = boundFiber (q.q ≫ r.morphism.hom) ⊥)
    (consistent : (q.quotient r).Consistent) :
    ¬ IsRegularEpi r.target.boundCopair := by
  intro h
  have complete := (q.quotient r).complete_iff_regularEpi.mpr h
  exact boolean_quotient_incomplete D hU represent identify q hpos hneg r a b ha hb
    consistent complete

end Incompleteness
end CategoricalEssentialIncompleteness
