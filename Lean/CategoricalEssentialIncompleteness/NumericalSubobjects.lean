/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEmbedding
public import CategoricalEssentialIncompleteness.NumericalDomains
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Support inclusions as PER subobjects

An arbitrary inclusion of supports is a monomorphism between equality PERs.
Its subobject order reflects precisely inclusion of supports. Restriction
domains therefore embed into PER subobjects, with image exactly the
c.e. support inclusions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def inclusionRepresentative {A B : Set ℕ} (h : A ⊆ B) :
    Representative (discrete A) (discrete B) where
  val := Part.some
  computable := Partrec.some
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b hn ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact ⟨h hn.1, hn.2⟩

def inclusion {A B : Set ℕ} (h : A ⊆ B) : discrete A ⟶ discrete B :=
  ofRepresentative (inclusionRepresentative h)

@[simp] theorem inclusion_comp {A B C : Set ℕ} (h : A ⊆ B) (k : B ⊆ C) :
    inclusion h ≫ inclusion k = inclusion (h.trans k) := by
  apply (discrete_arrow_eq_iff _ _).mpr
  intro n _
  exact Part.bind_some _ _

instance inclusion_mono {A B : Set ℕ} (h : A ⊆ B) : Mono (inclusion h) where
  right_cancellation := by
    intro R f g heq
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        apply (discrete_arrow_eq_iff f g).mpr
        have hv := (discrete_arrow_eq_iff
          (Representative.compose f (inclusionRepresentative h))
          (Representative.compose g (inclusionRepresentative h))).mp heq
        intro n hn
        simpa only [Representative.compose, inclusionRepresentative, Part.bind_some_right]
          using hv n hn

/-- The categorical subobject defined by an arbitrary support inclusion. -/
def supportSubobject {X : Set ℕ} (A : Set ℕ) (hA : A ⊆ X) : Subobject (discrete X) :=
  Subobject.mk (inclusion hA)

theorem supportSubobject_le_iff {X A B : Set ℕ} (hA : A ⊆ X) (hB : B ⊆ X) :
    supportSubobject A hA ≤ supportSubobject B hB ↔ A ⊆ B := by
  constructor
  · intro h
    let f := Subobject.ofMkLEMk (inclusion hA) (inclusion hB) h
    have hf : f ≫ inclusion hB = inclusion hA := Subobject.ofMkLEMk_comp h
    revert hf
    induction f using Quotient.inductionOn with | _ f =>
      intro hf
      have hv := (discrete_arrow_eq_iff
        (Representative.compose f (inclusionRepresentative hB)) (inclusionRepresentative hA)).mp hf
      intro n hn
      have he : f.val n = Part.some n := by
        simpa only [Representative.compose, inclusionRepresentative, Part.bind_some_right]
          using hv n ⟨hn, rfl⟩
      exact f.output_supported ⟨hn, rfl⟩ (Part.eq_some_iff.mp he) |>.1
  · intro h
    exact Subobject.mk_le_mk_of_comm (inclusion h) (inclusion_comp h hB)

theorem supportSubobject_eq_iff {X A B : Set ℕ} (hA : A ⊆ X) (hB : B ⊆ X) :
    supportSubobject A hA = supportSubobject B hB ↔ A = B := by
  constructor
  · intro h
    exact Set.Subset.antisymm ((supportSubobject_le_iff hA hB).mp h.le)
      ((supportSubobject_le_iff hB hA).mp h.ge)
  · rintro rfl; rfl


/-- The inverse-image support of an arbitrary subset under a supported representing function. -/
def inverseSupport {X Y : Set ℕ} (f : Representative (discrete X) (discrete Y))
    (A : Set ℕ) : Set ℕ := {n | n ∈ X ∧ ∃ m ∈ f.val n, m ∈ A}

def inverseRepresentative {X Y A : Set ℕ} (f : Representative (discrete X) (discrete Y)) :
    Representative (discrete (inverseSupport f A)) (discrete A) where
  val := f.val
  computable := f.computable
  total := by
    intro n hn
    obtain ⟨m, hm, _⟩ := hn.1.2
    exact hm.fst
  respects := by
    intro n m a b hn ha hb
    obtain ⟨hn, rfl⟩ := hn
    obtain ⟨k, hk, hkA⟩ := hn.2
    have hka := Part.mem_unique hk ha
    exact ⟨hka ▸ hkA, Part.mem_unique ha hb⟩

theorem inverse_square {X Y A : Set ℕ} (f : Representative (discrete X) (discrete Y))
    (hA : A ⊆ Y) :
    inclusion (show inverseSupport f A ⊆ X from fun _ h ↦ h.1) ≫ ofRepresentative f =
      ofRepresentative (inverseRepresentative f) ≫ inclusion hA := by
  apply (discrete_arrow_eq_iff _ _).mpr
  intro n _
  change (Part.some n).bind f.val = (f.val n).bind Part.some
  simp

theorem inverse_lift {X Y A : Set ℕ} (f : Representative (discrete X) (discrete Y))
    (hA : A ⊆ Y) {R : NumericalPER} (p : R ⟶ discrete X) (q : R ⟶ discrete A)
    (h : p ≫ ofRepresentative f = q ≫ inclusion hA) :
    ∃ l : R ⟶ discrete (inverseSupport f A),
      l ≫ inclusion (show inverseSupport f A ⊆ X from fun _ h ↦ h.1) = p ∧
      l ≫ ofRepresentative (inverseRepresentative f) = q := by
  induction p using Quotient.inductionOn with | _ p =>
    induction q using Quotient.inductionOn with | _ q =>
      have hv := (discrete_arrow_eq_iff
        (Representative.compose p f) (Representative.compose q (inclusionRepresentative hA))).mp h
      have hs : ∀ n ∈ R.support, ∀ a ∈ p.val n, a ∈ inverseSupport f A := by
        intro n hn a ha
        have hq := Part.get_mem (q.total n hn)
        have he : (p.val n).bind f.val = q.val n := by
          simpa only [Representative.compose, inclusionRepresentative, Part.bind_some_right]
            using hv n hn
        have hc : (q.val n).get (q.total n hn) ∈ (p.val n).bind f.val := he.symm ▸ hq
        obtain ⟨b, hb, hc⟩ := Part.mem_bind_iff.mp hc
        have hba := Part.mem_unique hb ha
        subst b
        exact ⟨(p.output_supported hn ha).1, _, hc, (q.output_supported hn hq).1⟩
      let l : Representative R (discrete (inverseSupport f A)) :=
        { val := p.val
          computable := p.computable
          total := p.total
          respects := fun h ha hb ↦ ⟨hs _ (supported_left h) _ ha, (p.respects h ha hb).2⟩ }
      have hl : ofRepresentative l ≫
          inclusion (show inverseSupport f A ⊆ X from fun _ h ↦ h.1) = ofRepresentative p := by
        apply (discrete_arrow_eq_iff _ _).mpr
        intro n _
        exact Part.bind_some_right (p.val n)
      refine ⟨ofRepresentative l, hl, ?_⟩
      apply (cancel_mono (inclusion hA)).mp
      rw [Category.assoc, ← inverse_square f hA, ← Category.assoc, hl]
      exact h

/-- The support inverse-image square has the full categorical pullback property. -/
theorem inverse_isPullback {X Y A : Set ℕ} (f : Representative (discrete X) (discrete Y))
    (hA : A ⊆ Y) :
    IsPullback
      (inclusion (show inverseSupport f A ⊆ X from fun _ h ↦ h.1))
      (ofRepresentative (inverseRepresentative f)) (ofRepresentative f) (inclusion hA) := by
  have hl := fun s : PullbackCone (ofRepresentative f) (inclusion hA) ↦
    inverse_lift f hA s.fst s.snd s.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk (inverse_square f hA)
    (fun s ↦ (hl s).choose)
    (fun s ↦ (hl s).choose_spec.1)
    (fun s ↦ (hl s).choose_spec.2)
    (fun s m hm _ ↦ (cancel_mono _).mp (hm.trans (hl s).choose_spec.1.symm)))

end NumericalPER
namespace Numerical

/-- The support inclusion associated with an numerical restriction idempotent. -/
def domainSubobject (X : Numerical) : Domain X ↪o Subobject (NumericalPER.discrete X.carrier) where
  toFun e := NumericalPER.supportSubobject e.support
    (fun _ hn ↦ e.hom.source (Part.get_mem hn))
  inj' _ _ h := Domain.support_injective X ((NumericalPER.supportSubobject_eq_iff _ _).mp h)
  map_rel_iff' := NumericalPER.supportSubobject_le_iff _ _

/-- Among support inclusions, the image consists exactly of c.e. supports. -/
theorem supportSubobject_in_range_iff {X : Numerical} (A : Set ℕ) (hA : A ⊆ X.carrier) :
    NumericalPER.supportSubobject A hA ∈ Set.range (domainSubobject X) ↔ REPred (· ∈ A) := by
  constructor
  · rintro ⟨e, he⟩
    have hs := (NumericalPER.supportSubobject_eq_iff _ _).mp he
    exact e.support_enumerable.of_eq (fun n ↦ by rw [hs])
  · intro he
    refine ⟨domainOfSupport ⟨A, he, hA⟩, ?_⟩
    apply (NumericalPER.supportSubobject_eq_iff _ _).mpr
    exact domainOfSupport_support _


/-- The support comparison identifies restriction inverse image with the PER pullback support. -/
theorem domainInverse_support_comparison {X Y : Total} (f : X ⟶ Y) (e : Domain Y.obj) :
    (domainInverse f.hom e).support =
      NumericalPER.inverseSupport (totalRepresentative f) e.support := by
  rw [domainInverse_support]
  ext n
  constructor
  · rintro ⟨m, hm, he⟩
    exact ⟨f.hom.source hm, m, hm, he⟩
  · rintro ⟨_, m, hm, he⟩
    exact ⟨m, hm, he⟩

end Numerical
end CategoricalEssentialIncompleteness
