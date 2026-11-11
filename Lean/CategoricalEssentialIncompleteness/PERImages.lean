/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERFiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

/-!
# Regular images in the numerical PER category

Enlarging a PER relation without changing its support gives a regular
epimorphism represented by the identity. Its coequalizer property uses
the PER of pairs of source representatives related in the enlarged relation.
For a representing function `f`, identifying source elements whose outputs are
related gives such a quotient. The function `f` induces a monomorphism from
this quotient to the target. Every arrow therefore factors as a regular
epimorphism followed by a monomorphism.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def quotientKernel (R S : NumericalPER) : NumericalPER :=
  onSubset (product R R) {n | S.rel (Nat.unpair n).1 (Nat.unpair n).2}

def quotientFstRepresentative (R S : NumericalPER) : Representative (quotientKernel R S) R where
  val n := Part.some (Nat.unpair n).1
  computable := (Computable.fst.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.1.1

def quotientSndRepresentative (R S : NumericalPER) : Representative (quotientKernel R S) R where
  val n := Part.some (Nat.unpair n).2
  computable := (Computable.snd.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.1.2

theorem quotient_condition {R S : NumericalPER}
    (hrel : ∀ n m, R.rel n m → S.rel n m) :
    ofRepresentative (quotientFstRepresentative R S) ≫
      ofRepresentative (relationRepresentative hrel) =
      ofRepresentative (quotientSndRepresentative R S) ≫
        ofRepresentative (relationRepresentative hrel) := by
  apply Quotient.sound
  intro n hn a ha b hb
  have ha' : a = (Nat.unpair n).1 := by
    simpa [Representative.compose, quotientFstRepresentative, relationRepresentative] using ha
  have hb' : b = (Nat.unpair n).2 := by
    simpa [Representative.compose, quotientSndRepresentative, relationRepresentative] using hb
  subst a; subst b
  exact hn.2.1

theorem quotient_desc_respects {R S T : NumericalPER}
    (hs : S.support ⊆ R.support) (h : Representative R T)
    (he : ofRepresentative (quotientFstRepresentative R S) ≫ ofRepresentative h =
      ofRepresentative (quotientSndRepresentative R S) ≫ ofRepresentative h)
    {n m a b : ℕ} (hnm : S.rel n m) (ha : a ∈ h.val n) (hb : b ∈ h.val m) :
    T.rel a b := by
  have hp : Nat.pair n m ∈ (quotientKernel R S).support := by
    change (R.rel (Nat.unpair (Nat.pair n m)).1 (Nat.unpair (Nat.pair n m)).1 ∧
      R.rel (Nat.unpair (Nat.pair n m)).2 (Nat.unpair (Nat.pair n m)).2) ∧
      S.rel (Nat.unpair (Nat.pair n m)).1 (Nat.unpair (Nat.pair n m)).2 ∧
      S.rel (Nat.unpair (Nat.pair n m)).1 (Nat.unpair (Nat.pair n m)).2
    simpa only [Nat.unpair_pair, support, Set.mem_ofPred_eq] using
      And.intro (And.intro (hs (supported_left hnm)) (hs (supported_right hnm)))
        (And.intro hnm hnm)
  apply (ofRepresentative_eq_iff _ _).mp he (Nat.pair n m) hp a _ b _
  · simpa [Representative.compose, quotientFstRepresentative] using ha
  · simpa [Representative.compose, quotientSndRepresentative] using hb

def quotientDescRepresentative {R S T : NumericalPER}
    (hs : S.support ⊆ R.support) (h : Representative R T)
    (he : ofRepresentative (quotientFstRepresentative R S) ≫ ofRepresentative h =
      ofRepresentative (quotientSndRepresentative R S) ≫ ofRepresentative h) :
    Representative S T where
  val := h.val
  computable := h.computable
  total := fun n hn ↦ h.total n (hs hn)
  respects := quotient_desc_respects hs h he

theorem quotient_cancel {R S T : NumericalPER}
    (hrel : ∀ n m, R.rel n m → S.rel n m) (hs : S.support ⊆ R.support)
    {f g : S ⟶ T} (he : ofRepresentative (relationRepresentative hrel) ≫ f =
      ofRepresentative (relationRepresentative hrel) ≫ g) : f = g := by
  revert he
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      intro he
      apply Quotient.sound
      intro n hn a ha b hb
      exact (ofRepresentative_eq_iff _ _).mp he n (hs hn)
        a (Part.mem_bind (Part.mem_some _) ha) b (Part.mem_bind (Part.mem_some _) hb)

theorem quotient_desc_existsUnique {R S T : NumericalPER}
    (hrel : ∀ n m, R.rel n m → S.rel n m) (hs : S.support ⊆ R.support)
    (h : R ⟶ T) (he : ofRepresentative (quotientFstRepresentative R S) ≫ h =
      ofRepresentative (quotientSndRepresentative R S) ≫ h) :
    ∃! l : S ⟶ T, ofRepresentative (relationRepresentative hrel) ≫ l = h := by
  revert he
  induction h using Quotient.inductionOn with | _ h =>
    intro he
    have hf : ofRepresentative (relationRepresentative hrel) ≫
        ofRepresentative (quotientDescRepresentative hs h he) = ofRepresentative h := by
      apply Quotient.sound
      exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some n h.val)
    exact ⟨ofRepresentative (quotientDescRepresentative hs h he), hf,
      fun _ hl ↦ quotient_cancel hrel hs (hl.trans hf.symm)⟩

/-- A relation inclusion with equal supports is a regular epimorphism. -/
def relationRegularEpi {R S : NumericalPER}
    (hrel : ∀ n m, R.rel n m → S.rel n m) (hs : S.support ⊆ R.support) :
    RegularEpi (ofRepresentative (relationRepresentative hrel)) where
  W := quotientKernel R S
  left := ofRepresentative (quotientFstRepresentative R S)
  right := ofRepresentative (quotientSndRepresentative R S)
  w := quotient_condition hrel
  isColimit := Cofork.IsColimit.ofExistsUnique
    (fun s ↦ quotient_desc_existsUnique hrel hs s.π s.condition)

/-- Source representatives, identified precisely when their outputs are related. -/
def imagePER {R S : NumericalPER} (f : Representative R S) : NumericalPER where
  rel n m := n ∈ R.support ∧ m ∈ R.support ∧
    ∀ a ∈ f.val n, ∀ b ∈ f.val m, S.rel a b
  symm := fun h ↦ ⟨h.2.1, h.1, fun _ ha _ hb ↦ S.symm (h.2.2 _ hb _ ha)⟩
  trans := by
    intro n m k h h'
    refine ⟨h.1, h'.2.1, ?_⟩
    intro a ha b hb
    have hm := Part.get_mem (f.total m h.2.1)
    exact S.trans (h.2.2 a ha _ hm) (h'.2.2 _ hm b hb)

theorem imagePER_rel {R S : NumericalPER} (f : Representative R S) (n m : ℕ)
    (h : R.rel n m) : (imagePER f).rel n m :=
  ⟨supported_left h, supported_right h, fun _ ha _ hb ↦ f.respects h ha hb⟩

@[simp] theorem imagePER_support {R S : NumericalPER} (f : Representative R S) :
    (imagePER f).support = R.support := by
  ext n
  exact ⟨fun h ↦ h.1, fun h ↦ imagePER_rel f n n h⟩

def imageQuotient {R S : NumericalPER} (f : Representative R S) : R ⟶ imagePER f :=
  ofRepresentative (relationRepresentative (imagePER_rel f))

instance imageQuotient_regularEpi {R S : NumericalPER} (f : Representative R S) :
    IsRegularEpi (imageQuotient f) :=
  isRegularEpi_of_regularEpi (relationRegularEpi (imagePER_rel f) (fun _ h ↦ h.1))

def imageRepresentative {R S : NumericalPER} (f : Representative R S) :
    Representative (imagePER f) S where
  val := f.val
  computable := f.computable
  total := fun n hn ↦ f.total n hn.1
  respects := fun h ha hb ↦ h.2.2 _ ha _ hb

def imageInclusion {R S : NumericalPER} (f : Representative R S) : imagePER f ⟶ S :=
  ofRepresentative (imageRepresentative f)

instance imageInclusion_mono {R S : NumericalPER} (f : Representative R S) :
    Mono (imageInclusion f) where
  right_cancellation h k he := by
    revert he
    induction h using Quotient.inductionOn with | _ h =>
      induction k using Quotient.inductionOn with | _ k =>
        intro he
        apply Quotient.sound
        intro n hn a ha b hb
        refine ⟨(h.output_supported hn ha).1, (k.output_supported hn hb).1, ?_⟩
        intro x hx y hy
        exact (ofRepresentative_eq_iff _ _).mp he n hn x (Part.mem_bind ha hx)
          y (Part.mem_bind hb hy)

@[simp, reassoc] theorem image_factorization {R S : NumericalPER} (f : Representative R S) :
    imageQuotient f ≫ imageInclusion f = ofRepresentative f := by
  apply Quotient.sound
  exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some n f.val)

def imageFactorisation {R S : NumericalPER} (f : Representative R S) :
    StrongEpiMonoFactorisation (ofRepresentative f) where
  I := imagePER f
  e := imageQuotient f
  m := imageInclusion f
  fac := image_factorization f

instance perHasStrongEpiMonoFactorisations : HasStrongEpiMonoFactorisations NumericalPER where
  has_fac f := by
    induction f using Quotient.inductionOn with | _ f =>
      exact ⟨imageFactorisation f⟩

/-- Every kernel pair has a coequalizer, given by the regular image quotient. -/
theorem hasCoequalizer_of_isKernelPair {R S T : NumericalPER} {f : R ⟶ S}
    {p q : T ⟶ R} (h : IsKernelPair f p q) : HasCoequalizer p q := by
  revert h
  induction f using Quotient.inductionOn with | _ f =>
    intro h
    change IsKernelPair (ofRepresentative f) p q at h
    rw [← image_factorization f] at h
    have hk : IsKernelPair (imageQuotient f) p q :=
      IsKernelPair.cancel_right_of_mono h
    exact ⟨⟨_, hk.toCoequalizer'⟩⟩

end NumericalPER
end CategoricalEssentialIncompleteness
