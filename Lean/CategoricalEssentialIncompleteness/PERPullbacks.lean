/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.PERFiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Pullbacks of numerical PERs

The pullback restricts the product PER to pairs whose images are related in
the common target. Recursive coordinate projections and pairing give its
universal property. No enumerability condition is required on this support.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def pullbackAgreement {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) : Set ℕ :=
  {n | ∃ a ∈ f.val (Nat.unpair n).1, ∃ b ∈ g.val (Nat.unpair n).2, T.rel a b}

def pullbackPER {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) : NumericalPER :=
  onSubset (product R S) (pullbackAgreement f g)

theorem pullbackPER_support {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (n : ℕ) :
    n ∈ (pullbackPER f g).support ↔
      (Nat.unpair n).1 ∈ R.support ∧ (Nat.unpair n).2 ∈ S.support ∧
        n ∈ pullbackAgreement f g := by
  change ((_ ∧ _) ∧ _ ∧ _) ↔ _
  tauto

def pullbackFstRepresentative {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) : Representative (pullbackPER f g) R where
  val n := Part.some (Nat.unpair n).1
  computable := (Computable.fst.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.1.1

def pullbackSndRepresentative {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) : Representative (pullbackPER f g) S where
  val n := Part.some (Nat.unpair n).2
  computable := (Computable.snd.comp Computable.unpair).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := by
    intro n m a b h ha hb
    obtain rfl := Part.mem_some_iff.mp ha
    obtain rfl := Part.mem_some_iff.mp hb
    exact h.1.2

def pullbackFst {R S T : NumericalPER} (f : Representative R T) (g : Representative S T) :
    pullbackPER f g ⟶ R := ofRepresentative (pullbackFstRepresentative f g)

def pullbackSnd {R S T : NumericalPER} (f : Representative R T) (g : Representative S T) :
    pullbackPER f g ⟶ S := ofRepresentative (pullbackSndRepresentative f g)

@[simp] theorem pullbackInclusion_fst {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) :
    subsetInclusion (product R S) (pullbackAgreement f g) ≫ fst R S = pullbackFst f g := by
  apply Quotient.sound
  exact Representative.equiv_of_val_eq _ _
    (funext fun n ↦ Part.bind_some n (fun m ↦ Part.some (Nat.unpair m).1))

@[simp] theorem pullbackInclusion_snd {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) :
    subsetInclusion (product R S) (pullbackAgreement f g) ≫ snd R S = pullbackSnd f g := by
  apply Quotient.sound
  exact Representative.equiv_of_val_eq _ _
    (funext fun n ↦ Part.bind_some n (fun m ↦ Part.some (Nat.unpair m).2))

theorem pullback_condition {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) :
    pullbackFst f g ≫ ofRepresentative f = pullbackSnd f g ≫ ofRepresentative g := by
  apply Quotient.sound
  intro n hn a ha b hb
  change a ∈ (Part.some (Nat.unpair n).1).bind f.val at ha
  change b ∈ (Part.some (Nat.unpair n).2).bind g.val at hb
  rw [Part.bind_some] at ha hb
  obtain ⟨x, hx, y, hy, hxy⟩ := hn.2.1
  exact Part.mem_unique ha hx ▸ Part.mem_unique hb hy ▸ hxy

theorem pullback_pair_supported {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T)
    (h : Representative W R) (k : Representative W S)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative k ≫ ofRepresentative g)
    {n p : ℕ} (hn : n ∈ W.support) (hp : p ∈ (pairRepresentative h k).val n) :
    p ∈ pullbackAgreement f g := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp hp
  have hf := Part.get_mem (f.total x (h.output_supported hn hx))
  have hg := Part.get_mem (g.total y (k.output_supported hn hy))
  refine ⟨_, ?_, _, ?_, (ofRepresentative_eq_iff _ _).mp he n hn
    _ (Part.mem_bind hx hf) _ (Part.mem_bind hy hg)⟩
  · simpa only [Nat.unpair_pair] using hf
  · simpa only [Nat.unpair_pair] using hg

def pullbackLiftRepresentative {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T)
    (h : Representative W R) (k : Representative W S)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative k ≫ ofRepresentative g) :
    Representative W (pullbackPER f g) where
  val := (pairRepresentative h k).val
  computable := (pairRepresentative h k).computable
  total := (pairRepresentative h k).total
  respects := fun hnm ha hb ↦ ⟨(pairRepresentative h k).respects hnm ha hb,
    pullback_pair_supported f g h k he (supported_left hnm) ha,
    pullback_pair_supported f g h k he (supported_right hnm) hb⟩

@[simp] theorem pullbackLiftRepresentative_fst {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T)
    (h : Representative W R) (k : Representative W S)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative k ≫ ofRepresentative g) :
    ofRepresentative (pullbackLiftRepresentative f g h k he) ≫ pullbackFst f g =
      ofRepresentative h := by
  exact pair_fst (ofRepresentative h) (ofRepresentative k)

@[simp] theorem pullbackLiftRepresentative_snd {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T)
    (h : Representative W R) (k : Representative W S)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative k ≫ ofRepresentative g) :
    ofRepresentative (pullbackLiftRepresentative f g h k he) ≫ pullbackSnd f g =
      ofRepresentative k := by
  exact pair_snd (ofRepresentative h) (ofRepresentative k)

theorem pullback_exists {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (h : W ⟶ R) (k : W ⟶ S)
    (he : h ≫ ofRepresentative f = k ≫ ofRepresentative g) :
    ∃ l : W ⟶ pullbackPER f g, l ≫ pullbackFst f g = h ∧ l ≫ pullbackSnd f g = k := by
  revert he
  induction h using Quotient.inductionOn with | _ h =>
    induction k using Quotient.inductionOn with | _ k =>
      intro he
      exact ⟨ofRepresentative (pullbackLiftRepresentative f g h k he),
        pullbackLiftRepresentative_fst f g h k he, pullbackLiftRepresentative_snd f g h k he⟩

theorem pullback_hom_ext {W R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) {h k : W ⟶ pullbackPER f g}
    (hf : h ≫ pullbackFst f g = k ≫ pullbackFst f g)
    (hg : h ≫ pullbackSnd f g = k ≫ pullbackSnd f g) : h = k := by
  revert hf hg
  induction h using Quotient.inductionOn with | _ h =>
    induction k using Quotient.inductionOn with | _ k =>
      intro hf hg
      apply Quotient.sound
      intro n hn a ha b hb
      refine ⟨⟨?_, ?_⟩, (h.output_supported hn ha).2.1, (k.output_supported hn hb).2.1⟩
      · exact (ofRepresentative_eq_iff _ _).mp hf n hn
          _ (Part.mem_bind ha (Part.mem_some _)) _ (Part.mem_bind hb (Part.mem_some _))
      · exact (ofRepresentative_eq_iff _ _).mp hg n hn
          _ (Part.mem_bind ha (Part.mem_some _)) _ (Part.mem_bind hb (Part.mem_some _))

def pullbackIsLimit {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) :
    IsLimit (PullbackCone.mk (pullbackFst f g) (pullbackSnd f g) (pullback_condition f g)) :=
  PullbackCone.isLimitAux' _ (fun s ↦ by
    let h := pullback_exists f g s.fst s.snd s.condition
    exact ⟨Classical.choose h, (Classical.choose_spec h).1, (Classical.choose_spec h).2,
      fun hf hg ↦ pullback_hom_ext f g
        (hf.trans (Classical.choose_spec h).1.symm)
        (hg.trans (Classical.choose_spec h).2.symm)⟩)

theorem pullback_isPullback {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) :
    IsPullback (pullbackFst f g) (pullbackSnd f g) (ofRepresentative f) (ofRepresentative g) :=
  IsPullback.of_isLimit (pullbackIsLimit f g)

end NumericalPER
end CategoricalEssentialIncompleteness
