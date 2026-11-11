/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Finite limits of numerical PERs

The terminal PER has one equivalence class. Equalizers restrict the source PER
to inputs where the two representing functions return related values. The
category contains arbitrary PERs, so this support need not be recursively
enumerable. A function representing an equalizing arrow takes its supported
inputs into this support and represents the unique factorization.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

def unitPER : NumericalPER where
  rel _ _ := True
  symm := fun _ ↦ trivial
  trans := fun _ _ ↦ trivial

def unitRepresentative (R : NumericalPER) : Representative R unitPER where
  val _ := Part.some 0
  computable := (Computable.const 0).partrec
  total := fun _ _ ↦ Part.some_dom _
  respects := fun _ _ _ ↦ trivial

def unitIsTerminal : IsTerminal unitPER :=
  IsTerminal.ofUniqueHom (fun R ↦ ofRepresentative (unitRepresentative R)) (by
    intro R f
    induction f using Quotient.inductionOn with | _ f =>
      apply Quotient.sound
      exact fun _ _ _ _ _ _ ↦ trivial)

instance perHasTerminal : HasTerminal NumericalPER :=
  unitIsTerminal.hasTerminal

/-- Restrict a PER to an arbitrary set of representatives. -/
def onSubset (R : NumericalPER) (A : Set ℕ) : NumericalPER where
  rel n m := R.rel n m ∧ n ∈ A ∧ m ∈ A
  symm := fun h ↦ ⟨R.symm h.1, h.2.2, h.2.1⟩
  trans := fun h k ↦ ⟨R.trans h.1 k.1, h.2.1, k.2.2⟩

def subsetInclusion (R : NumericalPER) (A : Set ℕ) : onSubset R A ⟶ R :=
  ofRepresentative (relationRepresentative (fun _ _ h ↦ h.1))

instance subsetInclusion_mono (R : NumericalPER) (A : Set ℕ) :
    Mono (subsetInclusion R A) where
  right_cancellation f g h := by
    revert h
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        intro h
        have he := (ofRepresentative_eq_iff _ _).mp h
        apply Quotient.sound
        intro n hn a ha b hb
        exact ⟨he n hn a (Part.mem_bind ha (Part.mem_some _))
            b (Part.mem_bind hb (Part.mem_some _)),
          (f.output_supported hn ha).2.1, (g.output_supported hn hb).2.1⟩

/-- Inputs on which two representing functions have related outputs. -/
def agreement {R S : NumericalPER} (f g : Representative R S) : Set ℕ :=
  {n | ∃ a ∈ f.val n, ∃ b ∈ g.val n, S.rel a b}

def equalizerPER {R S : NumericalPER} (f g : Representative R S) : NumericalPER :=
  onSubset R (agreement f g)

def equalizerInclusion {R S : NumericalPER} (f g : Representative R S) :
    equalizerPER f g ⟶ R := subsetInclusion R (agreement f g)

theorem equalizer_condition {R S : NumericalPER} (f g : Representative R S) :
    equalizerInclusion f g ≫ ofRepresentative f = equalizerInclusion f g ≫ ofRepresentative g := by
  apply Quotient.sound
  intro n hn a ha b hb
  change a ∈ (Part.some n).bind f.val at ha
  change b ∈ (Part.some n).bind g.val at hb
  rw [Part.bind_some] at ha hb
  obtain ⟨x, hx, y, hy, hxy⟩ := hn.2.1
  exact Part.mem_unique ha hx ▸ Part.mem_unique hb hy ▸ hxy

theorem equalizing_output {T R S : NumericalPER} (f g : Representative R S) (h : Representative T R)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative h ≫ ofRepresentative g)
    {n a : ℕ} (hn : n ∈ T.support) (ha : a ∈ h.val n) : a ∈ agreement f g := by
  have haR := h.output_supported hn ha
  have hf := Part.get_mem (f.total a haR)
  have hg := Part.get_mem (g.total a haR)
  exact ⟨_, hf, _, hg, (ofRepresentative_eq_iff _ _).mp he n hn
    _ (Part.mem_bind ha hf) _ (Part.mem_bind ha hg)⟩

def equalizerLiftRepresentative {T R S : NumericalPER}
    (f g : Representative R S) (h : Representative T R)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative h ≫ ofRepresentative g) :
    Representative T (equalizerPER f g) where
  val := h.val
  computable := h.computable
  total := h.total
  respects := fun hnm ha hb ↦ ⟨h.respects hnm ha hb,
    equalizing_output f g h he (supported_left hnm) ha,
    equalizing_output f g h he (supported_right hnm) hb⟩

@[simp] theorem equalizerLiftRepresentative_fac {T R S : NumericalPER}
    (f g : Representative R S) (h : Representative T R)
    (he : ofRepresentative h ≫ ofRepresentative f = ofRepresentative h ≫ ofRepresentative g) :
    ofRepresentative (equalizerLiftRepresentative f g h he) ≫ equalizerInclusion f g =
      ofRepresentative h := by
  apply Quotient.sound
  exact Representative.equiv_of_val_eq _ _ (funext fun n ↦ Part.bind_some_right (h.val n))

theorem equalizer_existsUnique {T R S : NumericalPER} (f g : Representative R S) (h : T ⟶ R)
    (he : h ≫ ofRepresentative f = h ≫ ofRepresentative g) :
    ∃! l : T ⟶ equalizerPER f g, l ≫ equalizerInclusion f g = h := by
  revert he
  induction h using Quotient.inductionOn with | _ h =>
    intro he
    refine ⟨ofRepresentative (equalizerLiftRepresentative f g h he),
      equalizerLiftRepresentative_fac f g h he, ?_⟩
    intro l hl
    exact (cancel_mono (subsetInclusion R (agreement f g))).mp
      (hl.trans (equalizerLiftRepresentative_fac f g h he).symm)

def equalizerIsLimit {R S : NumericalPER} (f g : Representative R S) :
    IsLimit (Fork.ofι (equalizerInclusion f g) (equalizer_condition f g)) :=
  Fork.IsLimit.ofExistsUnique (fun s ↦ equalizer_existsUnique f g s.ι s.condition)

instance equalizerHasLimit {R S : NumericalPER} (f g : R ⟶ S) :
    HasLimit (parallelPair f g) := by
  induction f using Quotient.inductionOn with | _ f =>
    induction g using Quotient.inductionOn with | _ g =>
      exact ⟨⟨_, equalizerIsLimit f g⟩⟩

instance perHasEqualizers : HasEqualizers NumericalPER :=
  hasEqualizers_of_hasLimit_parallelPair NumericalPER

instance perHasFiniteProducts : HasFiniteProducts NumericalPER :=
  hasFiniteProducts_of_has_binary_and_terminal

instance perHasFiniteLimits : HasFiniteLimits NumericalPER :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

end NumericalPER
end CategoricalEssentialIncompleteness
