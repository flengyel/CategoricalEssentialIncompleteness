/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.PartialFunctions

/-! # Set and total-function laws before arithmetic specialization -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSetModelLaws

def someMap {A B : Pfn} (f : A → B) : A ⟶ B :=
  fun x => Part.some (f x)

theorem someMap_total {A B : Pfn} (f : A → B) : isTotal (someMap f) := by
  apply PFun.ext
  intro x y
  simp [someMap]

theorem someMap_comp {A B C : Pfn} (f : A → B) (g : B → C) :
    someMap f ≫ someMap g = someMap (g ∘ f) := by
  apply PFun.ext
  intro a c
  simp [someMap,mem_comp]

theorem range_some_support {A B : Pfn} (f : A → B) (b : B) :
    b ∈ support (Ranges.range (someMap f)) ↔ ∃ a, f a = b := by
  rw [mem_support]
  simp only [mem_range,someMap,Part.mem_some_iff,exists_eq_right]
  exact exists_congr fun _ => eq_comm

theorem predicate_support {A : Pfn} (R : A → Prop) (x : A) :
    x ∈ support (setIdem {a : A | R a}) ↔ R x := by
  rw [support_setIdem]
  rfl

theorem pull_some_setIdem {A B : Pfn} (f : A → B) (R : B → Prop) :
    Idem.pull (someMap f) (setIdem {b : B | R b}) = setIdem {a : A | R (f a)} := by
  apply support_injective
  ext a
  simp [support_pull,someMap]

theorem setIdem_consistent {A : Pfn} (R : A → Prop) (f : A → A)
    (h : ∀ a, ¬(R a ∧ R (f a))) :
    setIdem {a : A | R a} ⊓ Idem.pull (someMap f) (setIdem {a : A | R a}) = ⊥ := by
  rw [pull_some_setIdem]
  apply support_injective
  ext a
  simp only [support_inf,support_setIdem,support_bot,Set.mem_inter_iff,
    Set.mem_ofPred_eq,Set.mem_empty_iff_false]
  exact iff_false_intro (h a)

theorem idem_eq_setIdem {A : Pfn} (t : Idem (A)) (R : A → Prop)
    (ht : ∀ a, a ∈ support t ↔ R a) : t = setIdem {a : A | R a} := by
  apply support_injective
  ext a
  simpa only [support_setIdem,Set.mem_ofPred_eq] using ht a

theorem pull_some_of_support {A B : Pfn} (f : A → B) (t : Idem (B))
    (R : B → Prop) (ht : ∀ b, b ∈ support t ↔ R b) :
    Idem.pull (someMap f) t = setIdem {a : A | R (f a)} := by
  rw [idem_eq_setIdem t R ht]
  exact pull_some_setIdem f R

theorem pull_twice_some_of_support {A B C : Pfn} (f : A → B) (g : B → C)
    (t : Idem (C)) (R : C → Prop) (ht : ∀ c, c ∈ support t ↔ R c) :
    Idem.pull (someMap f) (Idem.pull (someMap g) t) =
      setIdem {a : A | R (g (f a))} := by
  rw [← Idem.pull_comp,someMap_comp]
  exact pull_some_of_support (g ∘ f) t R ht

theorem consistent_of_support {A : Pfn} (t : Idem (A))
    (R : A → Prop) (f : A → A) (ht : ∀ a, a ∈ support t ↔ R a)
    (h : ∀ a, ¬(R a ∧ R (f a))) : t ⊓ Idem.pull (someMap f) t = ⊥ := by
  rw [idem_eq_setIdem t R ht]
  exact setIdem_consistent R f h

theorem setIdem_congr {A : Pfn} {R S : A → Prop} (h : ∀ a, R a ↔ S a) :
    setIdem {a : A | R a} = setIdem {a : A | S a} :=
  congrArg (fun X : Set A => setIdem X) (Set.ext h)

theorem setIdem_le {A : Pfn} {R S : A → Prop} (h : ∀ a, R a → S a) :
    setIdem {a : A | R a} ≤ setIdem {a : A | S a} := by
  apply (le_iff_support _ _).mpr
  intro a ha
  exact (predicate_support S a).mpr (h a ((predicate_support R a).mp ha))

theorem total_has_value {A B : Pfn} (f : A ⟶ B) (hf : isTotal f) (a : A) :
    ∃ b : B, b ∈ f a := by
  have h : a ∈ rst f a := by
    change rst f = 𝟙 A at hf
    rw [hf]
    exact Part.mem_some_iff.mpr rfl
  exact ((mem_rst f a a).mp h).1

noncomputable def totalValue {A B : Pfn} (f : A ⟶ B) (hf : isTotal f) (a : A) : B :=
  Classical.choose (total_has_value f hf a)

theorem totalValue_mem {A B : Pfn} (f : A ⟶ B) (hf : isTotal f) (a : A) :
    totalValue f hf a ∈ f a := Classical.choose_spec (total_has_value f hf a)

theorem pull_zero_not_mem {A B : Pfn} (f : A ⟶ B) (R : B → Prop)
    (h : Idem.pull f (setIdem {b : B | R b}) = ⊥) (a : A) (b : B)
    (hb : b ∈ f a) : ¬ R b := by
  intro hR
  have ha : a ∈ support (Idem.pull f (setIdem {b : B | R b})) := by
    rw [support_pull]
    exact ⟨b,hb,(predicate_support R b).mpr hR⟩
  rw [h,support_bot] at ha
  exact ha

end CategoricalEssentialIncompleteness.V46.ArithmeticSetModelLaws
