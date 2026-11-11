/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalRecursionCategory
public import CategoricalEssentialIncompleteness.NumericalCategory

/-! # Comparison with ordinary partial recursive functions -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Encodable CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

open SyntacticModel PartialFunctions

theorem mem_standard_index (A B : STObjectCode) (q : ℕ)
    (x : interpretedType ℕ A) (y : interpretedType ℕ B) :
    y ∈ J.map (Q.map (arrowOfIndex 𝗣𝗔 A B q)) x ↔
      (codingEquiv 𝗣𝗔 ℕ B y).val ∈ Kleene.eval q (codingEquiv 𝗣𝗔 ℕ A x).val :=
  (mem_model_index 𝗣𝗔 ℕ A B q x y).trans (eventualGraph_adequate q _ _)

theorem all_arrows_have_programs {X Y : Rec} (f : X ⟶ Y) :
    ∃ q : ℕ, ∀ (x : interpretedType ℕ (objectCode X.base))
      (y : interpretedType ℕ (objectCode Y.base)),
      y ∈ f.val x ↔ (codingEquiv 𝗣𝗔 ℕ _ y).val ∈
        Kleene.eval q (codingEquiv 𝗣𝗔 ℕ _ x).val := by
  obtain ⟨g, rfl⟩ := exists_source f
  obtain ⟨q, hq⟩ := exists_arrowOfIndex 𝗣𝗔 _ _ g
  refine ⟨q, ?_⟩
  intro x y
  rw [← hq]
  exact mem_standard_index _ _ q x y

theorem represents_partrec (f : ℕ → Part ℕ) (hf : Partrec f) :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, standardFunctor.map g = f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨arrowOfIndex 𝗣𝗔 .omega .omega (encode c), ?_⟩
  apply PFun.ext
  intro x y
  rw [mem_model_index, eventualGraph_adequate]
  change y ∈ Nat.Partrec.Code.eval (Denumerable.ofNat _ (encode c)) x ↔ y ∈ f x
  rw [Denumerable.ofNat_encode, hc]

/-- Every ordinary unary partial recursive function is an arrow. -/
def omegaArrow (f : ℕ → Part ℕ) (hf : Partrec f) : U ⟶ U :=
  ⟨f, represents_partrec f hf⟩

@[simp] theorem omegaArrow_val (f : ℕ → Part ℕ) (hf : Partrec f) :
    (omegaArrow f hf).val = f := rfl

/-- Every unary arrow is an ordinary partial recursive function. -/
theorem omegaArrow_partrec (f : U ⟶ U) :
    @Partrec ℕ ℕ inferInstance inferInstance (fun n => f.val n) := by
  obtain ⟨q, hq⟩ := all_arrows_have_programs f
  have he : f.val = Kleene.eval q := by
    funext x
    apply Part.ext
    intro y
    exact hq x y
  rw [he]
  exact Partrec.nat_iff.mpr (Nat.Partrec.Code.exists_code.mpr
    ⟨Denumerable.ofNat Nat.Partrec.Code q, rfl⟩)

def supportIdem (A : Set ℕ) (hA : REPred (· ∈ A)) : Idem U :=
  ⟨omegaArrow (supportIdentity A) (supportIdentity_partrec A hA), by
    apply J.map_injective
    rw [J_rst]
    apply PFun.ext
    intro x y
    change y ∈ rst (C := Pfn) (X := PartialFun.of ℕ) (Y := PartialFun.of ℕ)
      (supportIdentity A) x ↔
      y ∈ supportIdentity A x
    rw [mem_rst]
    constructor
    · rintro ⟨⟨z, hz⟩, hy⟩
      exact (mem_supportIdentity A x y).mpr ⟨((mem_supportIdentity A x z).mp hz).1, hy⟩
    · intro hy
      exact ⟨⟨y, hy⟩, ((mem_supportIdentity A x y).mp hy).2⟩⟩

@[simp] theorem supportIdem_image (A : Set ℕ) (hA : REPred (· ∈ A)) :
    inclusionRangeFunctor.mapIdem (supportIdem A hA) = setIdem A := by
  apply Idem.ext
  apply PFun.ext
  intro x y
  exact (mem_supportIdentity A x y).trans (mem_identity A x y).symm

theorem supportIdem_le {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (h : A ⊆ B) : supportIdem A hA ≤ supportIdem B hB := by
  apply Idem.le_def.mpr
  apply J.map_injective
  rw [J.map_comp]
  apply PFun.ext
  intro x y
  change y ∈ ((supportIdentity A x).bind (supportIdentity B)) ↔ y ∈ supportIdentity A x
  rw [Part.mem_bind_iff]
  constructor
  · rintro ⟨z, hz, hy⟩
    obtain ⟨hx, he⟩ := (mem_supportIdentity A x z).mp hz
    subst z
    exact (mem_supportIdentity A x y).mpr ⟨hx, ((mem_supportIdentity B x y).mp hy).2⟩
  · intro hy
    obtain ⟨hx, he⟩ := (mem_supportIdentity A x y).mp hy
    exact ⟨x, (mem_supportIdentity A x x).mpr ⟨hx, rfl⟩,
      (mem_supportIdentity B x y).mpr ⟨h hx, he⟩⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
