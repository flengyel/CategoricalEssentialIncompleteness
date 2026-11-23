/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Data.Finset.Basic

/-! # Hierarchies of relation symbols and formulas without terms

In Voutsadakis, *Categorical abstract algebraic logic: categorical algebraization
of first-order logic without terms*, Definition 1 indexes a hierarchy by finite
sets of variable indices. Its components intersect in the component at the
intersection. Definitions 2 and 3 give formulas in each context and substitution
for a symbol, including substitution under an existential quantifier.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoricalEssentialIncompleteness.V46.Voutsadakis

/-- The carrier is the union of the sets in the hierarchy. -/
structure HSet where
  carrier : Type u
  layer : Finset ℕ → Set carrier
  mem_inter : ∀ N M x, x ∈ layer (N ∩ M) ↔ x ∈ layer N ∧ x ∈ layer M
  covered : ∀ x, ∃ N, x ∈ layer N

theorem HSet.layer_mono (A : HSet) {N M : Finset ℕ} (h : N ⊆ M) : A.layer N ⊆ A.layer M := by
  intro x hx
  apply ((A.mem_inter N M x).mp ?_).2
  rwa [Finset.inter_eq_left.mpr h]

structure HSet.Hom (A B : HSet.{u}) where
  map : A.carrier → B.carrier
  map_mem : ∀ N x, x ∈ A.layer N → map x ∈ B.layer N

@[ext] theorem HSet.Hom.ext {A B : HSet.{u}} {f g : A.Hom B}
    (h : ∀ x, f.map x = g.map x) : f = g := by
  cases f; cases g
  congr 1
  exact funext h

instance : Category HSet.{u} where
  Hom := HSet.Hom
  id _ := ⟨id, fun _ _ h ↦ h⟩
  comp f g := ⟨g.map ∘ f.map, fun N x h ↦ g.map_mem N _ (f.map_mem N x h)⟩

/-- The component maps commute with every inclusion of finite contexts. -/
structure HSet.Components (A B : HSet.{u}) where
  app : ∀ N, A.layer N → B.layer N
  naturality : ∀ {N M} (h : N ⊆ M) (x : A.carrier) (hx : x ∈ A.layer N),
    (app M ⟨x, A.layer_mono h hx⟩).val = (app N ⟨x, hx⟩).val

@[ext] theorem HSet.Components.ext {A B : HSet.{u}} {f g : A.Components B}
    (h : ∀ N x, (f.app N x).val = (g.app N x).val) : f = g := by
  cases f with
  | mk a ha =>
    cases g with
    | mk b hb =>
      have eq : a = b := by funext N x; exact Subtype.ext (h N x)
      cases eq
      rfl

noncomputable def HSet.Components.value {A B : HSet.{u}} (f : A.Components B)
    (x : A.carrier) : B.carrier :=
  (f.app (A.covered x).choose ⟨x, (A.covered x).choose_spec⟩).val

theorem HSet.Components.value_eq {A B : HSet.{u}} (f : A.Components B)
    (N : Finset ℕ) (x : A.carrier) (hx : x ∈ A.layer N) :
    f.value x = (f.app N ⟨x, hx⟩).val := by
  let M := (A.covered x).choose
  exact (f.naturality (M := M ∪ N) Finset.subset_union_left x (A.covered x).choose_spec).symm.trans
    (f.naturality Finset.subset_union_right x hx)

/-- A map preserving all components is the same as the coherent family
of maps on components in Definition 1. -/
noncomputable def HSet.homEquivComponents (A B : HSet.{u}) : (A ⟶ B) ≃ A.Components B where
  toFun f := ⟨fun N x ↦ ⟨f.map x.val, f.map_mem N x.val x.property⟩, fun _ _ _ ↦ rfl⟩
  invFun f := ⟨HSet.Components.value f, fun N x hx ↦
    (HSet.Components.value_eq f N x hx).symm ▸ (f.app N ⟨x, hx⟩).property⟩
  left_inv _ := HSet.Hom.ext fun _ ↦ rfl
  right_inv f := HSet.Components.ext fun N x ↦ f.value_eq N x.val x.property

/-- Formulas of relational logic without terms (Definition 2). -/
inductive Formula (X : Type u) : Type u where
  | symbol (x : X)
  | equal (i j : ℕ)
  | neg (p : Formula X)
  | conj (p q : Formula X)
  | ex (k : ℕ) (p : Formula X)

namespace Formula

def Supported (A : HSet.{u}) : Formula A.carrier → Finset ℕ → Prop
  | .symbol x, N => x ∈ A.layer N
  | .equal i j, N => i ∈ N ∧ j ∈ N
  | .neg p, N => Supported A p N
  | .conj p q, N => Supported A p N ∧ Supported A q N
  | .ex k p, N => Supported A p (insert k N)

theorem supported_inter (A : HSet.{u}) (p : Formula A.carrier) (N M : Finset ℕ) :
    Supported A p (N ∩ M) ↔ Supported A p N ∧ Supported A p M := by
  induction p generalizing N M with
  | symbol x => exact A.mem_inter N M x
  | equal i j => simp only [Supported, Finset.mem_inter]; tauto
  | neg p ih => exact ih N M
  | conj p q ihp ihq => simp only [Supported, ihp, ihq]; tauto
  | ex k p ih =>
    simpa only [Supported, Finset.insert_inter_distrib] using ih (insert k N) (insert k M)

theorem supported_mono (A : HSet.{u}) (p : Formula A.carrier) {N M : Finset ℕ} (h : N ⊆ M)
    (hp : Supported A p N) : Supported A p M := by
  apply ((supported_inter A p N M).mp ?_).2
  rwa [Finset.inter_eq_left.mpr h]

theorem supported_somewhere (A : HSet.{u}) (p : Formula A.carrier) : ∃ N, Supported A p N := by
  induction p with
  | symbol x => exact A.covered x
  | equal i j => exact ⟨{i, j}, by simp [Supported]⟩
  | neg p ih => exact ih
  | conj p q ihp ihq =>
    obtain ⟨N, hp⟩ := ihp
    obtain ⟨M, hq⟩ := ihq
    exact ⟨N ∪ M, supported_mono A p Finset.subset_union_left hp,
      supported_mono A q Finset.subset_union_right hq⟩
  | ex k p ih =>
    obtain ⟨N, hp⟩ := ih
    exact ⟨N, supported_mono A p (Finset.subset_insert k N) hp⟩

def hierarchy (A : HSet.{u}) : HSet.{u} where
  carrier := Formula A.carrier
  layer N := {p | Supported A p N}
  mem_inter N M p := supported_inter A p N M
  covered := supported_somewhere A

def substitute {X Y : Type u} (f : X → Formula Y) : Formula X → Formula Y
  | .symbol x => f x
  | .equal i j => .equal i j
  | .neg p => .neg (substitute f p)
  | .conj p q => .conj (substitute f p) (substitute f q)
  | .ex k p => .ex k (substitute f p)

theorem substitute_supported {A B : HSet.{u}} (f : A ⟶ hierarchy B)
    (p : Formula A.carrier) (N : Finset ℕ) :
    Supported A p N → Supported B (substitute f.map p) N := by
  induction p generalizing N with
  | symbol x => exact f.map_mem N x
  | equal i j => exact id
  | neg p ih => exact ih N
  | conj p q ihp ihq => exact fun h ↦ ⟨ihp N h.1, ihq N h.2⟩
  | ex k p ih => exact ih (insert k N)

theorem substitute_symbol {X : Type u} (p : Formula X) : substitute symbol p = p := by
  induction p <;> simp [substitute, *]

theorem substitute_substitute {X Y Z : Type u} (f : X → Formula Y) (g : Y → Formula Z)
    (p : Formula X) : substitute g (substitute f p) = substitute (substitute g ∘ f) p := by
  induction p <;> simp [substitute, *]

end Formula

end CategoricalEssentialIncompleteness.V46.Voutsadakis
