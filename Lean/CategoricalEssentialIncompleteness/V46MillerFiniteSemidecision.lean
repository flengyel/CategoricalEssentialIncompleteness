/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Foundation.Vorspiel.Computability

/-! # Finite conjunction and functional realization of enumerable relations

Finite conjunction uses a single fuel bound for the ordinary evaluator.
Functionality permits an ordinary parallel search over a graph's output
coordinate; no totality of that graph is assumed.
-/

@[expose] public section
noncomputable section

namespace CategoricalEssentialIncompleteness.V46.Miller.FiniteSemidecision

open Encodable
open Nat.Partrec (Code)

variable {α : Type*} [Primcodable α]

/-- The bounded ordinary evaluator gives a primitive-recursive positive
test, including on arbitrary encoded input types. -/
def haltsWithin (c : Code) (x : α) (fuel : ℕ) : Prop :=
  (c.evaln fuel (encode x)).isSome = true

instance haltsWithin_decidable (c : Code) : DecidableRel (haltsWithin (α := α) c) :=
  fun x fuel => inferInstanceAs (Decidable ((c.evaln fuel (encode x)).isSome = true))

theorem haltsWithin_primrec (c : Code) :
    PrimrecRel (haltsWithin (α := α) c) := by
  have he : Primrec (fun p : α × ℕ => c.evaln p.2 (encode p.1)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd (Primrec.const c))
        (Primrec.encode.comp Primrec.fst))
  exact Primrec.eq.comp (Primrec.option_isSome.comp he) (Primrec.const true)

theorem haltsWithin_mono (c : Code) (x : α) {k l : ℕ} (hkl : k ≤ l)
    (hk : haltsWithin c x k) : haltsWithin c x l := by
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp hk
  exact Option.isSome_iff_exists.mpr
    ⟨y,Nat.Partrec.Code.evaln_mono hkl hy⟩

/-- All finitely many successful computations have one common fuel
bound. The empty list uses fuel zero, without an inhabitant of α. -/
theorem list_uniform_fuel (c : Code) (L : List α) :
    (∀ x ∈ L,(c.eval (encode x)).Dom) ↔
      ∃ fuel,∀ x ∈ L,haltsWithin c x fuel := by
  constructor
  · induction L with
    | nil => exact fun _ => ⟨0,by simp⟩
    | cons x L ih =>
      intro h
      obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp (h x (List.mem_cons_self ..))
      obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hy
      obtain ⟨l,hl⟩ := ih (fun z hz => h z (List.mem_cons_of_mem x hz))
      refine ⟨max k l,?_⟩
      intro z hz
      obtain rfl | hz := List.mem_cons.mp hz
      · exact haltsWithin_mono c z (le_max_left k l)
          (Option.isSome_iff_exists.mpr ⟨y,hk⟩)
      · exact haltsWithin_mono c z (le_max_right k l) (hl z hz)
  · rintro ⟨fuel,hfuel⟩ x hx
    obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp (hfuel x hx)
    exact Part.dom_iff_mem.mpr ⟨y,Nat.Partrec.Code.evaln_sound hy⟩

/-- A finite list of instances of any recursively enumerable predicate
is semidecidable uniformly in the entire list. -/
theorem listAll_re {P : α → Prop} (hP : REPred P) :
    REPred (fun L : List α => ∀ x ∈ L,P x) := by
  obtain ⟨c,hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.bind_decode₂_iff.mp hP)
  have hc_dom (x : α) : (c.eval (encode x)).Dom ↔ P x := by
    rw [hc]
    dsimp only
    rw [Encodable.encodek₂]
    simp only [Part.coe_some,Part.bind_some]
    change ((Part.assert (P x) (fun _ => Part.some ())).map encode).Dom ↔ P x
    simp [Part.assert]
  have hfinite : REPred (fun q : List α × ℕ => ∀ x ∈ q.1,haltsWithin c x q.2) :=
    (haltsWithin_primrec (α := α) c).forall_mem_list.computablePred.to_re
  apply hfinite.projection.of_eq
  intro L
  exact (list_uniform_fuel c L).symm.trans
    ⟨fun h x hx => (hc_dom x).mp (h x hx),
      fun h x hx => (hc_dom x).mpr (h x hx)⟩

/-- Every functional recursively enumerable graph is the exact graph of
an ordinary partial recursive function. Its domain may be empty. -/
theorem functional_graph {R : α × ℕ → Prop} (hR : REPred R)
    (hU : ∀ a x y,R (a,x) → R (a,y) → x = y) :
    ∃ F : α → Part ℕ,Partrec F ∧ ∀ a m,m ∈ F a ↔ R (a,m) := by
  let f (a : α) (n : ℕ) : Part ℕ :=
    (Part.assert (R (a,n)) (fun _ => Part.some ())).map (fun _ => n)
  have hf : Partrec₂ f :=
    (Partrec.map hR ((Computable.snd.comp Computable.fst).to₂)).to₂
  have hmem (a : α) (n m : ℕ) : m ∈ f a n ↔ R (a,n) ∧ n = m := by
    simp [f,Part.mem_map_iff,Part.mem_assert_iff]
  obtain ⟨F,hF,hFgraph⟩ := Partrec.projection hf (by
    intro a n₁ n₂ m₁ m₂ h₁ h₂
    obtain ⟨hr₁,hm₁⟩ := (hmem a n₁ m₁).mp h₁
    obtain ⟨hr₂,hm₂⟩ := (hmem a n₂ m₂).mp h₂
    exact hm₁.symm.trans ((hU a n₁ n₂ hr₁ hr₂).trans hm₂))
  refine ⟨F,hF,fun a m => ?_⟩
  rw [hFgraph m a]
  constructor
  · rintro ⟨n,hn⟩
    obtain ⟨hr,rfl⟩ := (hmem a n m).mp hn
    exact hr
  · intro hr
    exact ⟨m,(hmem a m m).mpr ⟨hr,rfl⟩⟩

end CategoricalEssentialIncompleteness.V46.Miller.FiniteSemidecision
