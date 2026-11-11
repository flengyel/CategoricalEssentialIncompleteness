/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkUniversal

/-! # Coherent recursive parameters and total embeddings into the universal fork -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def assemble (g0 g1 g2 : ℕ → ℕ) (q : ℕ × ℕ × ℕ) : ℕ :=
  quadCode (0, g0 q.1, g1 q.2.1, g2 q.2.2)

theorem assemble_computable {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) :
    Computable (assemble g0 g1 g2) :=
  quadCode_computable.comp (Computable.pair (.const 0)
    (Computable.pair (h0.comp .fst) (Computable.pair
      (h1.comp (Computable.fst.comp Computable.snd))
      (h2.comp (Computable.snd.comp Computable.snd)))))

def centerEncoding (X : Object) (g0 g1 g2 : ℕ → ℕ) (x : ℕ) : Part ℕ :=
  (val X.leftMap x).bind fun a => (val X.rightMap x).map
    (fun b => assemble g0 g1 g2 (x,a,b))

theorem centerEncoding_partrec (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) :
    Partrec (centerEncoding X g0 g1 g2) :=
  (EnumerableCarriers.val_partrec X.leftMap).bind
    (((EnumerableCarriers.val_partrec X.rightMap).comp Computable.fst).map
      ((assemble_computable h0 h1 h2).comp (Computable.pair
        (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))).to₂).to₂

theorem mem_centerEncoding (X : Object) (g0 g1 g2 : ℕ → ℕ) (x y : ℕ) :
    y ∈ centerEncoding X g0 g1 g2 x ↔
      ∃ a, a ∈ val X.leftMap x ∧ ∃ b, b ∈ val X.rightMap x ∧
        quadCode (0,g0 x,g1 a,g2 b)=y := by
  simp only [centerEncoding, Part.mem_bind_iff, Part.mem_map_iff, assemble]

def centerEncodingArrow (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) : X.center ⟶ natCarrier :=
  EnumerableCarriers.arrow (centerEncoding X g0 g1 g2) (centerEncoding_partrec X h0 h1 h2)
    (by
      intro x y h
      obtain ⟨a, ha, _⟩ := (mem_centerEncoding X g0 g1 g2 x y).mp h
      exact EnumerableCarriers.val_source X.leftMap x a ha)
    (fun _ _ _ => Set.mem_univ _)

def endpointEncoding {X : Carrier} (g : ℕ → ℕ) (hg : Computable g) : X ⟶ natCarrier :=
  EnumerableCarriers.totalFromFunction (fun n => Nat.pair 0 (g n))
    (Primrec₂.natPair.to_comp.comp (.const 0) hg) (fun _ _ => Set.mem_univ _)

theorem mem_endpointEncoding {X : Carrier} (g : ℕ → ℕ) (hg : Computable g) (x y : ℕ) :
    y ∈ val (endpointEncoding (X := X) g hg) x ↔ x ∈ X.support ∧ y=Nat.pair 0 (g x) :=
  EnumerableCarriers.mem_totalFromFunction _
    (Primrec₂.natPair.to_comp.comp (.const 0) hg) (fun _ _ => Set.mem_univ _) x y

theorem encoding_left_natural (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) :
    Respects X.leftMap V.leftMap (centerEncodingArrow X h0 h1 h2) (endpointEncoding g1 h1) := by
  intro x y u v hxy hxu hyv
  obtain ⟨a, ha, b, hb, he⟩ := (mem_centerEncoding X g0 g1 g2 x y).mp hxy
  have hv := (mem_V_left y v).mp hyv
  rw [← he, left_quad] at hv
  have hau : a=u := Part.mem_unique ha hxu
  exact (mem_endpointEncoding g1 h1 u v).mpr
    ⟨EnumerableCarriers.val_target X.leftMap x u hxu, hau ▸ hv⟩

theorem encoding_right_natural (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) :
    Respects X.rightMap V.rightMap (centerEncodingArrow X h0 h1 h2) (endpointEncoding g2 h2) := by
  intro x y u v hxy hxu hyv
  obtain ⟨a, ha, b, hb, he⟩ := (mem_centerEncoding X g0 g1 g2 x y).mp hxy
  have hv := (mem_V_right y v).mp hyv
  rw [← he, right_quad] at hv
  have hbu : b=u := Part.mem_unique hb hxu
  exact (mem_endpointEncoding g2 h2 u v).mpr
    ⟨EnumerableCarriers.val_target X.rightMap x u hxu, hbu ▸ hv⟩

def coherentEncoding (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) : X ⟶ V :=
  ⟨centerEncodingArrow X h0 h1 h2, endpointEncoding g1 h1, endpointEncoding g2 h2,
    encoding_left_natural X h0 h1 h2, encoding_right_natural X h0 h1 h2⟩

theorem coherentEncoding_total (X : Object) {g0 g1 g2 : ℕ → ℕ}
    (h0 : Computable g0) (h1 : Computable g1) (h2 : Computable g2) :
    isTotal (coherentEncoding X h0 h1 h2) := by
  apply (total_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (EnumerableCarriers.total_iff _).mpr
    intro x hx
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.leftMap).mp X.left_total x hx)
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.rightMap).mp X.right_total x hx)
    exact Part.dom_iff_mem.mpr ⟨quadCode (0,g0 x,g1 a,g2 b),
      (mem_centerEncoding X g0 g1 g2 x _).mpr ⟨a,ha,b,hb,rfl⟩⟩
  · exact EnumerableCarriers.totalFromFunction_total _
      (Primrec₂.natPair.to_comp.comp (.const 0) h1) (fun _ _ => Set.mem_univ _)
  · exact EnumerableCarriers.totalFromFunction_total _
      (Primrec₂.natPair.to_comp.comp (.const 0) h2) (fun _ _ => Set.mem_univ _)

def embedding (X : Object) : X ⟶ V := coherentEncoding X Computable.id Computable.id Computable.id

theorem embedding_injective (X : Object) : Injective (embedding X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x x' y hxy hx'y
    obtain ⟨a, ha, b, hb, he⟩ := (mem_centerEncoding X id id id x y).mp hxy
    obtain ⟨a', ha', b', hb', he'⟩ := (mem_centerEncoding X id id id x' y).mp hx'y
    exact congrArg (fun q : ℕ×ℕ×ℕ×ℕ => q.2.1) (quadCode.injective (he.trans he'.symm))
  · intro x x' y hxy hx'y
    obtain ⟨_, he⟩ := (mem_endpointEncoding id Computable.id x y).mp hxy
    obtain ⟨_, he'⟩ := (mem_endpointEncoding id Computable.id x' y).mp hx'y
    exact (Nat.pair_eq_pair.mp (he.symm.trans he')).2
  · intro x x' y hxy hx'y
    obtain ⟨_, he⟩ := (mem_endpointEncoding id Computable.id x y).mp hxy
    obtain ⟨_, he'⟩ := (mem_endpointEncoding id Computable.id x' y).mp hx'y
    exact (Nat.pair_eq_pair.mp (he.symm.trans he')).2

/-- Lemma A.5: every computational fork has the specified total restriction embedding. -/
theorem dominance (X : Object) :
    ∃ (m : X ⟶ V) (s : V ⟶ X), isTotal m ∧ m ≫ s = 𝟙 X ∧ s ≫ m = rst s := by
  let m := embedding X
  have hm : isTotal m := coherentEncoding_total X Computable.id Computable.id Computable.id
  have hi : Injective m := embedding_injective X
  obtain ⟨s, hs⟩ := section_of_injective m hi
  have he := partialMono_of_injective m hi (m ≫ s) (𝟙 X)
    (by simpa only [Category.assoc, Category.id_comp] using hs.receives)
  rw [show rst m=𝟙 X from hm, Category.comp_id, Category.id_comp] at he
  exact ⟨m,s,hm,he,hs.comp⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
