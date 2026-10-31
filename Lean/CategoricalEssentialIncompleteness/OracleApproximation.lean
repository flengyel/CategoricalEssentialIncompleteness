/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleDomainNumbering

/-! # Ordinary partial computations using finite oracle tables -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

def MonotoneValues (F : List ℕ × ℕ → Part ℕ) : Prop :=
  ∀ l l',l <+: l' → ∀ x y,y ∈ F (l,x) → y ∈ F (l',x)

def Represents (S : Set ℕ) (F : List ℕ × ℕ → Part ℕ) (f : ℕ → Part ℕ) : Prop :=
  ∀ x y,y ∈ f x ↔ ∃ n,y ∈ F (oraclePrefix S n,x)

def HasApproximation (S : Set ℕ) (f : ℕ → Part ℕ) : Prop :=
  ∃ F : List ℕ × ℕ → Part ℕ,Partrec F ∧ MonotoneValues F ∧ Represents S F f

namespace HasApproximation

variable {S : Set ℕ} {f g : ℕ → Part ℕ}

theorem of_eq (hf : HasApproximation S f) (h : ∀ x,f x=g x) : HasApproximation S g :=
  (funext h : f=g) ▸ hf

theorem of_partrec (hf : Partrec f) : HasApproximation S f :=
  ⟨fun p => f p.2,hf.comp Computable.snd,fun _ _ _ _ _ h => h,
    fun _ _ => ⟨fun h => ⟨0,h⟩,fun ⟨_,h⟩ => h⟩⟩

theorem oracle : HasApproximation S (fun n => Part.some (answer S n)) := by
  let F : List ℕ × ℕ → Part ℕ := fun p => ↑(p.1[p.2]?)
  have hF : Partrec F := Computable.ofOption Primrec.list_getElem?.to_comp
  have hm : MonotoneValues F := by
    rintro l l' ⟨t,rfl⟩ x y hy
    change y ∈ (↑(l[x]?) : Part ℕ) at hy
    change y ∈ (↑((l++t)[x]?) : Part ℕ)
    have he : l[x]?=some y := by simpa only [Part.mem_coe,Option.mem_def] using hy
    have hx : x<l.length := (List.getElem?_eq_some_iff.mp he).1
    simpa only [List.getElem?_append_left hx] using hy
  refine ⟨F,hF,hm,?_⟩
  intro x y
  constructor
  · intro hy
    have he : y=answer S x := Part.mem_some_iff.mp hy
    refine ⟨x+1,?_⟩
    change y ∈ (↑((oraclePrefix S (x+1))[x]?) : Part ℕ)
    simp only [oraclePrefix,List.getElem?_map,List.getElem?_range (by omega : x<x+1),
      Option.map_some,Part.coe_some,Part.mem_some_iff]
    exact he
  · rintro ⟨n,hy⟩
    have he : (oraclePrefix S n)[x]?=some y := by
      simpa only [F,Part.mem_coe,Option.mem_def] using hy
    have hx : x<n := by simpa only [prefix_length] using (List.getElem?_eq_some_iff.mp he).1
    rw [oraclePrefix,List.getElem?_map,List.getElem?_range hx,Option.map_some] at he
    exact Part.mem_some_iff.mpr (Option.some.inj he).symm

theorem pair (hf : HasApproximation S f) (hg : HasApproximation S g) :
    HasApproximation S (fun x => (f x).bind fun a => (g x).map (Nat.pair a)) := by
  obtain ⟨F,hF,hMF,hf⟩ := hf
  obtain ⟨G,hG,hMG,hg⟩ := hg
  let H : List ℕ × ℕ → Part ℕ :=
    fun p => (F p).bind fun a => (G p).map (Nat.pair a)
  have hH : Partrec H := hF.bind
    (((hG.comp Computable.fst).map (Primrec₂.natPair.to_comp.comp
      (Computable.snd.comp Computable.fst) Computable.snd).to₂).to₂)
  have hm : MonotoneValues H := by
    intro l l' hl x y hy
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hb
    exact Part.mem_bind_iff.mpr ⟨a,hMF l l' hl x a ha,
      (Part.mem_map_iff _).mpr ⟨b,hMG l l' hl x b hb,he⟩⟩
  refine ⟨H,hH,hm,?_⟩
  intro x y
  constructor
  · intro hy
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hb
    obtain ⟨n,hn⟩ := (hf x a).mp ha
    obtain ⟨m,hm⟩ := (hg x b).mp hb
    exact ⟨max n m,Part.mem_bind_iff.mpr ⟨a,hMF _ _ (prefix_le S (le_max_left n m)) x a hn,
      (Part.mem_map_iff _).mpr ⟨b,hMG _ _ (prefix_le S (le_max_right n m)) x b hm,he⟩⟩⟩
  · rintro ⟨n,hy⟩
    obtain ⟨a,ha,hb⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hb
    exact Part.mem_bind_iff.mpr ⟨a,(hf x a).mpr ⟨n,ha⟩,
      (Part.mem_map_iff _).mpr ⟨b,(hg x b).mpr ⟨n,hb⟩,he⟩⟩

theorem comp (hf : HasApproximation S f) (hg : HasApproximation S g) :
    HasApproximation S (fun x => (g x).bind f) := by
  obtain ⟨F,hF,hMF,hf⟩ := hf
  obtain ⟨G,hG,hMG,hg⟩ := hg
  let H : List ℕ × ℕ → Part ℕ := fun p => (G p).bind fun a => F (p.1,a)
  have hH : Partrec H := hG.bind
    ((hF.comp (Computable.pair (Computable.fst.comp Computable.fst) Computable.snd)).to₂)
  have hm : MonotoneValues H := by
    intro l l' hl x y hy
    obtain ⟨a,ha,hy⟩ := Part.mem_bind_iff.mp hy
    exact Part.mem_bind_iff.mpr ⟨a,hMG l l' hl x a ha,hMF l l' hl a y hy⟩
  refine ⟨H,hH,hm,?_⟩
  intro x y
  constructor
  · intro hy
    obtain ⟨a,ha,hy⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨n,hn⟩ := (hg x a).mp ha
    obtain ⟨m,hm⟩ := (hf a y).mp hy
    exact ⟨max n m,Part.mem_bind_iff.mpr
      ⟨a,hMG _ _ (prefix_le S (le_max_left n m)) x a hn,
        hMF _ _ (prefix_le S (le_max_right n m)) a y hm⟩⟩
  · rintro ⟨n,hy⟩
    obtain ⟨a,ha,hy⟩ := Part.mem_bind_iff.mp hy
    exact Part.mem_bind_iff.mpr ⟨a,(hg x a).mpr ⟨n,ha⟩,(hf a y).mpr ⟨n,hy⟩⟩

end HasApproximation
end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
