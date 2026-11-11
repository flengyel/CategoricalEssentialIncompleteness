/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCutDigitsStrict
public import CategoricalEssentialIncompleteness.DisjointJoins


/-! # Definitions and theorems in `V46MillerCutInseparability` -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual parity diagonal and the consequence of a cut reduction

The diagonal theorem and source conditionals apply to the constructed
uniform category. The reusable cut consequence takes an ordinary recursive reduction.
The concrete Lemma8.3 reduction is supplied by CutReduction/CutApplications.
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability

open _root_.CategoricalEssentialIncompleteness.V46.Miller.Uniform
attribute [instance 2000] Uniform.nativeRestriction

def parityIso (P : Family) : N P ≅ coprod (N P) (N P) :=
  (Uniform.codeIso (Uniform.coproduct (N P) (N P))).symm

theorem parityIso_value (P : Family) :
    (parityIso P).hom.val = fun n : ℕ =>
      Part.some (if n%2=0 then Sum.inl (n/2) else Sum.inr (n/2)) := rfl

variable {P : Family}

def pair0 (τ : product (N P) (N P) ⟶ N P) : Idem (N P) :=
  Idem.pull (Uniform.diagonal (N P) ≫ τ ≫ (parityIso P).hom) (summand0 (N P) (N P))

def pair1 (τ : product (N P) (N P) ⟶ N P) : Idem (N P) :=
  Idem.pull (Uniform.diagonal (N P) ≫ τ ≫ (parityIso P).hom) (summand1 (N P) (N P))

theorem support_pull {X Y : Object P} (f : X ⟶ Y) (a : Idem Y) :
    Uniform.support (Idem.pull f a) = {x | ∃ y,y ∈ f.val x ∧ y ∈ Uniform.support a} :=
  PartialFunctions.support_pull f.val (Uniform.toPfnIdem a)

theorem support_summand0 {X Y : Object P} (s : carrier P (coprod X Y)) :
    s ∈ Uniform.support (summand0 X Y) ↔ ∃ x,s=Sum.inl x := by
  change ((summand0 X Y).hom.val s).Dom ↔ _
  simp only [summand0,Idem.sum_hom,Idem.top_hom,Idem.bot_hom,
    Uniform.coprod_map_rawVal,Uniform.id_val,Uniform.zero_val]
  cases s <;> simp [PartialFunctions.sumMap,Part.some,Part.none]

theorem support_summand1 {X Y : Object P} (s : carrier P (coprod X Y)) :
    s ∈ Uniform.support (summand1 X Y) ↔ ∃ y,s=Sum.inr y := by
  change ((summand1 X Y).hom.val s).Dom ↔ _
  simp only [summand1,Idem.sum_hom,Idem.top_hom,Idem.bot_hom,
    Uniform.coprod_map_rawVal,Uniform.id_val,Uniform.zero_val]
  cases s <;> simp [PartialFunctions.sumMap,Part.some,Part.none]

theorem support_pair0 (τ : product (N P) (N P) ⟶ N P) (e : ℕ) :
    e ∈ Uniform.support (pair0 τ) ↔ ∃ m:ℕ,m ∈ τ.val (e,e) ∧ m%2=0 := by
  rw [pair0,support_pull]
  change (∃ s,s ∈ (Uniform.diagonal (N P) ≫ τ ≫ (parityIso P).hom).val e ∧
    s ∈ Uniform.support (summand0 (N P) (N P))) ↔ _
  simp only [Uniform.comp_val,Uniform.diagonal_val,parityIso_value,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand0]
  constructor
  · rintro ⟨s,⟨m,hm,hms⟩,x,hx⟩
    refine ⟨m,hm,?_⟩
    split_ifs at hms with he
    · exact he
    · rw [hx] at hms
      cases hms
  · rintro ⟨m,hm,he⟩
    exact ⟨Sum.inl (m/2),⟨m,hm,by simp only [ite_eq_left he]⟩,m/2,rfl⟩

theorem support_pair1 (τ : product (N P) (N P) ⟶ N P) (e : ℕ) :
    e ∈ Uniform.support (pair1 τ) ↔ ∃ m:ℕ,m ∈ τ.val (e,e) ∧ m%2=1 := by
  rw [pair1,support_pull]
  change (∃ s,s ∈ (Uniform.diagonal (N P) ≫ τ ≫ (parityIso P).hom).val e ∧
    s ∈ Uniform.support (summand1 (N P) (N P))) ↔ _
  simp only [Uniform.comp_val,Uniform.diagonal_val,parityIso_value,Part.bind_some,
    Part.mem_bind_iff,Part.mem_some_iff,support_summand1]
  constructor
  · rintro ⟨s,⟨m,hm,hms⟩,x,hx⟩
    refine ⟨m,hm,?_⟩
    split_ifs at hms with he
    · rw [hx] at hms
      cases hms
    · omega
  · rintro ⟨m,hm,he⟩
    have hn : m%2≠0 := by omega
    exact ⟨Sum.inr (m/2),⟨m,hm,by simp only [ite_eq_right hn]⟩,m/2,rfl⟩

private theorem forbids_left (c : Idem (N P))
    (ℓ : N P ⟶ coprod (N P) (N P))
    (he : c.hom ≫ ℓ = c.hom ≫ i1 (N P) (N P))
    (x k : ℕ) (hx : x ∈ Uniform.support c) (hs : Sum.inl k ∈ ℓ.val x) : False := by
  have hcx : x ∈ c.hom.val x := (Uniform.mem_idem c x x).mpr ⟨hx,rfl⟩
  have hm : Sum.inl k ∈ (c.hom ≫ ℓ).val x :=
    Part.mem_bind_iff.mpr ⟨x,hcx,hs⟩
  rw [he] at hm
  change Sum.inl k ∈ (c.hom.val x).bind (fun y => Part.some (Sum.inr y)) at hm
  rw [Part.eq_some_iff.mpr hcx,Part.bind_some] at hm
  cases Part.mem_some_iff.mp hm

private theorem forbids_right (c : Idem (N P))
    (ℓ : N P ⟶ coprod (N P) (N P))
    (he : c.hom ≫ ℓ = c.hom ≫ i0 (N P) (N P))
    (x k : ℕ) (hx : x ∈ Uniform.support c) (hs : Sum.inr k ∈ ℓ.val x) : False := by
  have hcx : x ∈ c.hom.val x := (Uniform.mem_idem c x x).mpr ⟨hx,rfl⟩
  have hm : Sum.inr k ∈ (c.hom ≫ ℓ).val x :=
    Part.mem_bind_iff.mpr ⟨x,hcx,hs⟩
  rw [he] at hm
  change Sum.inr k ∈ (c.hom.val x).bind (fun y => Part.some (Sum.inl y)) at hm
  rw [Part.eq_some_iff.mpr hcx,Part.bind_some] at hm
  cases Part.mem_some_iff.mp hm

/-- This is the categorical diagonal argument, with the actual source
switch supplied by disjoint joins. It quantifies over every source
complementary pair and uses the full Turing property on all partial arrows. -/
theorem turing_pair_inseparable (τ : product (N P) (N P) ⟶ N P)
    (hτ : RecursionCategory.IsTuringMorphism τ) : Inseparable (pair0 τ) (pair1 τ) := by
  constructor
  · rw [pair0,pair1,← Idem.pull_inf,summands_disjoint,Idem.pull_bot]
  · rintro ⟨c,c',hc,ha,hb⟩
    obtain ⟨ℓ,hℓ,hcℓ,hc'ℓ,_⟩ := disjoint_joins_switch c c' hc.toPair
    obtain ⟨g,hg,he⟩ := turing_diagonal τ hτ (parityIso P) ℓ
    have hgnative : isTotal g := (Uniform.induced_restriction g).symm.trans hg
    obtain ⟨x,hx⟩ := Part.dom_iff_mem.mp ((Uniform.total_iff g).mp hgnative (0:ℕ))
    obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp ((Uniform.total_iff ℓ).mp hℓ x)
    let D := Uniform.diagonal (N P) ≫ τ ≫ (parityIso P).hom
    have he' : g ≫ D = g ≫ ℓ := he
    have hm : s ∈ (g ≫ D).val (0:ℕ) := by
      rw [he']
      exact Part.mem_bind_iff.mpr ⟨x,hx,hs⟩
    obtain ⟨x',hx',hD⟩ := Part.mem_bind_iff.mp hm
    have hxx : x'=x := Part.mem_unique hx' hx
    subst x'
    cases s with
    | inl k =>
      have h₀ : x ∈ Uniform.support (pair0 τ) :=
        (Set.ext_iff.mp (support_pull D (summand0 (N P) (N P))) x).mpr
          ⟨Sum.inl k,hD,(support_summand0 _).mpr ⟨k,rfl⟩⟩
      exact forbids_left c ℓ hcℓ x k ((Uniform.support_le_iff _ _).mp ha h₀) hs
    | inr k =>
      have h₁ : x ∈ Uniform.support (pair1 τ) :=
        (Set.ext_iff.mp (support_pull D (summand1 (N P) (N P))) x).mpr
          ⟨Sum.inr k,hD,(support_summand1 _).mpr ⟨k,rfl⟩⟩
      exact forbids_right c' ℓ hc'ℓ x k ((Uniform.support_le_iff _ _).mp hb h₁) hs

def diagonal0 (z : Point) := pair0 (Uniform.tau z)
def diagonal1 (z : Point) := pair1 (Uniform.tau z)

/-- No Miller-property assumption is needed for this source categorical
pair; the actual unanimous evaluator already has the Turing property. -/
theorem source_diagonal_inseparable (z : Point) :
    Inseparable (diagonal0 z) (diagonal1 z) :=
  turing_pair_inseparable (Uniform.tau z) (Uniform.tau_isTuring z)

theorem diagonal0_support (z : Point) (e : ℕ) :
    e ∈ Uniform.support (diagonal0 z) ↔
      ∃ m,m ∈ Unanimity.tau z e e ∧ m%2=0 := support_pair0 (Uniform.tau z) e

theorem diagonal1_support (z : Point) (e : ℕ) :
    e ∈ Uniform.support (diagonal1 z) ↔
      ∃ m,m ∈ Unanimity.tau z e e ∧ m%2=1 := support_pair1 (Uniform.tau z) e

private theorem idem_ext_support {X : Object P} {a b : Idem X}
    (h : Uniform.support a = Uniform.support b) : a=b := by
  apply Idem.ext
  apply Uniform.hom_ext_mem
  intro x y
  simp only [Uniform.mem_idem,h]

theorem support_recursive_pull (h : ℕ → ℕ) (hh : Computable h) (a : Idem (N P)) :
    Uniform.support (Idem.pull (Uniform.totalFromFunction (X:=N P) (Y:=N P) h hh) a) =
      h ⁻¹' Uniform.support a := by
  rw [support_pull]
  ext x
  change (∃ y,y ∈ Part.some (h x) ∧ y ∈ Uniform.support a) ↔ h x ∈ Uniform.support a
  simp only [Part.mem_some_iff,exists_eq_left]

/-- The reusable reduction premise is displayed with its exact two inverse-image
equations. This consequence does not prove or assume any further part of
Lemma8.3, nor does it replace its ordinary recursive requirement. -/
theorem cuts_inseparable_of_recursive_reduction (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' CutDigits.lowerCut z = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' CutDigits.upperCut z = Uniform.support (diagonal1 z)) :
    Inseparable (CutDigits.lowerIdem z) (CutDigits.upperIdem z) := by
  let θ : N (Family.ofPoint z) ⟶ N (Family.ofPoint z) := Uniform.totalFromFunction h hh
  have hθ : isTotal θ := Uniform.totalFromFunction_total (X:=N (Family.ofPoint z)) (Y:=N (Family.ofPoint z)) h hh
  have e₀ : Idem.pull θ (CutDigits.lowerIdem z) = diagonal0 z :=
    idem_ext_support (by rw [support_recursive_pull,CutDigits.lowerIdem_support,h₀])
  have e₁ : Idem.pull θ (CutDigits.upperIdem z) = diagonal1 z :=
    idem_ext_support (by rw [support_recursive_pull,CutDigits.upperIdem_support,h₁])
  constructor
  · apply idem_ext_support
    change PartialFunctions.support (Uniform.toPfnIdem
      (CutDigits.lowerIdem z ⊓ CutDigits.upperIdem z)) =
        PartialFunctions.support (Uniform.toPfnIdem (⊥ : Idem (N (Family.ofPoint z))))
    rw [Uniform.toPfnIdem_inf,Uniform.toPfnIdem_bot,PartialFunctions.support_inf,
      PartialFunctions.support_bot]
    change CutDigits.lowerCut z ∩ CutDigits.upperCut z = ∅
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro n hn
    change (z n:ℝ)<1/2 ∧ 1/2<(z n:ℝ) at hn
    exact (not_lt_of_ge (le_of_lt hn.1)) hn.2
  · rintro ⟨c,c',hc,ha,hb⟩
    apply (source_diagonal_inseparable z).no_separator
    refine ⟨Idem.pull θ c,Idem.pull θ c',hc.pull θ hθ,?_,?_⟩
    · rw [← e₀]
      exact Idem.pull_mono θ ha
    · rw [← e₁]
      exact Idem.pull_mono θ hb

theorem diagonal_fixed_separator_of_recursive_reduction
    (z : Point) (h : ℕ → ℕ) (hh : Computable h)
    (h₀ : h ⁻¹' CutDigits.lowerCut z = Uniform.support (diagonal0 z))
    (h₁ : h ⁻¹' CutDigits.upperCut z = Uniform.support (diagonal1 z))
    (p : Bits) (hp : p ∈ representations z) :
    Uniform.support (diagonal0 z) ⊆ h ⁻¹' CutDigits.separator p ∧
      Disjoint (h ⁻¹' CutDigits.separator p) (Uniform.support (diagonal1 z)) ∧
      Nat.RecursiveIn (OracleComputation.oracleSet (OracleRelative.oracleSupport p))
        (fun e => Part.some (CutDigits.decision p (h e))) := by
  have hsep := CutDigits.separates_point z p hp
  refine ⟨?_,?_,?_⟩
  · intro e he
    exact hsep.1 ((Set.ext_iff.mp h₀ e).mpr he)
  · apply Set.disjoint_left.mpr
    intro e he hA
    exact Set.disjoint_left.mp hsep.2 he ((Set.ext_iff.mp h₁ e).mpr hA)
  · apply (Nat.RecursiveIn.comp (CutDigits.decision_recursiveIn p)
      (OracleComputation.recursiveIn_of_computable hh)).of_eq
    intro e
    exact Part.bind_some (h e) (fun n => Part.some (CutDigits.decision p n))

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability
