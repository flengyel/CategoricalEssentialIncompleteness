/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ExponentialPairingPrimrec
public import CategoricalEssentialIncompleteness.V46PrintedObjectCodingModels
public import Mathlib.SetTheory.ZFC.Basic

/-! # Realized sets of the syntactic recursion category

Section 6 realizes formal object terms as sets, starting with the von Neumann ordinal `ω`.
The coordinate projections and the two tag fibres recover the factors and summands.
-/

@[expose] public section

noncomputable section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RealizedObjectSets

/-- The finite von Neumann ordinal with `n` elements. -/
def ordinal (n : ℕ) : ZFSet.{0} := ZFSet.mk (PSet.ofNat n)

theorem ordinal_mem_omega (n : ℕ) : ordinal n ∈ ZFSet.omega :=
  ⟨⟨n⟩, PSet.Equiv.rfl⟩

private theorem ordinal_mem_of_lt {n m : ℕ} (h : n < m) : ordinal n ∈ ordinal m := by
  induction m with
  | zero => exact (Nat.not_lt_zero n h).elim
  | succ m ih =>
    change ordinal n ∈ insert (ordinal m) (ordinal m)
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hm | rfl
    · exact ZFSet.mem_insert_of_mem _ (ih hm)
    · exact ZFSet.mem_insert _ _

theorem ordinal_injective : Function.Injective ordinal := by
  intro n m he
  rcases lt_trichotomy n m with h | h | h
  · exact (ZFSet.mem_irrefl _ (he ▸ ordinal_mem_of_lt h)).elim
  · exact h
  · exact (ZFSet.mem_irrefl _ (he.symm ▸ ordinal_mem_of_lt h)).elim

/-- Each member of `ω` is a unique finite von Neumann ordinal. -/
def ordinalEquiv : ℕ ≃ ↥(ZFSet.omega.{0}) :=
  Equiv.ofBijective (fun n => ⟨ordinal n, ordinal_mem_omega n⟩) <| by
    constructor
    · intro m n he
      exact ordinal_injective (congrArg Subtype.val he)
    · rintro ⟨x, hx⟩
      obtain ⟨z, rfl⟩ := Quotient.exists_rep x
      obtain ⟨⟨n⟩, h⟩ := hx
      exact ⟨n, Subtype.ext (ZFSet.sound h.symm)⟩

/-- The disjoint union in §6 tags its two summands on the right by `0` and `1`. -/
def taggedUnion (A B : ZFSet.{0}) : ZFSet.{0} :=
  A.prod {ordinal 0} ∪ B.prod {ordinal 1}

theorem pair_mem_taggedUnion {A B x i : ZFSet.{0}} :
    x.pair i ∈ taggedUnion A B ↔ (x ∈ A ∧ i = ordinal 0) ∨ (x ∈ B ∧ i = ordinal 1) := by
  simp only [taggedUnion, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

private theorem tag_ne : ordinal 0 ≠ ordinal 1 := ordinal_injective.ne (by decide)

theorem tag_zero_fibre {A B x : ZFSet.{0}} :
    x.pair (ordinal 0) ∈ taggedUnion A B ↔ x ∈ A := by simp [pair_mem_taggedUnion, tag_ne]

theorem tag_one_fibre {A B x : ZFSet.{0}} :
    x.pair (ordinal 1) ∈ taggedUnion A B ↔ x ∈ B := by simp [pair_mem_taggedUnion, tag_ne.symm]

/-- The realization of an object term by Kuratowski products and tagged unions. -/
def realize : STObjectCode → ZFSet.{0}
  | .omega => ZFSet.omega
  | .product X Y => (realize X).prod (realize Y)
  | .coproduct X Y => taggedUnion (realize X) (realize Y)

/-- A pair of members determines a member of the Cartesian product. -/
def productMember {A B : ZFSet.{0}} (x : A) (y : B) : A.prod B :=
  ⟨x.val.pair y.val, ZFSet.pair_mem_prod.mpr ⟨x.property, y.property⟩⟩

def productEquiv (A B : ZFSet.{0}) : (A × B) ≃ ↥(A.prod B) :=
  Equiv.ofBijective (fun p => productMember p.1 p.2) <| by
    constructor
    · intro p q hpq
      obtain ⟨h, k⟩ := ZFSet.pair_inj.mp (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext h) (Subtype.ext k)
    · rintro ⟨z, hz⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.mp hz
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

/-- Either tag supplies a member of the disjoint union. -/
def taggedMember {A B : ZFSet.{0}} : A ⊕ B → ↥(taggedUnion A B)
  | .inl x => ⟨x.val.pair (ordinal 0), tag_zero_fibre.mpr x.property⟩
  | .inr y => ⟨y.val.pair (ordinal 1), tag_one_fibre.mpr y.property⟩

def taggedEquiv (A B : ZFSet.{0}) : (A ⊕ B) ≃ ↥(taggedUnion A B) :=
  Equiv.ofBijective taggedMember <| by
    constructor
    · intro p q he
      cases p <;> cases q <;> have h := ZFSet.pair_inj.mp (congrArg Subtype.val he)
      · exact congrArg Sum.inl (Subtype.ext h.1)
      · exact (tag_ne h.2).elim
      · exact (tag_ne h.2.symm).elim
      · exact congrArg Sum.inr (Subtype.ext h.1)
    · rintro ⟨z, hz⟩
      rcases ZFSet.mem_union.mp hz with hl | hr
      · obtain ⟨a, ha, i, hi, rfl⟩ := ZFSet.mem_prod.mp hl
        obtain rfl := ZFSet.mem_singleton.mp hi
        exact ⟨.inl ⟨a, ha⟩, rfl⟩
      · obtain ⟨b, hb, i, hi, rfl⟩ := ZFSet.mem_prod.mp hr
        obtain rfl := ZFSet.mem_singleton.mp hi
        exact ⟨.inr ⟨b, hb⟩, rfl⟩

/-- The members of each realized set are precisely its recursively interpreted values. -/
def members : (X : STObjectCode) → SyntacticModel.interpretedType ℕ X ≃ ↥(realize X)
  | .omega => ordinalEquiv
  | .product X Y => (Equiv.prodCongr (members X) (members Y)).trans (productEquiv _ _)
  | .coproduct X Y => (Equiv.sumCongr (members X) (members Y)).trans (taggedEquiv _ _)

/-- The bijection `γ_X` of §6 on the members of the realized set. -/
def coding (X : STObjectCode) : ↥(realize X) ≃ ℕ :=
  (members X).symm.trans (PrintedObjectCoding.valueEquiv 𝗣𝗔 ℕ X)

private theorem coding_members (X : STObjectCode) (x : SyntacticModel.interpretedType ℕ X) :
    coding X (members X x) = PrintedObjectCoding.value ℕ X x := by
  simp [coding, PrintedObjectCoding.valueEquiv]

theorem coding_ordinal (n : ℕ) : coding .omega ⟨ordinal n, ordinal_mem_omega n⟩ = n :=
  coding_members .omega n

theorem coding_product (X Y : STObjectCode) (x : realize X) (y : realize Y) :
    coding (.product X Y) (productMember x y) = 2 ^ coding X x * (2 * coding Y y + 1) - 1 := by
  obtain ⟨a, rfl⟩ := (members X).surjective x
  obtain ⟨b, rfl⟩ := (members Y).surjective y
  change coding (.product X Y) (members (.product X Y) (a, b)) = _
  rw [coding_members (.product X Y) (a, b), coding_members X a, coding_members Y b]
  exact ExponentialPairing.code_nat _ _

theorem coding_inl (X Y : STObjectCode) (x : realize X) :
    coding (.coproduct X Y) (taggedMember (.inl x)) = 2 * coding X x := by
  obtain ⟨a, rfl⟩ := (members X).surjective x
  change coding (.coproduct X Y) (members (.coproduct X Y) (.inl a)) = _
  rw [coding_members (.coproduct X Y) (.inl a), coding_members X a]
  rfl

theorem coding_inr (X Y : STObjectCode) (y : realize Y) :
    coding (.coproduct X Y) (taggedMember (.inr y)) = 2 * coding Y y + 1 := by
  obtain ⟨b, rfl⟩ := (members Y).surjective y
  change coding (.coproduct X Y) (members (.coproduct X Y) (.inr b)) = _
  rw [coding_members (.coproduct X Y) (.inr b), coding_members Y b]
  rfl

/-- The coding program converts a typed program input to the numerical code of its set member. -/
theorem coding_program (X : STObjectCode) (x : realize X) :
    SyntacticModel.programRelation 𝗣𝗔 ℕ (PrintedObjectCoding.isoToOmega 𝗣𝗔 X).hom.val
      (SyntacticModel.codingEquiv 𝗣𝗔 ℕ X ((members X).symm x)).val (coding X x) :=
  PrintedObjectCoding.value_model 𝗣𝗔 ℕ X ((members X).symm x)

/-- The inverse program recovers the typed value from its set member's numerical code. -/
theorem inverse_coding_program (X : STObjectCode) (x : realize X) (n : ℕ) :
    SyntacticModel.programRelation 𝗣𝗔 ℕ (PrintedObjectCoding.isoToOmega 𝗣𝗔 X).inv.val
      (coding X x) n ↔ n = (SyntacticModel.codingEquiv 𝗣𝗔 ℕ X ((members X).symm x)).val :=
  PrintedObjectCoding.inverse_value_model 𝗣𝗔 ℕ X ((members X).symm x) n

theorem infinite_realize (X : STObjectCode) : (realize X : Set ZFSet.{0}).Infinite :=
  Set.infinite_coe_iff.mp (Infinite.of_injective _ (coding X).symm.injective)

open scoped ZFSet

/-- The set of first coordinates of ordered pairs in `R`. -/
def firstProjection (R : ZFSet.{0}) : ZFSet.{0} :=
  (⋃₀ ⋃₀ R).sep (fun x => ∃ y, x.pair y ∈ R)

/-- The set of second coordinates of ordered pairs in `R`. -/
def secondProjection (R : ZFSet.{0}) : ZFSet.{0} :=
  (⋃₀ ⋃₀ R).sep (fun y => ∃ x, ZFSet.pair x y ∈ R)

private theorem pair_coordinates {R x y : ZFSet.{0}} (h : x.pair y ∈ R) :
    x ∈ ⋃₀ ⋃₀ R ∧ y ∈ ⋃₀ ⋃₀ R := by
  have hxy : ({x, y} : ZFSet) ∈ ⋃₀ R :=
    ZFSet.mem_sUnion.mpr ⟨_, h, ZFSet.mem_pair.mpr (Or.inr rfl)⟩
  exact ⟨ZFSet.mem_sUnion.mpr ⟨_, hxy, ZFSet.mem_pair.mpr (Or.inl rfl)⟩,
    ZFSet.mem_sUnion.mpr ⟨_, hxy, ZFSet.mem_pair.mpr (Or.inr rfl)⟩⟩

theorem mem_firstProjection {R x : ZFSet.{0}} :
    x ∈ firstProjection R ↔ ∃ y, x.pair y ∈ R := by
  rw [firstProjection, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨y, h⟩ => ⟨(pair_coordinates h).1, y, h⟩⟩

theorem mem_secondProjection {R y : ZFSet.{0}} :
    y ∈ secondProjection R ↔ ∃ x, ZFSet.pair x y ∈ R := by
  rw [secondProjection, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨x, h⟩ => ⟨(pair_coordinates h).2, x, h⟩⟩

theorem firstProjection_product (A B : ZFSet.{0}) (hB : B.Nonempty) :
    firstProjection (A.prod B) = A := by
  apply ZFSet.ext
  intro x
  simpa only [mem_firstProjection, ZFSet.pair_mem_prod, exists_and_left, ZFSet.nonempty_def]
    using and_iff_left hB (a := x ∈ A)

theorem secondProjection_product (A B : ZFSet.{0}) (hA : A.Nonempty) :
    secondProjection (A.prod B) = B := by
  apply ZFSet.ext
  intro y
  simpa only [mem_secondProjection, ZFSet.pair_mem_prod, exists_and_right, ZFSet.nonempty_def]
    using and_iff_right hA (b := y ∈ B)

theorem secondProjection_taggedUnion (A B : ZFSet.{0}) (hA : A.Nonempty) (hB : B.Nonempty) :
    secondProjection (taggedUnion A B) = {ordinal 0, ordinal 1} := by
  apply ZFSet.ext
  intro i
  simpa only [mem_secondProjection, pair_mem_taggedUnion, exists_or, exists_and_right,
    ZFSet.mem_pair, ZFSet.nonempty_def] using or_congr (and_iff_right hA (b := i = ordinal 0))
      (and_iff_right hB (b := i = ordinal 1))

theorem taggedUnion_injective : Function.Injective2 taggedUnion := by
  intro A C B D he
  exact ⟨ZFSet.ext fun x => by rw [← tag_zero_fibre (B := B), he, tag_zero_fibre],
    ZFSet.ext fun x => by rw [← tag_one_fibre (A := A), he, tag_one_fibre]⟩

private theorem empty_notMem_product (A B : ZFSet.{0}) : ∅ ∉ A.prod B := by
  intro h
  obtain ⟨a, _, b, _, he⟩ := ZFSet.mem_prod.mp h
  have hpair : ({a} : ZFSet) ∈ a.pair b := ZFSet.mem_pair.mpr (Or.inl rfl)
  exact ZFSet.notMem_empty _ (he.symm ▸ hpair)

theorem omega_ne_product (A B : ZFSet.{0}) : ZFSet.omega ≠ A.prod B :=
  fun h => empty_notMem_product A B (h ▸ ZFSet.omega_zero)

theorem omega_ne_taggedUnion (A B : ZFSet.{0}) : ZFSet.omega ≠ taggedUnion A B := by
  intro he
  rcases ZFSet.mem_union.mp (he ▸ ZFSet.omega_zero) with h | h
  · exact empty_notMem_product _ _ h
  · exact empty_notMem_product _ _ h

theorem product_ne_taggedUnion (X Y Z W : STObjectCode) :
    (realize X).prod (realize Y) ≠ taggedUnion (realize Z) (realize W) := by
  intro he
  have h := congrArg secondProjection he
  rw [secondProjection_product _ _ (infinite_realize X).nonempty,
    secondProjection_taggedUnion _ _ (infinite_realize Z).nonempty
      (infinite_realize W).nonempty] at h
  have hinf := infinite_realize Y
  rw [h, ZFSet.coe_insert, ZFSet.coe_singleton] at hinf
  exact hinf (Set.finite_singleton _ |>.insert _)

/-- Equality of realized sets recovers the complete formal object term. -/
theorem realize_injective : Function.Injective realize := by
  intro X
  induction X with
  | omega =>
    rintro (_ | ⟨A, B⟩ | ⟨A, B⟩) he
    · rfl
    · exact (omega_ne_product _ _ he).elim
    · exact (omega_ne_taggedUnion _ _ he).elim
  | product X Y hX hY =>
    rintro (_ | ⟨A, B⟩ | ⟨A, B⟩) he
    · exact (omega_ne_product _ _ he.symm).elim
    · have h₁ := congrArg firstProjection he
      have h₂ := congrArg secondProjection he
      rw [realize, realize, firstProjection_product _ _ (infinite_realize Y).nonempty,
        firstProjection_product _ _ (infinite_realize B).nonempty] at h₁
      rw [realize, realize, secondProjection_product _ _ (infinite_realize X).nonempty,
        secondProjection_product _ _ (infinite_realize A).nonempty] at h₂
      rw [hX h₁, hY h₂]
    · exact (product_ne_taggedUnion X Y A B he).elim
  | coproduct X Y hX hY =>
    rintro (_ | ⟨A, B⟩ | ⟨A, B⟩) he
    · exact (omega_ne_taggedUnion _ _ he.symm).elim
    · exact (product_ne_taggedUnion A B X Y he.symm).elim
    · obtain ⟨hl, hr⟩ := taggedUnion_injective he
      rw [hX hl, hY hr]

/-- The realized sets form the least family containing `ω` and closed under the two operations. -/
theorem mem_range_realize_iff (A : ZFSet.{0}) : A ∈ Set.range realize ↔
    ∀ S : Set ZFSet.{0}, ZFSet.omega ∈ S →
      (∀ B ∈ S, ∀ C ∈ S, B.prod C ∈ S) → (∀ B ∈ S, ∀ C ∈ S, taggedUnion B C ∈ S) → A ∈ S := by
  constructor
  · rintro ⟨X, rfl⟩ S hω hp hs
    induction X with
    | omega => exact hω
    | product X Y hX hY => exact hp _ hX _ hY
    | coproduct X Y hX hY => exact hs _ hX _ hY
  · intro h
    apply h (Set.range realize) ⟨.omega, rfl⟩
    · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
      exact ⟨.product X Y, rfl⟩
    · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
      exact ⟨.coproduct X Y, rfl⟩

/-- Every set in the generated family determines its unique object term. -/
def objectEquiv : STObjectCode ≃ Set.range realize :=
  Equiv.ofInjective realize realize_injective

/-- The realized set as a member of the generated family. -/
abbrev objectSet (X : STObjectCode) : Set.range realize := ⟨realize X, ⟨X, rfl⟩⟩

theorem unique_term (A : Set.range realize) : ∃! X, realize X = A.val := by
  obtain ⟨X, hX⟩ := A.property
  exact ⟨X, hX, fun Y hY => realize_injective (hY.trans hX.symm)⟩

/-- Transport the recursive coding along an equality of sets. -/
def codingOfRealization {A : ZFSet.{0}} (X : STObjectCode) (h : realize X = A) : ↥A ≃ ℕ :=
  (Equiv.cast (congrArg (fun Z : ZFSet.{0} => ↥Z) h.symm)).trans (coding X)

theorem codingOfRealization_unique {A : ZFSet.{0}} {X Y : STObjectCode}
    (hX : realize X = A) (hY : realize Y = A) :
    codingOfRealization X hX = codingOfRealization Y hY := by
  obtain rfl := realize_injective (hX.trans hY.symm)
  rfl

/-- The numerical coding determined by a generated set. -/
def setCoding (A : Set.range realize) : ↥A.val ≃ ℕ :=
  codingOfRealization (objectEquiv.symm A) (Equiv.apply_ofInjective_symm realize_injective A)

theorem setCoding_realize (X : STObjectCode) : setCoding (objectSet X) = coding X :=
  codingOfRealization_unique _ rfl

theorem unique_coding (A : Set.range realize) :
    ∃! γ : ↥A.val ≃ ℕ, ∃ (X : STObjectCode) (h : realize X = A.val),
      γ = codingOfRealization X h := by
  refine ⟨setCoding A, ⟨objectEquiv.symm A, Equiv.apply_ofInjective_symm realize_injective A,
    rfl⟩, ?_⟩
  rintro γ ⟨X, hX, rfl⟩
  exact codingOfRealization_unique hX _

end CategoricalEssentialIncompleteness.V46.RealizedObjectSets
