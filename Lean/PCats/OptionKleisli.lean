/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Coproducts
public import PCats.NCoproducts
public import PCats.Recursion

/-!
# The Kleisli category of `Option`

Objects are types and morphisms are `X → Option Y`, with composition
`fun x => (f x).bind g` and identity `some`; this is the Kleisli category of the
`Option` monad. Because `f x = none` is a decidable test, these are the partial
functions with decidable domain.

This is not the category `Pfn` of sets and partial functions of Appendix A and
of Di Paola--Heller, whose morphisms have arbitrary domains, and the name `Pfn`
is left free for it. The two are equivalent classically but not constructively:
Mathlib's `PartialFun` uses `PFun`, which is `Part`-valued, and its
documentation gives this difference as the reason its equivalence with pointed
types is nonconstructive. `Option` is used here because every axiom then reduces
to a case split with no library lemmas involved.

The near product is the Cartesian product of types, which is not a categorical
product here: `p₀ (f ⊠ g)` is undefined wherever `g` is, so it differs from
`f p₀`. That failure is what `p0_nat_of_isTotal` repairs by assuming `g` total.
The disjoint union satisfies the coproduct universal property without a
totality hypothesis, as expressed by `existsUnique_copair`.

Each instance field is proved by splitting on the `Option` values of the
morphisms at the relevant arguments. For a split to substitute anything, the
goal must first be beta-reduced and the instance projections unfolded; the
`@[simp]` application lemmas between the two instance declarations do the
latter.
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Types and partial functions with decidable domain: the Kleisli category of
`Option`. -/
def OptionKleisli : Type (u + 1) := Type u

namespace OptionKleisli

instance : CoeSort OptionKleisli (Type u) := ⟨id⟩

/-- Regard a type as an object. Reducible, so that `nearProd X Y` and `X × Y`
are interchangeable at the transparency `simp` uses. -/
abbrev of (X : Type u) : OptionKleisli := X

instance largeCategory : LargeCategory.{u} OptionKleisli where
  Hom X Y := X → Option Y
  id _ := fun x => some x
  comp f g := fun x => (f x).bind g
  id_comp _ := rfl
  comp_id f := by funext x; cases f x <;> rfl
  assoc f _ _ := by funext x; dsimp only; cases f x <;> rfl

@[simp] lemma id_apply {X : OptionKleisli} (x : X) : (𝟙 X) x = some x := rfl

@[simp] lemma comp_apply {X Y Z : OptionKleisli} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = (f x).bind g := rfl

instance instPCategoryStruct : PCategoryStruct OptionKleisli.{u} where
  nearProd X Y := of (X × Y)
  nearProd_map f g := fun p => (f p.1).bind fun a => (g p.2).map fun b => (a, b)
  diag _ := fun x => some (x, x)
  p0 _ _ := fun p => some p.1
  p1 _ _ := fun p => some p.2

open PCategoryStruct

@[simp] lemma nearProd_map_apply {W X Y Z : OptionKleisli} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : W × Y) :
    nearProd_map f g p = (f p.1).bind fun a => (g p.2).map fun b => (a, b) := rfl

@[simp] lemma diag_apply {X : OptionKleisli} (x : X) : diag X x = some (x, x) := rfl

@[simp] lemma p0_apply {X Y : OptionKleisli} (p : X × Y) : p0 X Y p = some p.1 := rfl

@[simp] lemma p1_apply {X Y : OptionKleisli} (p : X × Y) : p1 X Y p = some p.2 := rfl

-- `Option.bind` and `Option.map` are unfolded explicitly: `simp` does not
-- reduce either on `some` on its own.
attribute [local simp] Option.bind Option.map

instance : PCategory OptionKleisli.{u} where
  nearProd_id _ _ := by funext p; obtain ⟨x, y⟩ := p; rfl
  nearProd_comp f g h k := by
    -- The `some a`/`none` branch leaves `(g a).bind (fun _ => none)`, whose
    -- head is not a constructor, so it needs its own split on `g a`.
    funext p; obtain ⟨u, v⟩ := p
    cases hf : f u with
    | none => simp [hf]
    | some a =>
      cases hh : h v with
      | none => cases hg : g a <;> simp [hf, hh, hg]
      | some b => simp [hf, hh]
  diag_p0 _ := by funext x; rfl
  diag_p1 _ := by funext x; rfl
  diag_p0_p1 _ _ := by funext p; obtain ⟨x, y⟩ := p; rfl
  p0_p0 _ _ _ := by funext p; obtain ⟨x, y, z⟩ := p; rfl
  p0_p1 _ _ _ := by funext p; obtain ⟨x, y, z⟩ := p; rfl
  p1_p0 _ _ _ := by funext p; obtain ⟨⟨x, y⟩, z⟩ := p; rfl
  p1_p1 _ _ _ := by funext p; obtain ⟨⟨x, y⟩, z⟩ := p; rfl
  diag_nat f := by funext x; cases hf : f x <;> simp [hf]
  p0_nat f := by funext p; obtain ⟨x, z⟩ := p; cases hf : f x <;> simp [hf]
  p1_nat f := by funext p; obtain ⟨z, x⟩ := p; cases hf : f x <;> simp [hf]
  assoc_nat f g h := by
    funext p; obtain ⟨⟨x, y⟩, z⟩ := p
    cases hf : f x <;> cases hg : g y <;> cases hh : h z <;>
      simp [assoc, partialPairing, hf, hg, hh]
  swap_nat f g := by
    funext p; obtain ⟨x, y⟩ := p
    cases hf : f x <;> cases hg : g y <;> simp [swap, partialPairing, hf, hg]

/-- The restriction of `f` is the partial identity on the domain of `f`. -/
lemma rst_apply {X Y : OptionKleisli} (f : X ⟶ Y) (x : X) :
    rst f x = (f x).map fun _ => x := by
  cases hf : f x <;> simp [rst, hf]

/-- A morphism is total exactly when it is everywhere defined. -/
lemma isTotal_iff {X Y : OptionKleisli} (f : X ⟶ Y) :
    rst f = 𝟙 X ↔ ∀ x : X, (f x).isSome := by
  constructor
  · intro h x
    have hx := congrFun h x
    rw [rst_apply, id_apply] at hx
    cases hf : f x with
    | none => rw [hf] at hx; simp at hx
    | some b => rfl
  · intro h
    funext x
    rw [rst_apply, id_apply]
    cases hf : f x with
    | none =>
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x)
      rw [hf] at hb
      cases hb
    | some b => rfl

/-! ### Coproducts

The disjoint union of types. Every field is a case split on `Sum`, with a
further split on an `Option` value only where a morphism is applied. -/

instance : CoprodStruct OptionKleisli.{u} where
  coprod X Y := of (X ⊕ Y)
  coprod_map f g := fun s =>
    match s with
    | .inl x => (f x).map Sum.inl
    | .inr y => (g y).map Sum.inr
  codiag _ := fun s => some (Sum.elim id id s)
  i0 _ _ := fun x => some (Sum.inl x)
  i1 _ _ := fun y => some (Sum.inr y)

open CoprodStruct

@[simp] lemma coprod_map_inl {W X Y Z : OptionKleisli} (f : W ⟶ X) (g : Y ⟶ Z)
    (x : W) : coprod_map f g (Sum.inl x) = (f x).map Sum.inl := rfl

@[simp] lemma coprod_map_inr {W X Y Z : OptionKleisli} (f : W ⟶ X) (g : Y ⟶ Z)
    (y : Y) : coprod_map f g (Sum.inr y) = (g y).map Sum.inr := rfl

@[simp] lemma codiag_inl {X : OptionKleisli} (x : X) :
    codiag X (Sum.inl x) = some x := rfl

@[simp] lemma codiag_inr {X : OptionKleisli} (x : X) :
    codiag X (Sum.inr x) = some x := rfl

@[simp] lemma i0_apply {X Y : OptionKleisli} (x : X) :
    i0 X Y x = some (Sum.inl x) := rfl

@[simp] lemma i1_apply {X Y : OptionKleisli} (y : Y) :
    i1 X Y y = some (Sum.inr y) := rfl

instance : HasCoproducts OptionKleisli.{u} where
  coprod_id _ _ := by funext s; cases s <;> rfl
  coprod_comp f g h k := by
    funext s
    cases s with
    | inl x => cases hf : f x <;> simp [hf]
    | inr y => cases hh : h y <;> simp [hh]
  i0_codiag _ := by funext x; rfl
  i1_codiag _ := by funext x; rfl
  i0_i1_codiag _ _ := by funext s; cases s <;> rfl
  codiag_nat f := by
    funext s
    cases s with
    | inl x => cases hf : f x <;> simp [hf]
    | inr y => cases hf : f y <;> simp [hf]
  i0_nat f := by funext x; cases hf : f x <;> simp [hf]
  i0_nat_right g := by funext x; rfl
  i1_nat f := by funext y; cases hf : f y <;> simp [hf]
  i1_nat_left f := by funext y; rfl

/-! ### Distributivity

Both comparison morphisms are total and bijective on the underlying types, so
each has a total inverse and `IsIso` holds. Every equation is a case split on
`Sum` followed by `rfl`: no morphism is applied, so no `Option` value is opened.

`OptionKleisli` is therefore a model of `Distributive`. It is not a model of
`HasRanges`: `ran f` would be the partial identity on the image of `f`, whose
domain is not decidable, so `X → Option Y` cannot express it without excluded
middle. -/

@[simp] lemma distribLeft_inl (W U V : OptionKleisli) (w : W) (u : U) :
    distribLeft W U V (Sum.inl (w, u)) = some (w, Sum.inl u) := rfl

@[simp] lemma distribLeft_inr (W U V : OptionKleisli) (w : W) (v : V) :
    distribLeft W U V (Sum.inr (w, v)) = some (w, Sum.inr v) := rfl

@[simp] lemma distribRight_inl (U V W : OptionKleisli) (u : U) (w : W) :
    distribRight U V W (Sum.inl (u, w)) = some (Sum.inl u, w) := rfl

@[simp] lemma distribRight_inr (U V W : OptionKleisli) (v : V) (w : W) :
    distribRight U V W (Sum.inr (v, w)) = some (Sum.inr v, w) := rfl

/-- The inverse of `distribLeft`. -/
def distribLeftInv (W U V : OptionKleisli) :
    nearProd W (coprod U V) ⟶ coprod (nearProd W U) (nearProd W V) :=
  fun p =>
    match p.2 with
    | .inl u => some (Sum.inl (p.1, u))
    | .inr v => some (Sum.inr (p.1, v))

/-- The inverse of `distribRight`. -/
def distribRightInv (U V W : OptionKleisli) :
    nearProd (coprod U V) W ⟶ coprod (nearProd U W) (nearProd V W) :=
  fun p =>
    match p.1 with
    | .inl u => some (Sum.inl (u, p.2))
    | .inr v => some (Sum.inr (v, p.2))

instance : Distributive OptionKleisli.{u} where
  isIso_distribLeft W U V :=
    ⟨⟨distribLeftInv W U V,
      by funext s
         cases s with
         | inl a => obtain ⟨w, u⟩ := a; rfl
         | inr b => obtain ⟨w, v⟩ := b; rfl,
      by funext p
         obtain ⟨w, s⟩ := p
         cases s <;> rfl⟩⟩
  isIso_distribRight U V W :=
    ⟨⟨distribRightInv U V W,
      by funext s
         cases s with
         | inl a => obtain ⟨u, w⟩ := a; rfl
         | inr b => obtain ⟨v, w⟩ := b; rfl,
      by funext p
         obtain ⟨s, w⟩ := p
         cases s <;> rfl⟩⟩

/-! ### Zero morphisms

The nowhere-defined partial function. `OptionKleisli` is prodominical: the near
product of anything with the zero morphism is zero, because the pair is defined
only where both components are.

It is not an isotype, so it is not a model of `PRecursionCategory`. `Empty` and
`Unit` are not isomorphic here: the only morphism `Unit ⟶ Empty` is zero, and
composing it with any `Empty ⟶ Unit` gives zero rather than the identity. -/

instance zeroHom (X Y : OptionKleisli) : Zero (X ⟶ Y) := ⟨fun _ => none⟩

@[simp] lemma zero_apply {X Y : OptionKleisli} (x : X) :
    (0 : X ⟶ Y) x = none := rfl

lemma comp_zero' {X Y Z : OptionKleisli} (f : X ⟶ Y) :
    f ≫ (0 : Y ⟶ Z) = 0 := by
  funext x; cases hf : f x <;> simp [hf]

lemma zero_comp' {X Y Z : OptionKleisli} (f : Y ⟶ Z) :
    (0 : X ⟶ Y) ≫ f = 0 := by
  funext x; rfl

-- The binder arrangement of `comp_zero` and `zero_comp` differs between Mathlib
-- versions, so the fields are discharged after `intros` rather than by naming
-- their arguments positionally.
instance : Limits.HasZeroMorphisms OptionKleisli.{u} where
  zero := zeroHom
  comp_zero := by intros; exact comp_zero' _
  zero_comp := by intros; exact zero_comp' _

instance : RecursionCategory.Prodominical OptionKleisli.{u} where
  nearProd_zero_right {A} {B} {X} {Y} f := by
    funext p
    obtain ⟨x, y⟩ := p
    change (f x).bind (fun a => ((0 : X ⟶ Y) y).map fun b => (a, b)) = none
    rw [zero_apply]
    cases f x <;> rfl
  nearProd_zero_left f := by
    funext p; obtain ⟨x, y⟩ := p; rfl

/-! ### Countable coproducts

The dependent sum `Σ n, Uₙ`. Everything is a case split on `Sigma`, with a
further split on an `Option` value only where a morphism is applied, exactly as
for the binary coproduct.

The dependent sum supplies `NCoprodStruct`, `HasNCoproducts`, and
`CountablyDistributive` instances. The manuscript's `rPΣ`-structure also
requires ranges and `IsRP`; the corresponding constructions for
`OptionKleisli` use classical logic. -/

instance : NCoprodStruct OptionKleisli.{u} where
  ncoprod U := of (Σ n : ℕ, U n)
  ncoprod_map f := fun p => (f p.1 p.2).map (Sigma.mk p.1)
  ncodiag _ := fun p => some p.2
  ninj _ n := fun x => some (Sigma.mk n x)

open NCoprodStruct

@[simp] lemma ninj_apply {U : ℕ → OptionKleisli} (n : ℕ) (x : U n) :
    ninj U n x = some (Sigma.mk n x) := rfl

@[simp] lemma ncoprod_map_apply {U V : ℕ → OptionKleisli}
    (f : ∀ n, U n ⟶ V n) (p : Σ n : ℕ, U n) :
    ncoprod_map f p = (f p.1 p.2).map (Sigma.mk p.1) := rfl

@[simp] lemma ncodiag_apply {X : OptionKleisli}
    (p : Σ _ : ℕ, X) :
    ncodiag X p = some p.2 := rfl

instance : HasNCoproducts OptionKleisli.{u} where
  ncoprod_id _ := by funext p; obtain ⟨n, x⟩ := p; rfl
  ncoprod_comp f g := by
    funext p; obtain ⟨n, x⟩ := p
    -- `f n x` sits under unreduced instance projections, so a bare `cases`
    -- substitutes nothing; `change` to the definitional unfolding first, then
    -- every branch is `rfl`.
    change ((f n x).map (Sigma.mk n)).bind _ = ((f n x).bind (g n)).map (Sigma.mk n)
    cases f n x <;> rfl
  ninj_ncodiag _ _ := by funext x; rfl
  ncoprod_ninj_ncodiag _ := by funext p; obtain ⟨n, x⟩ := p; rfl
  ninj_nat f n := by
    funext x
    change (f n x).bind _ = (f n x).map (Sigma.mk n)
    cases f n x <;> rfl
  ncodiag_nat {X Y} f := by
    funext p
    obtain ⟨n, x⟩ := p
    change
      ((f x).map
          (fun y : Y => (⟨n, y⟩ : Σ _ : ℕ, Y))).bind
        (fun q => some q.2)
        = f x
    cases f x <;> rfl

/-- `δ^L : W ⊠ (∐ Uₙ) ⟶ ∐ (W ⊠ Uₙ)`. -/
def ndistribL (W : OptionKleisli) (U : ℕ → OptionKleisli) :
    nearProd W (ncoprod U) ⟶ ncoprod fun n => nearProd W (U n) :=
  fun p => some (Sigma.mk p.2.1 (Prod.mk p.1 p.2.2))

/-- Its inverse. -/
def ndistribLInv (W : OptionKleisli) (U : ℕ → OptionKleisli) :
    (ncoprod fun n => nearProd W (U n)) ⟶ nearProd W (ncoprod U) :=
  fun p => some (Prod.mk p.2.1 (Sigma.mk p.1 p.2.2))

/-- `δ^R : (∐ Uₙ) ⊠ W ⟶ ∐ (Uₙ ⊠ W)`. -/
def ndistribR (U : ℕ → OptionKleisli) (W : OptionKleisli) :
    nearProd (ncoprod U) W ⟶ ncoprod fun n => nearProd (U n) W :=
  fun p => some (Sigma.mk p.1.1 (Prod.mk p.1.2 p.2))

/-- Its inverse. -/
def ndistribRInv (U : ℕ → OptionKleisli) (W : OptionKleisli) :
    (ncoprod fun n => nearProd (U n) W) ⟶ nearProd (ncoprod U) W :=
  fun p => some (Prod.mk (Sigma.mk p.1 p.2.1) p.2.2)

instance : CountablyDistributive OptionKleisli.{u} where
  distribL := ndistribL
  distribR := ndistribR
  isIso_distribL W U :=
    ⟨⟨ndistribLInv W U,
      by funext p; obtain ⟨w, n, x⟩ := p; rfl,
      by funext p; obtain ⟨n, w, x⟩ := p; rfl⟩⟩
  isIso_distribR U W :=
    ⟨⟨ndistribRInv U W,
      by funext p; obtain ⟨⟨n, x⟩, w⟩ := p; rfl,
      by funext p; obtain ⟨n, x, w⟩ := p; rfl⟩⟩
  distribL_ninj _ _ _ := by funext p; obtain ⟨w, x⟩ := p; rfl
  distribR_ninj _ _ _ := by funext p; obtain ⟨x, w⟩ := p; rfl

end OptionKleisli

end CategoryTheory
