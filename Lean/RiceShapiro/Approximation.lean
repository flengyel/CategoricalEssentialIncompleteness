/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats

/-!
# Approximation data and extension spans

Section "Approximation data and extension spans" of *Countable Extension
Families and a Quotient-Fibration Form of the Rice–Shapiro Theorem*.

Composition is diagrammatic, as in `PCats`: the manuscript's `ε(i ⊠ 1_X)` is
`nearProd_map i (𝟙 X) ≫ ev`, and its `α_a = ε_i \rst{α_a}` is
`evalAt approx a = rst (evalAt approx a) ≫ evalAt ev i`.

The Lean statements use weaker hypotheses in two places.

* `extends_comp` does not require the reindexing morphism to be total. Totality
  is needed only when the composites are to remain index families.
* `gen_receives_index` requires totality of the approximation morphism `a`, but
  not of the index morphism `i`.

The generated-domain proofs use `HasRanges.ran_le_of_receives`, the
range-minimality lemma from `PCats.Ranges`.

Stable countable unions are in `PCats.Unions` and `PCats.CountableUnions`,
countable distributivity in `PCats.NCoproducts`, and countable extension
families in `RiceShapiro.ExtensionFamilies`.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- `ε_i = ε(i ⊠ 1_X)`, the morphism indexed by `i`. Serves for both the
evaluator and the approximation morphism of an approximation datum. -/
def evalAt {I X Y : C} (ev : nearProd I X ⟶ Y) {Z : C} (i : Z ⟶ I) :
    nearProd Z X ⟶ Y :=
  nearProd_map i (𝟙 X) ≫ ev

/-- `ε_{wi} = ε_i(w ⊠ 1_X)`: reindexing an indexed morphism. -/
lemma evalAt_comp {I X Y W Z : C} (ev : nearProd I X ⟶ Y) (w : W ⟶ Z)
    (i : Z ⟶ I) :
    evalAt ev (w ≫ i) = nearProd_map w (𝟙 X) ≫ evalAt ev i := by
  dsimp only [evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id]

/-- An approximation datum `(I, A, ε, α, e)` for indexed morphisms `X ⟶ Y`. -/
structure ApproximationDatum (X Y : C) where
  /-- The object of indices. -/
  I : C
  /-- The object of approximation parameters. -/
  A : C
  /-- The evaluator. -/
  ev : nearProd I X ⟶ Y
  /-- The approximation morphism. -/
  approx : nearProd A X ⟶ Y
  /-- The extension domain `e ∈ Dom(A ⊠ I)`. -/
  ext : DomSemilattice (nearProd A I)
  /-- Compatibility: `a ≼ i` exactly when `ε_i` extends `α_a`. -/
  compat : ∀ {Z : C} (a : Z ⟶ A) (i : Z ⟶ I), rst a = 𝟙 Z → rst i = 𝟙 Z →
    (partialPairing a i ≫ ext.hom = partialPairing a i
      ↔ evalAt approx a = rst (evalAt approx a) ≫ evalAt ev i)

namespace ApproximationDatum

variable {X Y : C} (𝒜 : ApproximationDatum X Y)

/-- `a ≼_Z i`: the extension domain receives `⟨a, i⟩`. When it holds, `a` is an
extension witness for `i`. -/
def Extends {Z : C} (a : Z ⟶ 𝒜.A) (i : Z ⟶ 𝒜.I) : Prop :=
  partialPairing a i ≫ 𝒜.ext.hom = partialPairing a i

/-- Reindexing of extension witnesses. No totality hypothesis is needed. -/
lemma extends_comp {W Z : C} (h : W ⟶ Z) {a : Z ⟶ 𝒜.A} {i : Z ⟶ 𝒜.I}
    (ha : 𝒜.Extends a i) : 𝒜.Extends (h ≫ a) (h ≫ i) := by
  dsimp [Extends] at ha ⊢
  rw [← comp_partialPairing, Category.assoc, ha]

omit [PCategory C] in
/-- Extension invariance: `≼` depends on `i` only through `ε_i`. -/
lemma extends_congr {Z : C} {a : Z ⟶ 𝒜.A} {i j : Z ⟶ 𝒜.I}
    (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hj : rst j = 𝟙 Z)
    (h : evalAt 𝒜.ev i = evalAt 𝒜.ev j) :
    𝒜.Extends a i ↔ 𝒜.Extends a j := by
  rw [Extends, Extends, 𝒜.compat a i ha hi, 𝒜.compat a j ha hj, h]

end ApproximationDatum

/-- A domain `s ∈ Dom(I)` is extensional for `ε` when membership in `s` depends
on an index only through the morphism it indexes. -/
def Extensional {I X Y : C} (ev : nearProd I X ⟶ Y) (s : DomSemilattice I) : Prop :=
  ∀ {Z : C} (i j : Z ⟶ I), rst i = 𝟙 Z → rst j = 𝟙 Z →
    evalAt ev i = evalAt ev j → (i ≫ s.hom = i ↔ j ≫ s.hom = j)

namespace ApproximationDatum

variable {X Y : C} [HasRanges C] (𝒜 : ApproximationDatum X Y)

/-- The morphism whose range is the generated domain:
`p₁ (e ∧ (b ⊠ 1_I))`, written in the manuscript's order as `p₁ e (b ⊠ 1_I)`.
The two agree because `e` and `b ⊠ 1` are domains and so commute, but the order
here is the one the factorization in `gen_mono` needs. -/
def genHom (b : DomSemilattice 𝒜.A) : nearProd 𝒜.A 𝒜.I ⟶ 𝒜.I :=
  nearProd_map b.hom (𝟙 𝒜.I) ≫ 𝒜.ext.hom ≫ p1 𝒜.A 𝒜.I

/-- The generated domain `υ(b) = ran (p₁ (e ∧ (b ⊠ 1_I)))`. -/
def gen (b : DomSemilattice 𝒜.A) : DomSemilattice 𝒜.I :=
  ⟨HasRanges.ran (𝒜.genHom b), HasRanges.rst_ran _⟩

@[simp] lemma gen_hom (b : DomSemilattice 𝒜.A) :
    (𝒜.gen b).hom = HasRanges.ran (𝒜.genHom b) := rfl

/-- Property (i): `υ(b)` receives the morphism it is the range of. -/
lemma gen_receives (b : DomSemilattice 𝒜.A) :
    𝒜.genHom b ≫ (𝒜.gen b).hom = 𝒜.genHom b :=
  HasRanges.comp_ran _

/-- Property (ii): `υ` is monotone. -/
lemma gen_mono {b c : DomSemilattice 𝒜.A} (h : b ≤ c) : 𝒜.gen b ≤ 𝒜.gen c := by
  have h' : b.hom ≫ c.hom = b.hom := h
  have hbc : nearProd_map b.hom (𝟙 𝒜.I) ≫ nearProd_map c.hom (𝟙 𝒜.I)
      = nearProd_map b.hom (𝟙 𝒜.I) := by
    rw [nearProd_comp, h', Category.comp_id]
  have hfac : nearProd_map b.hom (𝟙 𝒜.I) ≫ 𝒜.genHom c = 𝒜.genHom b := by
    dsimp [genHom]
    rw [← Category.assoc, hbc]
  have hd : 𝒜.genHom b ≫ (𝒜.gen c).hom = 𝒜.genHom b := by
    rw [← hfac, Category.assoc, gen_hom, HasRanges.comp_ran]
  change HasRanges.ran (𝒜.genHom b) ≫ (𝒜.gen c).hom = HasRanges.ran (𝒜.genHom b)
  exact HasRanges.ran_le_of_receives _ hd

/-- Property (iii): an extension witness in `b` puts its index in `υ(b)`. -/
lemma gen_receives_index {Z : C} {b : DomSemilattice 𝒜.A} {a : Z ⟶ 𝒜.A} {i : Z ⟶ 𝒜.I}
    (ha : rst a = 𝟙 Z) (hab : a ≫ b.hom = a) (hai : 𝒜.Extends a i) :
    i ≫ (𝒜.gen b).hom = i := by
  have hai' : partialPairing a i ≫ 𝒜.ext.hom = partialPairing a i := hai
  have hw : partialPairing a i ≫ 𝒜.genHom b = i := by
    dsimp [genHom]
    rw [← Category.assoc, partialPairing_comp_nearProd_map, hab,
      Category.comp_id, ← Category.assoc, hai', p1_partialPairing, ha,
      Category.id_comp]
  calc i ≫ (𝒜.gen b).hom
      = (partialPairing a i ≫ 𝒜.genHom b) ≫ (𝒜.gen b).hom := by rw [hw]
    _ = partialPairing a i ≫ 𝒜.genHom b ≫ HasRanges.ran (𝒜.genHom b) :=
        Category.assoc _ _ _
    _ = partialPairing a i ≫ 𝒜.genHom b := by rw [HasRanges.comp_ran]
    _ = i := hw

end ApproximationDatum

/-- An extension span for `s` relative to `𝒜`. Clause (T1) is `ran_r`, (T2) is
`ext_pair`, (T2') is `p1_pair`, and (T3) is `theta_le`. -/
structure ExtensionSpan {X Y : C} [HasRanges C] (𝒜 : ApproximationDatum X Y)
    (s : DomSemilattice 𝒜.I) where
  /-- The apex of the span. -/
  T : C
  /-- The leg into the approximation parameters. -/
  o : T ⟶ 𝒜.A
  /-- The leg into the indices. -/
  r : T ⟶ 𝒜.I
  /-- (T1) `ran r = s`. -/
  ran_r : HasRanges.ran r = s.hom
  /-- (T2) `e⟨o, r⟩ = ⟨o, r⟩`. -/
  ext_pair : partialPairing o r ≫ 𝒜.ext.hom = partialPairing o r
  /-- (T2') `p₁⟨o, r⟩ = r`. -/
  p1_pair : partialPairing o r ≫ p1 𝒜.A 𝒜.I = r
  /-- (T3) `ran θ ≤ s` for `θ = p₁ e (o ⊠ 1_I)`. -/
  theta_le :
    HasRanges.ran (nearProd_map o (𝟙 𝒜.I) ≫ 𝒜.ext.hom ≫ p1 𝒜.A 𝒜.I) ≫ s.hom
      = HasRanges.ran (nearProd_map o (𝟙 𝒜.I) ≫ 𝒜.ext.hom ≫ p1 𝒜.A 𝒜.I)

/-- `𝒜` has the extension-span property when every extensional domain admits an
extension span. -/
def HasExtensionSpanProperty {X Y : C} [HasRanges C]
    (𝒜 : ApproximationDatum X Y) : Prop :=
  ∀ s : DomSemilattice 𝒜.I, Extensional 𝒜.ev s → Nonempty (ExtensionSpan 𝒜 s)

end CategoryTheory
