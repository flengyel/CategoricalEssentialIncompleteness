/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.PCat

/-!
# `ℕ`-ary coproducts and countable distributivity

This module defines `NCoprodStruct`, `HasNCoproducts`, and
`CountablyDistributive`. It derives the countable-coproduct universal property,
the restriction and totality formulas for countable copairings, explicit
inverses to the distributivity morphisms, and their naturality.

The manuscript's `rPΣ` context additionally assumes ranges, `IsRP`, binary
coproducts, and binary distributivity. Stable countable unions of ranges are
treated in `PCats.CountableUnions`.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct

/-- The data of an `ℕ`-ary coproduct. -/
class NCoprodStruct (C : Type u) [Category.{v} C] where
  ncoprod (U : ℕ → C) : C
  ncoprod_map {U V : ℕ → C} (f : ∀ n, U n ⟶ V n) : ncoprod U ⟶ ncoprod V
  ncodiag (X : C) : ncoprod (fun _ => X) ⟶ X
  ninj (U : ℕ → C) (n : ℕ) : U n ⟶ ncoprod U

namespace NCoprodStruct

variable {C : Type u} [Category.{v} C] [NCoprodStruct C]

/-- Countable copairing `[qₙ] = ∇ (∐ qₙ)`. -/
def ncopair {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) : ncoprod U ⟶ Q :=
  ncoprod_map q ≫ ncodiag Q

end NCoprodStruct

open NCoprodStruct in
/-- The axioms for an `ℕ`-ary coproduct. -/
class HasNCoproducts (C : Type u) [Category.{v} C] [NCoprodStruct C] : Prop where
  /-- Functoriality. -/
  ncoprod_id : ∀ (U : ℕ → C), ncoprod_map (fun n => 𝟙 (U n)) = 𝟙 (ncoprod U)
  ncoprod_comp : ∀ {U V W : ℕ → C} (f : ∀ n, U n ⟶ V n) (g : ∀ n, V n ⟶ W n),
    ncoprod_map f ≫ ncoprod_map g = ncoprod_map fun n => f n ≫ g n
  /-- `∇ ιₙ = 1`. -/
  ninj_ncodiag : ∀ (X : C) (n : ℕ), ninj (fun _ => X) n ≫ ncodiag X = 𝟙 X
  /-- `∇ (∐ ιₙ) = 1`. -/
  ncoprod_ninj_ncodiag : ∀ (U : ℕ → C),
    ncoprod_map (ninj U) ≫ ncodiag (ncoprod U) = 𝟙 (ncoprod U)
  /-- The injections are natural in the whole family at once. -/
  ninj_nat : ∀ {U V : ℕ → C} (f : ∀ n, U n ⟶ V n) (n : ℕ),
    f n ≫ ninj V n = ninj U n ≫ ncoprod_map f
  /-- The codiagonal is natural. -/
  ncodiag_nat : ∀ {X Y : C} (f : X ⟶ Y),
    ncoprod_map (fun _ => f) ≫ ncodiag Y = ncodiag X ≫ f

namespace HasNCoproducts

open NCoprodStruct

variable {C : Type u} [Category.{v} C] [NCoprodStruct C] [HasNCoproducts C]

/-- `[qₙ] ιₘ = qₘ`. -/
lemma ninj_ncopair {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) (n : ℕ) :
    ninj U n ≫ ncopair q = q n := by
  dsimp [ncopair]
  rw [← Category.assoc, ← ninj_nat, Category.assoc, ninj_ncodiag,
    Category.comp_id]

/-- The eta rule `[ιₙ h] = h`, dual to `partialPairing_proj` and with no
totality hypothesis. -/
lemma ncopair_ninj {U : ℕ → C} {Q : C} (h : ncoprod U ⟶ Q) :
    ncopair (fun n => ninj U n ≫ h) = h := by
  dsimp [ncopair]
  rw [← ncoprod_comp, Category.assoc, ncodiag_nat, ← Category.assoc,
    ncoprod_ninj_ncodiag, Category.id_comp]

/-- Two morphisms out of a countable coproduct agreeing after every injection
are equal. -/
lemma hom_ext {U : ℕ → C} {Q : C} {h h' : ncoprod U ⟶ Q}
    (hn : ∀ n, ninj U n ≫ h = ninj U n ≫ h') : h = h' := by
  rw [← ncopair_ninj h, ← ncopair_ninj h']
  exact congrArg ncopair (funext hn)

lemma eq_ncopair_of_ninj {U : ℕ → C} {Q : C} {h : ncoprod U ⟶ Q}
    {q : ∀ n, U n ⟶ Q} (hq : ∀ n, ninj U n ≫ h = q n) :
    h = ncopair q := by
  rw [← ncopair_ninj h]
  exact congrArg ncopair (funext hq)

/-- `ncoprod` is a categorical coproduct. -/
theorem existsUnique_ncopair {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    ∃! h : ncoprod U ⟶ Q, ∀ n, ninj U n ≫ h = q n := by
  refine ⟨ncopair q, ninj_ncopair q, ?_⟩
  intro h hh
  exact eq_ncopair_of_ninj hh

/-- `[qₙ] k = [qₙ k]`. -/
lemma ncopair_comp {U : ℕ → C} {Q R : C} (q : ∀ n, U n ⟶ Q) (k : Q ⟶ R) :
    ncopair q ≫ k = ncopair fun n => q n ≫ k := by
  dsimp [ncopair]
  rw [Category.assoc, ← ncodiag_nat, ← Category.assoc, ncoprod_comp]

/-! ### Restriction of a countable copairing -/

section Restriction

variable [PCategoryStruct C] [PCategory C]

/-- `rst [qₙ] = ∐ rst qₙ`. Both sides are compared after every injection: on
the left by R4 and `ninj_ncopair`, on the right by `ninj_nat`. -/
lemma rst_ncopair {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    rst (ncopair q) = ncoprod_map fun n => rst (q n) := by
  apply hom_ext
  intro n
  rw [← ninj_nat]
  have h := PCategory.rst_comp' (ninj U n) (ncopair q)
  rw [ninj_ncopair] at h
  exact h.symm

/-- A countable copairing of total morphisms is total. Heller's proposition;
no separate assumption that the injections are total is needed. -/
lemma isTotal_ncopair {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q)
    (hq : ∀ n, rst (q n) = 𝟙 (U n)) : rst (ncopair q) = 𝟙 (ncoprod U) := by
  rw [rst_ncopair]
  have hfun : (fun n => rst (q n)) = fun n => 𝟙 (U n) := funext hq
  rw [hfun, ncoprod_id]

end Restriction

end HasNCoproducts

open NCoprodStruct in
/-- The countable distributivity morphisms `δ^L` and `δ^R`, their
invertibility, and their values on the coproduct injections.

The full `rPΣ` context additionally assumes ranges, `IsRP`, binary coproducts,
and binary distributivity. -/
class CountablyDistributive (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [NCoprodStruct C] [HasNCoproducts C] where
  /-- `δ^L : W ⊠ (∐ Uₙ) ⟶ ∐ (W ⊠ Uₙ)`. -/
  distribL (W : C) (U : ℕ → C) :
    nearProd W (ncoprod U) ⟶ ncoprod fun n => nearProd W (U n)
  /-- `δ^R : (∐ Uₙ) ⊠ W ⟶ ∐ (Uₙ ⊠ W)`. -/
  distribR (U : ℕ → C) (W : C) :
    nearProd (ncoprod U) W ⟶ ncoprod fun n => nearProd (U n) W
  isIso_distribL : ∀ (W : C) (U : ℕ → C), IsIso (distribL W U)
  isIso_distribR : ∀ (U : ℕ → C) (W : C), IsIso (distribR U W)
  /-- `δ^L (1_W ⊠ ιₙ) = λₙ`. -/
  distribL_ninj : ∀ (W : C) (U : ℕ → C) (n : ℕ),
    nearProd_map (𝟙 W) (ninj U n) ≫ distribL W U
      = ninj (fun m => nearProd W (U m)) n
  /-- `δ^R (ιₙ ⊠ 1_W) = κₙ`. -/
  distribR_ninj : ∀ (U : ℕ → C) (W : C) (n : ℕ),
    nearProd_map (ninj U n) (𝟙 W) ≫ distribR U W
      = ninj (fun m => nearProd (U m) W) n

attribute [instance] CountablyDistributive.isIso_distribL CountablyDistributive.isIso_distribR

namespace CountablyDistributive

open NCoprodStruct HasNCoproducts

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [NCoprodStruct C] [HasNCoproducts C] [CountablyDistributive C]

/-- The canonical map opposite to `δ^L`, defined by copairing. -/
def undistribL (W : C) (U : ℕ → C) :
    (ncoprod fun n => nearProd W (U n)) ⟶ nearProd W (ncoprod U) :=
  ncopair fun n => nearProd_map (𝟙 W) (ninj U n)

/-- The canonical map opposite to `δ^R`, defined by copairing. -/
def undistribR (U : ℕ → C) (W : C) :
    (ncoprod fun n => nearProd (U n) W) ⟶ nearProd (ncoprod U) W :=
  ncopair fun n => nearProd_map (ninj U n) (𝟙 W)

lemma undistribL_distribL (W : C) (U : ℕ → C) :
    undistribL W U ≫ distribL W U
      = 𝟙 (ncoprod fun n => nearProd W (U n)) := by
  apply hom_ext
  intro n
  rw [← Category.assoc]
  dsimp only [undistribL]
  rw [ninj_ncopair, distribL_ninj, Category.comp_id]

lemma undistribR_distribR (U : ℕ → C) (W : C) :
    undistribR U W ≫ distribR U W
      = 𝟙 (ncoprod fun n => nearProd (U n) W) := by
  apply hom_ext
  intro n
  rw [← Category.assoc]
  dsimp only [undistribR]
  rw [ninj_ncopair, distribR_ninj, Category.comp_id]

/-- The reverse inverse equation for `δ^L`. -/
lemma distribL_undistribL (W : C) (U : ℕ → C) :
    distribL W U ≫ undistribL W U = 𝟙 (nearProd W (ncoprod U)) := by
  obtain ⟨i, h1, _⟩ := (isIso_distribL W U).out
  have hu : i = undistribL W U := by
    calc i = 𝟙 _ ≫ i := (Category.id_comp _).symm
      _ = (undistribL W U ≫ distribL W U) ≫ i := by rw [undistribL_distribL]
      _ = undistribL W U ≫ distribL W U ≫ i := Category.assoc _ _ _
      _ = undistribL W U ≫ 𝟙 _ := by rw [h1]
      _ = undistribL W U := Category.comp_id _
  rw [← hu]
  exact h1

/-- The reverse inverse equation for `δ^R`. -/
lemma distribR_undistribR (U : ℕ → C) (W : C) :
    distribR U W ≫ undistribR U W = 𝟙 (nearProd (ncoprod U) W) := by
  obtain ⟨i, h1, _⟩ := (isIso_distribR U W).out
  have hu : i = undistribR U W := by
    calc i = 𝟙 _ ≫ i := (Category.id_comp _).symm
      _ = (undistribR U W ≫ distribR U W) ≫ i := by rw [undistribR_distribR]
      _ = undistribR U W ≫ distribR U W ≫ i := Category.assoc _ _ _
      _ = undistribR U W ≫ 𝟙 _ := by rw [h1]
      _ = undistribR U W := Category.comp_id _
  rw [← hu]
  exact h1

omit [CountablyDistributive C] in
lemma undistribL_nearProd (W : C) {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    undistribL W U ≫ nearProd_map (𝟙 W) (ncopair q)
      = ncopair fun n => nearProd_map (𝟙 W) (q n) := by
  apply hom_ext
  intro n
  rw [← Category.assoc]
  dsimp only [undistribL]
  rw [ninj_ncopair, ninj_ncopair, PCategory.nearProd_comp, Category.comp_id, ninj_ncopair]

omit [CountablyDistributive C] in
lemma undistribR_nearProd {U : ℕ → C} (W : C) {Q : C} (q : ∀ n, U n ⟶ Q) :
    undistribR U W ≫ nearProd_map (ncopair q) (𝟙 W)
      = ncopair fun n => nearProd_map (q n) (𝟙 W) := by
  apply hom_ext
  intro n
  rw [← Category.assoc]
  dsimp only [undistribR]
  rw [ninj_ncopair, ninj_ncopair, PCategory.nearProd_comp, Category.comp_id, ninj_ncopair]

omit [CountablyDistributive C] in
/-- Naturality of `undistribL`. -/
lemma undistribL_nat {W W' : C} {U V : ℕ → C} (f : W ⟶ W')
    (g : ∀ n, U n ⟶ V n) :
    ncoprod_map (fun n => nearProd_map f (g n)) ≫ undistribL W' V
      = undistribL W U ≫ nearProd_map f (ncoprod_map g) := by
  apply hom_ext
  intro n
  rw [← Category.assoc, ← ninj_nat, Category.assoc]
  dsimp only [undistribL]
  rw [ninj_ncopair, ← Category.assoc, ninj_ncopair, PCategory.nearProd_comp,
    PCategory.nearProd_comp, Category.comp_id, Category.id_comp, ← ninj_nat]

omit [CountablyDistributive C] in
/-- Naturality of `undistribR`. -/
lemma undistribR_nat {W W' : C} {U V : ℕ → C} (f : W ⟶ W')
    (g : ∀ n, U n ⟶ V n) :
    ncoprod_map (fun n => nearProd_map (g n) f) ≫ undistribR V W'
      = undistribR U W ≫ nearProd_map (ncoprod_map g) f := by
  apply hom_ext
  intro n
  rw [← Category.assoc, ← ninj_nat, Category.assoc]
  dsimp only [undistribR]
  rw [ninj_ncopair, ← Category.assoc, ninj_ncopair, PCategory.nearProd_comp,
    PCategory.nearProd_comp, Category.comp_id, Category.id_comp, ← ninj_nat]

/-- Precomposition with `undistribL` is cancellable; `distribL` is a section of
`undistribL`. -/
lemma cancel_undistribL {W : C} {U : ℕ → C} {R : C}
    {A B : nearProd W (ncoprod U) ⟶ R}
    (h : undistribL W U ≫ A = undistribL W U ≫ B) : A = B := by
  calc A = (distribL W U ≫ undistribL W U) ≫ A := by
        rw [distribL_undistribL, Category.id_comp]
    _ = distribL W U ≫ undistribL W U ≫ A := Category.assoc _ _ _
    _ = distribL W U ≫ undistribL W U ≫ B := by rw [h]
    _ = (distribL W U ≫ undistribL W U) ≫ B := (Category.assoc _ _ _).symm
    _ = B := by rw [distribL_undistribL, Category.id_comp]

/-- Precomposition with `undistribR` is cancellable; `distribR` is a section of
`undistribR`. -/
lemma cancel_undistribR {U : ℕ → C} {W R : C}
    {A B : nearProd (ncoprod U) W ⟶ R}
    (h : undistribR U W ≫ A = undistribR U W ≫ B) : A = B := by
  calc A = (distribR U W ≫ undistribR U W) ≫ A := by
        rw [distribR_undistribR, Category.id_comp]
    _ = distribR U W ≫ undistribR U W ≫ A := Category.assoc _ _ _
    _ = distribR U W ≫ undistribR U W ≫ B := by rw [h]
    _ = (distribR U W ≫ undistribR U W) ≫ B := (Category.assoc _ _ _).symm
    _ = B := by rw [distribR_undistribR, Category.id_comp]

/-- Naturality of `distribL`. -/
lemma distribL_nat {W W' : C} {U V : ℕ → C} (f : W ⟶ W') (g : ∀ n, U n ⟶ V n) :
    nearProd_map f (ncoprod_map g) ≫ distribL W' V
      = distribL W U ≫ ncoprod_map fun n => nearProd_map f (g n) := by
  apply cancel_undistribL
  rw [← Category.assoc, ← undistribL_nat, Category.assoc, undistribL_distribL,
    Category.comp_id, ← Category.assoc, undistribL_distribL, Category.id_comp]

/-- Naturality of `distribR`. -/
lemma distribR_nat {W W' : C} {U V : ℕ → C} (f : W ⟶ W') (g : ∀ n, U n ⟶ V n) :
    nearProd_map (ncoprod_map g) f ≫ distribR V W'
      = distribR U W ≫ ncoprod_map fun n => nearProd_map (g n) f := by
  apply cancel_undistribR
  rw [← Category.assoc, ← undistribR_nat, Category.assoc, undistribR_distribR,
    Category.comp_id, ← Category.assoc, undistribR_distribR, Category.id_comp]

/-- `1_W ⊠ [qₙ] = δ^L [1_W ⊠ qₙ]`. -/
lemma nearProd_id_ncopair (W : C) {U : ℕ → C} {Q : C} (q : ∀ n, U n ⟶ Q) :
    nearProd_map (𝟙 W) (ncopair q)
      = distribL W U ≫ ncopair fun n => nearProd_map (𝟙 W) (q n) := by
  rw [← undistribL_nearProd, ← Category.assoc, distribL_undistribL,
    Category.id_comp]

/-- `[qₙ] ⊠ 1_W = δ^R [qₙ ⊠ 1_W]`. -/
lemma nearProd_ncopair_id {U : ℕ → C} (W : C) {Q : C} (q : ∀ n, U n ⟶ Q) :
    nearProd_map (ncopair q) (𝟙 W)
      = distribR U W ≫ ncopair fun n => nearProd_map (q n) (𝟙 W) := by
  rw [← undistribR_nearProd, ← Category.assoc, distribR_undistribR,
    Category.id_comp]

end CountablyDistributive

end CategoryTheory
