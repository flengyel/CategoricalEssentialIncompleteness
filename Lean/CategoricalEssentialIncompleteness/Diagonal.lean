/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.Order.Hom.BoundedLattice

/-!
# The external diagonal argument

The two indexed lattices `E` and `P` describe restriction idempotents and
general predicates, respectively. Only specified complementary pairs are used.
Composition is diagrammatic: `f ≫ g` applies `f` first.
-/

set_option autoImplicit false

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

/-- A contravariant family of bounded distributive lattices. -/
structure PredicateLattice (A : Type u) [Category.{v} A] where
  obj : A → Type w
  lattice : ∀ X, DistribLattice (obj X)
  bounds : ∀ X, BoundedOrder (obj X)
  pull : ∀ {X Y}, (X ⟶ Y) → BoundedLatticeHom (obj Y) (obj X)
  pull_id : ∀ X (a : obj X), pull (𝟙 X) a = a
  pull_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) (a : obj Z),
    pull (f ≫ g) a = pull f (pull g a)

attribute [instance] PredicateLattice.lattice PredicateLattice.bounds

/-- An injective natural bounded lattice map. -/
structure PredicateEmbedding {A : Type u} [Category.{v} A]
    (E : PredicateLattice.{v, u, w} A) (P : PredicateLattice.{v, u, w'} A) where
  app : ∀ X, BoundedLatticeHom (E.obj X) (P.obj X)
  injective : ∀ X, Function.Injective (app X)
  naturality : ∀ {X Y} (f : X ⟶ Y) (e : E.obj Y),
    P.pull f (app Y e) = app X (E.pull f e)

/-- A pair with a specified lattice complement. -/
structure ComplementaryPair (α : Type w) [DistribLattice α] [BoundedOrder α] where
  pos : α
  neg : α
  compl : IsCompl pos neg

namespace ComplementaryPair

variable {α : Type w} {β : Type w'}
variable [DistribLattice α] [BoundedOrder α] [DistribLattice β] [BoundedOrder β]

/-- Exchange the two members of a complementary pair. -/
def swap (a : ComplementaryPair α) : ComplementaryPair α :=
  ⟨a.neg, a.pos, a.compl.symm⟩

/-- Bounded lattice maps preserve complementary pairs. -/
def map (f : BoundedLatticeHom α β) (a : ComplementaryPair α) : ComplementaryPair β :=
  ⟨f a.pos, f a.neg, IsCompl.of_eq
    (by rw [← map_inf, a.compl.inf_eq_bot, map_bot])
    (by rw [← map_sup, a.compl.sup_eq_top, map_top])⟩

/-- Componentwise inequalities between complementary pairs force equality. -/
theorem eq_of_le (a b : ComplementaryPair α)
    (hp : a.pos ≤ b.pos) (hn : a.neg ≤ b.neg) : a.pos = b.pos := by
  exact le_antisymm hp (a.compl.symm.Antitone b.compl.symm hn)

/-- Equal complementary elements collapse the two bounds. -/
theorem bot_eq_top (a : ComplementaryPair α) (h : a.pos = a.neg) :
    (⊥ : α) = ⊤ := by
  have hp : a.pos = ⊥ := by simpa [← h] using a.compl.inf_eq_bot
  have ht : a.pos = ⊤ := by simpa [← h] using a.compl.sup_eq_top
  exact hp.symm.trans ht

end ComplementaryPair

variable {A : Type u} [Category.{v} A] [HasBinaryProducts A]
variable {E : PredicateLattice.{v, u, w} A} {P : PredicateLattice.{v, u, w'} A}

/-- The external data used in representation and diagonalization. -/
structure DiagonalData (E : PredicateLattice.{v, u, w} A)
    (P : PredicateLattice.{v, u, w'} A) where
  embedding : PredicateEmbedding E P
  U : A
  S : A
  substitution : U ⨯ U ⟶ S
  positive : P.obj S
  negative : P.obj S
  disjoint : Disjoint positive negative

namespace DiagonalData

variable (D : DiagonalData E P)

/-- The substitution diagonal `s Δ`. -/
def diagonal : D.U ⟶ D.S := prod.lift (𝟙 D.U) (𝟙 D.U) ≫ D.substitution

/-- The family `s (g ⊗ 1)`. -/
def row (g : D.U ⟶ D.U) : D.U ⨯ D.U ⟶ D.S :=
  prod.map g (𝟙 D.U) ≫ D.substitution

/-- The two representation equations, with a common parameter `g`. -/
def Represents (a : ComplementaryPair (E.obj D.U)) (g : D.U ⟶ D.U) : Prop :=
  P.pull (D.row g) D.positive = P.pull prod.snd (D.embedding.app D.U a.pos) ∧
  P.pull (D.row g) D.negative = P.pull prod.snd (D.embedding.app D.U a.neg)

/-- Both separator inequalities are imposed in the general predicate lattice. -/
def Separates (a : ComplementaryPair (E.obj D.S)) : Prop :=
  D.positive ≤ D.embedding.app D.S a.pos ∧
  D.negative ≤ D.embedding.app D.S a.neg

/-- The diagonal pair is `δ* (Dᶜ), δ* D`. -/
def diagonalPair (a : ComplementaryPair (E.obj D.S)) : ComplementaryPair (E.obj D.U) :=
  a.swap.map (E.pull D.diagonal)

theorem pairing_row (g : D.U ⟶ D.U) :
    prod.lift (𝟙 D.U) g ≫ D.row g = g ≫ D.diagonal := by
  simp [row, diagonal, ← Category.assoc, prod.comp_lift]

/-- The diagonal calculation, before imposing nontriviality on `E(U)`.
This equality is also the algebraic input needed at generalized elements. -/
theorem diagonal_collapse (a : ComplementaryPair (E.obj D.S))
    (ha : D.Separates a) (g : D.U ⟶ D.U)
    (hg : D.Represents (D.diagonalPair a) g) : (⊥ : E.obj D.U) = ⊤ := by
  let x : ComplementaryPair (P.obj (D.U ⨯ D.U)) :=
    (D.diagonalPair a).map (D.embedding.app D.U) |>.map (P.pull prod.snd)
  let y := a.map (D.embedding.app D.S) |>.map (P.pull (D.row g))
  have hp : x.pos ≤ y.pos := by
    change P.pull prod.snd (D.embedding.app D.U (D.diagonalPair a).pos) ≤
      P.pull (D.row g) (D.embedding.app D.S a.pos)
    rw [← hg.1]
    exact OrderHomClass.mono (P.pull (D.row g)) ha.1
  have hn : x.neg ≤ y.neg := by
    change P.pull prod.snd (D.embedding.app D.U (D.diagonalPair a).neg) ≤
      P.pull (D.row g) (D.embedding.app D.S a.neg)
    rw [← hg.2]
    exact OrderHomClass.mono (P.pull (D.row g)) ha.2
  have heq := congrArg (P.pull (prod.lift (𝟙 D.U) g)) (x.eq_of_le y hp hn)
  change P.pull (prod.lift (𝟙 D.U) g)
      (P.pull prod.snd (D.embedding.app D.U (E.pull D.diagonal a.neg))) =
    P.pull (prod.lift (𝟙 D.U) g)
      (P.pull (D.row g) (D.embedding.app D.S a.pos)) at heq
  rw [← P.pull_comp, prod.lift_snd, ← P.pull_comp, D.pairing_row,
    D.embedding.naturality, D.embedding.naturality, ← E.pull_comp] at heq
  exact (a.map (E.pull (g ≫ D.diagonal))).bot_eq_top
    ((D.embedding.injective D.U heq).symm)

/-- `thm:integration-diagonal`: a separator's diagonal pair has no representative. -/
theorem integration_diagonal (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (a : ComplementaryPair (E.obj D.S)) (ha : D.Separates a) :
    ¬ ∃ g, D.Represents (D.diagonalPair a) g := by
  rintro ⟨g, hg⟩
  exact hU (D.diagonal_collapse a ha g hg)

/-- `cor:definability-algebra-inseparability`, at global elements. -/
theorem inseparable (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (represent : ∀ a : ComplementaryPair (E.obj D.U), ∃ g, D.Represents a g) :
    ¬ ∃ a, D.Separates a := by
  rintro ⟨a, ha⟩
  exact D.integration_diagonal hU a ha (represent (D.diagonalPair a))

end DiagonalData
end CategoricalEssentialIncompleteness
