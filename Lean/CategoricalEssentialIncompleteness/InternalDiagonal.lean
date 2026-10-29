/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.InternalCartesian

/-!
# Diagonalization at arbitrary parameters

The representative in this module is a morphism from the parameter object into
an internal hom-object. It need not be a global arrow. The representation section
and the separator object are constructed in `InternalRepresentation`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

structure InternalDiagonalData {V : Type u} [Category.{v} V] [HasFiniteLimits V]
    {O : Type w} {H : InternalHom V O} (E P : InternalPredicates H) where
  embedding : InternalPredicateEmbedding E P
  U : O
  S : O
  substitution : ⊤_ V ⟶ H.hom (H.product U U) S
  positive : ⊤_ V ⟶ (P.lattice S).obj
  negative : ⊤_ V ⟶ (P.lattice S).obj
  disjoint : Disjoint positive negative

namespace InternalDiagonalData
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} {E P : InternalPredicates H}
variable (D : InternalDiagonalData E P)

def substitutionAt (T : V) : T ⟶ H.hom (H.product D.U D.U) D.S :=
  terminal.from T ≫ D.substitution
def positiveAt (T : V) : T ⟶ (P.lattice D.S).obj := terminal.from T ≫ D.positive
def negativeAt (T : V) : T ⟶ (P.lattice D.S).obj := terminal.from T ≫ D.negative

def diagonal {T : V} : T ⟶ H.hom D.U D.S :=
  H.comp (H.pair (H.identity D.U) (H.identity D.U)) (D.substitutionAt T)

def row {T : V} (g : T ⟶ H.hom D.U D.U) :
    T ⟶ H.hom (H.product D.U D.U) D.S :=
  H.comp (H.pair (H.comp (H.fst D.U D.U) g) (H.snd D.U D.U)) (D.substitutionAt T)

@[simp] theorem precomp_diagonal {T T' : V} (k : T' ⟶ T) :
    k ≫ D.diagonal = D.diagonal := by simp [diagonal, substitutionAt]
@[simp] theorem precomp_row {T T' : V} (k : T' ⟶ T) (g : T ⟶ H.hom D.U D.U) :
    k ≫ D.row g = D.row (k ≫ g) := by simp [row, substitutionAt]
@[simp] theorem precomp_positive {T T' : V} (k : T' ⟶ T) :
    k ≫ D.positiveAt T = D.positiveAt T' := by simp [positiveAt]
@[simp] theorem precomp_negative {T T' : V} (k : T' ⟶ T) :
    k ≫ D.negativeAt T = D.negativeAt T' := by simp [negativeAt]

/-- Representation at an arbitrary base object, using both equations. -/
def Represents {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.U).obj))
    (g : T ⟶ H.hom D.U D.U) : Prop :=
  P.pull (D.row g) (D.positiveAt T) =
    P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp T a.pos) ∧
  P.pull (D.row g) (D.negativeAt T) =
    P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp T a.neg)

def Separates {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.S).obj)) : Prop :=
  D.positiveAt T ≤ (D.embedding.app D.S).postcomp T a.pos ∧
  D.negativeAt T ≤ (D.embedding.app D.S).postcomp T a.neg

def diagonalPair {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.S).obj)) :
    ComplementaryPair (T ⟶ (E.lattice D.U).obj) := a.swap.map (E.pull D.diagonal)

variable [H.CartesianLaws]

/-- The two structural identities used to evaluate the row on the diagonal. -/
theorem pairing_row {T : V} (g : T ⟶ H.hom D.U D.U) :
    H.comp (H.pair (H.identity D.U) g) (D.row g) = H.comp g D.diagonal := by
  simp [row, diagonal, ← InternalHom.CartesianLaws.assoc]

/-- The diagonal calculation holds at every parameter, including `Sep`. -/
theorem diagonal_collapse {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.S).obj))
    (ha : D.Separates a) (g : T ⟶ H.hom D.U D.U)
    (hg : D.Represents (D.diagonalPair a) g) : (⊥ : T ⟶ (E.lattice D.U).obj) = ⊤ := by
  let x := (D.diagonalPair a).map ((D.embedding.app D.U).postcomp T) |>.map
    (P.pull (H.snd D.U D.U))
  let y := a.map ((D.embedding.app D.S).postcomp T) |>.map (P.pull (D.row g))
  have hp : x.pos ≤ y.pos := by
    change P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp T
      (D.diagonalPair a).pos) ≤ P.pull (D.row g) ((D.embedding.app D.S).postcomp T a.pos)
    rw [← hg.1]
    exact OrderHomClass.mono (P.pull (D.row g)) ha.1
  have hn : x.neg ≤ y.neg := by
    change P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp T
      (D.diagonalPair a).neg) ≤ P.pull (D.row g) ((D.embedding.app D.S).postcomp T a.neg)
    rw [← hg.2]
    exact OrderHomClass.mono (P.pull (D.row g)) ha.2
  have heq := congrArg (P.pull (H.pair (H.identity D.U) g)) (x.eq_of_le y hp hn)
  change P.pull (H.pair (H.identity D.U) g)
      (P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp T
        (E.pull D.diagonal a.neg))) =
    P.pull (H.pair (H.identity D.U) g)
      (P.pull (D.row g) ((D.embedding.app D.S).postcomp T a.pos)) at heq
  simp only [InternalLatticeHom.postcomp_apply] at heq
  rw [← P.pull_comp, InternalHom.CartesianLaws.pair_snd, ← P.pull_comp, D.pairing_row,
    D.embedding.naturality, D.embedding.naturality, ← E.pull_comp] at heq
  have he := D.embedding.injective T D.U
    (by simpa only [InternalLatticeHom.postcomp_apply] using heq)
  exact (a.map (E.pull (H.comp g D.diagonal))).bot_eq_top he.symm

end InternalDiagonalData
end CategoricalEssentialIncompleteness
