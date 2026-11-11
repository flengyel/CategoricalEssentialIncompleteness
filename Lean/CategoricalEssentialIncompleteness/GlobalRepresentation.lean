/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.GlobalCartesian
public import CategoricalEssentialIncompleteness.InternalRepresentation

/-!
# The global representation comparison

The internal section supplies representatives for the external diagonal data.
The product isomorphism is included in the substitution arrow; its naturality
identifies the external rows with the internal rows after that isomorphism.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

/-- Reindexing along an isomorphism reflects equality of predicates. -/
theorem PredicateLattice.pull_iso_injective {A : Type u} [Category.{v} A]
    (P : PredicateLattice.{v, u, w} A) {X Y : A} (e : X ≅ Y) :
    Function.Injective (P.pull e.hom) := by
  intro a b h
  have h' := congrArg (P.pull e.inv) h
  rw [← P.pull_comp, ← P.pull_comp, e.inv_hom_id, P.pull_id, P.pull_id] at h'
  exact h'

namespace InternalDiagonalData
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} [H.CartesianLaws] {E P : InternalPredicates H}
variable (D : InternalDiagonalData E P)

/-- The external data, with the chosen-product comparison in the substitution map. -/
def globalData : DiagonalData E.globalPredicates P.globalPredicates where
  embedding := D.embedding.globalEmbedding
  U := ⟨D.U⟩
  S := ⟨D.S⟩
  substitution := (H.globalProductIso ⟨D.U⟩ ⟨D.U⟩).hom ≫
    (D.substitution : H.globalProduct ⟨D.U⟩ ⟨D.U⟩ ⟶ ⟨D.S⟩)
  positive := D.positive
  negative := D.negative
  disjoint := D.disjoint

private theorem terminal_from_terminal : terminal.from (⊤_ V) = 𝟙 (⊤_ V) :=
  terminalIsTerminal.hom_ext _ _

/-- The two notions of row differ precisely by the chosen-product isomorphism. -/
theorem global_row_comparison (g : ⊤_ V ⟶ H.hom D.U D.U) :
    (D.globalData).row g = (H.globalProductIso ⟨D.U⟩ ⟨D.U⟩).hom ≫
      (D.row g : H.globalProduct ⟨D.U⟩ ⟨D.U⟩ ⟶ ⟨D.S⟩) := by
  simp only [DiagonalData.row, globalData]
  rw [← Category.assoc, H.globalProductIso_naturality, Category.assoc]
  congr 1
  change H.comp (H.pair (H.comp (H.fst D.U D.U) g)
      (H.comp (H.snd D.U D.U) (H.identity D.U))) D.substitution = D.row g
  simp only [InternalHom.CartesianLaws.comp_id, row, substitutionAt,
    terminal_from_terminal, Category.id_comp]

/-- The external representation equations are equivalent to the internal ones at `1`. -/
theorem global_represents_iff
    (a : ComplementaryPair (⊤_ V ⟶ (E.lattice D.U).obj))
    (g : ⊤_ V ⟶ H.hom D.U D.U) :
    (D.globalData).Represents a g ↔ D.Represents a g := by
  let A : H.Global := ⟨D.U⟩
  let e := H.globalProductIso A A
  have hi := P.globalPredicates.pull_iso_injective e
  change Function.Injective (P.pull e.hom) at hi
  unfold DiagonalData.Represents
  rw [D.global_row_comparison]
  change (P.pull (H.comp e.hom (D.row g)) D.positive =
      P.pull (prod.snd : A ⨯ A ⟶ A) ((D.embedding.app D.U).postcomp _ a.pos) ∧
    P.pull (H.comp e.hom (D.row g)) D.negative =
      P.pull (prod.snd : A ⨯ A ⟶ A) ((D.embedding.app D.U).postcomp _ a.neg)) ↔ _
  have hs : (prod.snd : A ⨯ A ⟶ A) = e.hom ≫ H.globalSnd A A :=
    (H.globalProductIso_hom_snd A A).symm
  rw [hs]
  change (P.pull (H.comp e.hom (D.row g)) D.positive =
      P.pull (H.comp e.hom (H.snd D.U D.U)) ((D.embedding.app D.U).postcomp _ a.pos) ∧
    P.pull (H.comp e.hom (D.row g)) D.negative =
      P.pull (H.comp e.hom (H.snd D.U D.U)) ((D.embedding.app D.U).postcomp _ a.neg)) ↔ _
  simp only [P.pull_comp, hi.eq_iff, Represents, positiveAt, negativeAt,
    terminal_from_terminal, Category.id_comp]
  rfl

/-- The internal section supplies the representatives required by external diagonalization. -/
theorem global_representation (σ : D.RepresentationSection)
    (a : ComplementaryPair (⊤_ V ⟶ (E.lattice D.U).obj)) :
    ∃ g, (D.globalData).Represents a g :=
  ⟨((E.lattice D.U).liftComplement a ≫ σ.representative : ⊤_ V ⟶ H.hom D.U D.U),
    (D.global_represents_iff _ _).mpr (σ.represents a)⟩

/-- External inseparability obtained from the internal representation section. -/
theorem global_inseparable (σ : D.RepresentationSection)
    (hU : (⊥ : ⊤_ V ⟶ (E.lattice D.U).obj) ≠ ⊤) :
    ¬ ∃ a, (D.globalData).Separates a :=
  (D.globalData).inseparable hU (D.global_representation σ)

end InternalDiagonalData
end CategoricalEssentialIncompleteness
