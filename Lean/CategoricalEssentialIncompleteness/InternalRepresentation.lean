/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.InternalDiagonal
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial

/-!
# The representation section and the internal separator

We form the manuscript's representation pullback and separator equalizer in an
arbitrary finitely complete base. A section supplies representatives at every
parameter. In particular it supplies the representative at the actual separator
object, yielding the factorization through the equalizer of the bounds.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace InternalDiagonalData
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} {E P : InternalPredicates H}
variable (D : InternalDiagonalData E P)

/-- The pair of row evaluations, denoted `ell` in the manuscript. -/
def representationLeft : H.hom D.U D.U ⟶
    (P.lattice (H.product D.U D.U)).obj ⨯ (P.lattice (H.product D.U D.U)).obj :=
  prod.lift (P.pull (D.row (𝟙 _)) (D.positiveAt _))
    (P.pull (D.row (𝟙 _)) (D.negativeAt _))

/-- The two embedded complementary predicates pulled back along the second projection. -/
def representationRight : (E.lattice D.U).Complements ⟶
    (P.lattice (H.product D.U D.U)).obj ⨯ (P.lattice (H.product D.U D.U)).obj :=
  prod.lift
    (P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp _
      (E.lattice D.U).complementPos))
    (P.pull (H.snd D.U D.U) ((D.embedding.app D.U).postcomp _
      (E.lattice D.U).complementNeg))

/-- The actual pullback `R` of `eq:v8-representation-pullback`. -/
def Representation : V := pullback D.representationLeft D.representationRight

/-- The manuscript's section of the projection `R → C_U`. -/
structure RepresentationSection where
  sectionMap : (E.lattice D.U).Complements ⟶ D.Representation
  section_eq : sectionMap ≫ pullback.snd _ _ = 𝟙 _

namespace RepresentationSection
variable {D} (σ : D.RepresentationSection)

def representative : (E.lattice D.U).Complements ⟶ H.hom D.U D.U :=
  σ.sectionMap ≫ pullback.fst _ _

theorem representative_condition : σ.representative ≫ D.representationLeft =
    D.representationRight := by
  rw [representative, Category.assoc, pullback.condition, ← Category.assoc,
    σ.section_eq, Category.id_comp]

/-- The section supplies both representation equations at every generalized point. -/
theorem represents {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.U).obj)) :
    D.Represents a ((E.lattice D.U).liftComplement a ≫ σ.representative) := by
  have hp := congrArg (fun k ↦ (E.lattice D.U).liftComplement a ≫ k ≫ prod.fst)
    σ.representative_condition
  have hn := congrArg (fun k ↦ (E.lattice D.U).liftComplement a ≫ k ≫ prod.snd)
    σ.representative_condition
  simp only [representationLeft, representationRight, Category.assoc,
    prod.lift_fst, prod.lift_snd] at hp hn
  simp only [← Category.assoc, P.precomp_pull, D.precomp_row, Category.comp_id,
    D.precomp_positive, D.precomp_negative, H.precomp_snd,
    InternalLatticeHom.postcomp_apply, InternalLattice.liftComplement_pos,
    InternalLattice.liftComplement_neg] at hp hn
  simpa only [Represents, InternalLatticeHom.postcomp_apply] using And.intro hp hn

end RepresentationSection

/-- Conversely, the two universal representation equations construct the section. -/
def sectionOfRepresentative (ρ : (E.lattice D.U).Complements ⟶ H.hom D.U D.U)
    (hρ : ρ ≫ D.representationLeft = D.representationRight) : D.RepresentationSection where
  sectionMap := pullback.lift ρ (𝟙 _) (by simpa using hρ)
  section_eq := by simp

/-- Existence of a section is equivalent to existence of the representing arrow `rho`. -/
theorem representation_section_iff : Nonempty D.RepresentationSection ↔
    ∃ ρ, ρ ≫ D.representationLeft = D.representationRight := by
  constructor
  · rintro ⟨σ⟩
    exact ⟨σ.representative, σ.representative_condition⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨D.sectionOfRepresentative ρ hρ⟩

/-- Meet equations defining the separator subobject. -/
def separatorLeft : (E.lattice D.S).Complements ⟶
    (P.lattice D.S).obj ⨯ (P.lattice D.S).obj :=
  prod.lift
    (D.positiveAt _ ⊓ (D.embedding.app D.S).postcomp _ (E.lattice D.S).complementPos)
    (D.negativeAt _ ⊓ (D.embedding.app D.S).postcomp _ (E.lattice D.S).complementNeg)

def separatorRight : (E.lattice D.S).Complements ⟶
    (P.lattice D.S).obj ⨯ (P.lattice D.S).obj :=
  prod.lift (D.positiveAt _) (D.negativeAt _)

/-- The manuscript's actual equalizer `Sep`. -/
def Sep : V := equalizer D.separatorLeft D.separatorRight

def separatorPair : ComplementaryPair (D.Sep ⟶ (E.lattice D.S).obj) :=
  (E.lattice D.S).complementPair (equalizer.ι D.separatorLeft D.separatorRight)

/-- The universal pair on `Sep` satisfies the two separator inequalities. -/
theorem separatorPair_separates : D.Separates D.separatorPair := by
  have h := equalizer.condition D.separatorLeft D.separatorRight
  have hp := congrArg (fun k ↦ k ≫ prod.fst) h
  have hn := congrArg (fun k ↦ k ≫ prod.snd) h
  simp only [separatorLeft, separatorRight, Category.assoc,
    prod.lift_fst, prod.lift_snd, InternalLattice.comp_inf,
    D.precomp_positive, D.precomp_negative] at hp hn
  constructor
  · apply inf_eq_left.mp
    simpa only [separatorPair, Sep, separatorLeft, separatorRight,
      InternalLattice.complementPair_pos,
      InternalLatticeHom.postcomp_apply, Category.assoc] using hp
  · apply inf_eq_left.mp
    simpa only [separatorPair, Sep, separatorLeft, separatorRight,
      InternalLattice.complementPair_neg,
      InternalLatticeHom.postcomp_apply, Category.assoc] using hn

/-- Every generalized separator gives a morphism into the separator equalizer. -/
def liftSeparator {T : V} (a : ComplementaryPair (T ⟶ (E.lattice D.S).obj))
    (ha : D.Separates a) : T ⟶ D.Sep :=
  equalizer.lift ((E.lattice D.S).liftComplement a) (by
    apply prod.hom_ext
    · simpa [separatorLeft, separatorRight, Category.assoc,
        InternalLatticeHom.postcomp_apply, InternalLattice.liftComplement_pos_assoc]
        using (inf_eq_left.mpr ha.1)
    · simpa [separatorLeft, separatorRight, Category.assoc,
        InternalLatticeHom.postcomp_apply, InternalLattice.liftComplement_neg_assoc]
        using (inf_eq_left.mpr ha.2))

/-- The locus where the two bounds of `E_U` agree. -/
def ZeroLocus : V := equalizer (⊥ : ⊤_ V ⟶ (E.lattice D.U).obj) ⊤

/-- The constructed diagonal pair gives the manuscript's `gamma : Sep → C_U`. -/
def separatorDiagonal : D.Sep ⟶ (E.lattice D.U).Complements :=
  (E.lattice D.U).liftComplement (D.diagonalPair D.separatorPair)

/-- At the universal separator, the section supplies the required varying representative. -/
theorem separator_represented (σ : D.RepresentationSection) :
    D.Represents (D.diagonalPair D.separatorPair)
      (D.separatorDiagonal ≫ σ.representative) := σ.represents _

variable [H.CartesianLaws]

/-- The internal diagonal proof equates the bounds as morphisms out of `Sep`. -/
theorem separator_bounds_eq (σ : D.RepresentationSection) :
    (⊥ : D.Sep ⟶ (E.lattice D.U).obj) = ⊤ :=
  D.diagonal_collapse D.separatorPair D.separatorPair_separates _ (D.separator_represented σ)

/-- The factorization in `thm:internal-inseparability`, for the internal total-arrow reduct. -/
def separatorFactor (σ : D.RepresentationSection) : D.Sep ⟶ D.ZeroLocus :=
  equalizer.lift (terminal.from D.Sep) (by simpa using D.separator_bounds_eq σ)

@[simp, reassoc]
theorem separatorFactor_ι (σ : D.RepresentationSection) :
    D.separatorFactor σ ≫ equalizer.ι (⊥ : ⊤_ V ⟶ (E.lattice D.U).obj) ⊤ =
      terminal.from D.Sep := by simp [separatorFactor]

/-- The structure arrow of the actual separator factors through the actual bound equalizer. -/
theorem internal_inseparability (σ : D.RepresentationSection) :
    ∃ f : D.Sep ⟶ D.ZeroLocus,
      f ≫ equalizer.ι (⊥ : ⊤_ V ⟶ (E.lattice D.U).obj) ⊤ = terminal.from D.Sep :=
  ⟨D.separatorFactor σ, D.separatorFactor_ι σ⟩

/-- Unequal global bounds exclude a global separator, without a well-pointedness assumption. -/
theorem no_global_separator (σ : D.RepresentationSection)
    (hne : (⊥ : ⊤_ V ⟶ (E.lattice D.U).obj) ≠ ⊤) : IsEmpty (⊤_ V ⟶ D.Sep) := by
  exact no_global_point_of_factorization hne (D.separatorFactor σ)

/-- In a base with strict initial object, an initial bound locus forces an initial separator. -/
def separatorIsInitial [HasStrictInitialObjects V] (σ : D.RepresentationSection)
    (hZ : IsInitial D.ZeroLocus) : IsInitial D.Sep :=
  hZ.ofStrict (D.separatorFactor σ)

end InternalDiagonalData
end CategoricalEssentialIncompleteness
