/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ArithmeticAdequacy
public import CategoricalEssentialIncompleteness.NumericalEnrichedPredicates

/-!
# Internal arithmetic representation

Numeral substitution and the theorem and refutation predicates define internal
diagonal data in the numerical Set-enrichment. Strong numeralwise definability
supplies a section of its representation pullback.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness
namespace ArithmeticSyntax

attribute [local instance] typeHomDistribLattice typeHomBoundedOrder

/-- Arithmetic substitution and provability in the numerical Set-enrichment. -/
def internalDiagonalData (T : ArithmeticTheory) [Entailment.Consistent T] :
    InternalDiagonalData
      (Numerical.enrichedRestriction.domainPredicates Numerical.enrichedProducts)
      Numerical.enrichedPredicates where
  embedding := Numerical.enrichedPredicateEmbedding
  U := Numerical.nat
  S := Numerical.nat
  substitution := TypeCat.ofHom fun _ =>
    (Numerical.enrichedTotalEquiv _ _).symm substitutionArrow
  positive := TypeCat.ofHom fun _ => theoremPredicate T
  negative := TypeCat.ofHom fun _ => refutationPredicate T
  disjoint := by
    dsimp only [Numerical.enrichedPredicates, Numerical.enrichedPredicateLattice, typeLattice]
    apply disjoint_iff.mpr
    apply ConcreteCategory.hom_ext
    intro t
    exact disjoint_iff.mp (predicates_disjoint T)

/-- Evaluate a family of internal domains as a numerical domain. -/
def domainEvaluation (X : Type) (x : X) :
    BoundedLatticeHom (X ⟶ Numerical.enrichedRestriction.domainObject Numerical.nat)
      (Numerical.Domain Numerical.nat) where
  toFun a := Numerical.enrichedDomainEquiv Numerical.nat (a x)
  map_inf' a b := (Numerical.enrichedDomainOrderIso Numerical.nat).map_inf (a x) (b x)
  map_sup' a b := (Numerical.enrichedDomainOrderIso Numerical.nat).map_sup (a x) (b x)
  map_bot' := (Numerical.enrichedDomainOrderIso Numerical.nat).map_bot
  map_top' := (Numerical.enrichedDomainOrderIso Numerical.nat).map_top

/-- A complementary family evaluates to a complementary pair of numerical domains. -/
def domainPairAt {X : Type}
    (a : ComplementaryPair (X ⟶ Numerical.enrichedRestriction.domainObject Numerical.nat))
    (x : X) : ComplementaryPair (Numerical.Domain Numerical.nat) :=
  a.map (domainEvaluation X x)

private theorem total_fst_apply {X : Type} (x : X) :
    Numerical.enrichedTotalEquiv _ _
      ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).fst
        Numerical.nat Numerical.nat x) =
      Numerical.fst (Numerical.totalObject Numerical.nat)
        (Numerical.totalObject Numerical.nat) := by
  apply WideSubcategory.hom_ext
  exact ConcreteCategory.congr_hom
    (Numerical.enrichedRestriction.total_fst_ι Numerical.enrichedProducts
      (T := X) Numerical.nat Numerical.nat) x

private theorem total_snd_apply {X : Type} (x : X) :
    Numerical.enrichedTotalEquiv _ _
      ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
        Numerical.nat Numerical.nat x) =
      Numerical.snd (Numerical.totalObject Numerical.nat)
        (Numerical.totalObject Numerical.nat) := by
  apply WideSubcategory.hom_ext
  exact ConcreteCategory.congr_hom
    (Numerical.enrichedRestriction.total_snd_ι Numerical.enrichedProducts
      (T := X) Numerical.nat Numerical.nat) x

/-- Internal rows evaluate to the numerical substitution rows. -/
theorem internal_row_apply (T : ArithmeticTheory) [Entailment.Consistent T]
    {X : Type} (g : X ⟶ Numerical.enrichedRestriction.totalObject Numerical.nat Numerical.nat)
    (x : X) :
    Numerical.enrichedTotalEquiv _ _ ((internalDiagonalData T).row g x) =
      substitutionRow (Numerical.enrichedTotalEquiv _ _ (g x)) := by
  unfold InternalDiagonalData.row
  dsimp only [internalDiagonalData]
  erw [Numerical.enrichedTotal_comp]
  change Numerical.enrichedTotalEquiv (Numerical.product Numerical.nat Numerical.nat)
    (Numerical.product Numerical.nat Numerical.nat)
    ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).pair
      ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).comp
        ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).fst
          Numerical.nat Numerical.nat) g)
      ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
        Numerical.nat Numerical.nat) x) ≫
    Numerical.enrichedTotalEquiv _ _ ((Numerical.enrichedTotalEquiv _ _).symm substitutionArrow) = _
  erw [Numerical.enrichedTotal_pair, Numerical.enrichedTotal_comp, total_fst_apply,
    total_snd_apply, Equiv.apply_symm_apply]
  rfl

/-- Internal representation is equivalent to the numerical equations at every parameter. -/
theorem internal_represents_iff (T : ArithmeticTheory) [Entailment.Consistent T]
    {X : Type}
    (a : ComplementaryPair (X ⟶ Numerical.enrichedRestriction.domainObject Numerical.nat))
    (g : X ⟶ Numerical.enrichedRestriction.totalObject Numerical.nat Numerical.nat) :
    (internalDiagonalData T).Represents a g ↔
      ∀ x : X, RepresentsPair T (domainPairAt a x)
        (Numerical.enrichedTotalEquiv _ _ (g x)) := by
  change (_ = _ ∧ _ = _) ↔ _
  constructor
  · rintro ⟨hp, hn⟩ x
    constructor
    · have h := ConcreteCategory.congr_hom hp x
      change Numerical.predicates.pull
        (Numerical.enrichedTotalEquiv (Numerical.product Numerical.nat Numerical.nat) Numerical.nat
          ((internalDiagonalData T).row g x)) (theoremPredicate T) =
        Numerical.predicates.pull (Numerical.enrichedTotalEquiv _ _
          ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
            Numerical.nat Numerical.nat x))
          (Numerical.domainSubobject Numerical.nat (domainPairAt a x).pos) at h
      erw [internal_row_apply, total_snd_apply] at h
      exact h
    · have h := ConcreteCategory.congr_hom hn x
      change Numerical.predicates.pull
        (Numerical.enrichedTotalEquiv (Numerical.product Numerical.nat Numerical.nat) Numerical.nat
          ((internalDiagonalData T).row g x)) (refutationPredicate T) =
        Numerical.predicates.pull (Numerical.enrichedTotalEquiv _ _
          ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
            Numerical.nat Numerical.nat x))
          (Numerical.domainSubobject Numerical.nat (domainPairAt a x).neg) at h
      erw [internal_row_apply, total_snd_apply] at h
      exact h
  · intro h
    constructor
    · apply ConcreteCategory.hom_ext
      intro x
      change Numerical.predicates.pull
        (Numerical.enrichedTotalEquiv (Numerical.product Numerical.nat Numerical.nat) Numerical.nat
          ((internalDiagonalData T).row g x)) (theoremPredicate T) =
        Numerical.predicates.pull (Numerical.enrichedTotalEquiv _ _
          ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
            Numerical.nat Numerical.nat x))
          (Numerical.domainSubobject Numerical.nat (domainPairAt a x).pos)
      erw [internal_row_apply, total_snd_apply]
      exact (h x).1
    · apply ConcreteCategory.hom_ext
      intro x
      change Numerical.predicates.pull
        (Numerical.enrichedTotalEquiv (Numerical.product Numerical.nat Numerical.nat) Numerical.nat
          ((internalDiagonalData T).row g x)) (refutationPredicate T) =
        Numerical.predicates.pull (Numerical.enrichedTotalEquiv _ _
          ((Numerical.enrichedRestriction.totalHom Numerical.enrichedProducts).snd
            Numerical.nat Numerical.nat x))
          (Numerical.domainSubobject Numerical.nat (domainPairAt a x).neg)
      erw [internal_row_apply, total_snd_apply]
      exact (h x).2

/-- The universal complementary pair of internal numerical domains. -/
def internalUniversalPair : ComplementaryPair
    ((Numerical.enrichedRestriction.domainLattice Numerical.nat).Complements ⟶
      Numerical.enrichedRestriction.domainObject Numerical.nat) :=
  ⟨_, _, (Numerical.enrichedRestriction.domainLattice Numerical.nat).complement_isCompl⟩

/-- A choice of numerical representatives determines an internal representing arrow. -/
def internalRepresentative (T : ArithmeticTheory) [Entailment.Consistent T]
    (hrep : ∀ a : ComplementaryPair (Numerical.Domain Numerical.nat),
      ∃ g, RepresentsPair T a g) :
    (Numerical.enrichedRestriction.domainLattice Numerical.nat).Complements ⟶
      Numerical.enrichedRestriction.totalObject Numerical.nat Numerical.nat :=
  TypeCat.ofHom fun a => (Numerical.enrichedTotalEquiv _ _).symm
    (Classical.choose (hrep (domainPairAt internalUniversalPair a)))

theorem internalRepresentative_represents (T : ArithmeticTheory) [Entailment.Consistent T]
    (hrep : ∀ a : ComplementaryPair (Numerical.Domain Numerical.nat),
      ∃ g, RepresentsPair T a g) :
    (internalDiagonalData T).Represents internalUniversalPair (internalRepresentative T hrep) := by
  apply (internal_represents_iff T _ _).mpr
  intro a
  change RepresentsPair T _ ((Numerical.enrichedTotalEquiv _ _)
    ((Numerical.enrichedTotalEquiv _ _).symm _))
  erw [Equiv.apply_symm_apply]
  exact Classical.choose_spec (hrep (domainPairAt internalUniversalPair a))

theorem internalRepresentative_condition (T : ArithmeticTheory) [Entailment.Consistent T]
    (hrep : ∀ a : ComplementaryPair (Numerical.Domain Numerical.nat),
      ∃ g, RepresentsPair T a g) :
    internalRepresentative T hrep ≫ (internalDiagonalData T).representationLeft =
      (internalDiagonalData T).representationRight := by
  have h := internalRepresentative_represents T hrep
  apply prod.hom_ext
  · simp only [InternalDiagonalData.representationLeft,
      InternalDiagonalData.representationRight, Category.assoc, prod.lift_fst]
    erw [Numerical.enrichedPredicates.precomp_pull,
      InternalDiagonalData.precomp_row, Category.comp_id,
      InternalDiagonalData.precomp_positive]
    exact h.1
  · simp only [InternalDiagonalData.representationLeft,
      InternalDiagonalData.representationRight, Category.assoc, prod.lift_snd]
    erw [Numerical.enrichedPredicates.precomp_pull,
      InternalDiagonalData.precomp_row, Category.comp_id,
      InternalDiagonalData.precomp_negative]
    exact h.2

/-- Representation of every complementary numerical domain yields a section
of the internal representation pullback. -/
def representationSectionOfPairs (T : ArithmeticTheory) [Entailment.Consistent T]
    (hrep : ∀ a : ComplementaryPair (Numerical.Domain Numerical.nat),
      ∃ g, RepresentsPair T a g) : (internalDiagonalData T).RepresentationSection :=
  (internalDiagonalData T).sectionOfRepresentative (internalRepresentative T hrep)
    (internalRepresentative_condition T hrep)

/-- Strong numeralwise definability of recursive sets supplies the internal section. -/
def representationSectionOfDefinability (T : ArithmeticTheory) [Entailment.Consistent T]
    (hdef : ∀ A : Set ℕ, ComputablePred (· ∈ A) →
      ∃ φ : ArithmeticSemisentence 1,
        ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ) :
    (internalDiagonalData T).RepresentationSection :=
  representationSectionOfPairs T ((represents_all_pairs_iff T).mpr hdef)

/-- Every consistent extension of `PA⁻` has an internal representation section. -/
def representationSection (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] [Entailment.Consistent T] :
    (internalDiagonalData T).RepresentationSection :=
  representationSectionOfPairs T (every_pair_represented T)

/-- Regard a numerical domain as a constant global internal domain. -/
def domainConstants : BoundedLatticeHom (Numerical.Domain Numerical.nat)
    (⊤_ Type ⟶ Numerical.enrichedRestriction.domainObject Numerical.nat) where
  toFun a := TypeCat.ofHom fun _ => (Numerical.enrichedDomainOrderIso Numerical.nat).symm a
  map_inf' a b := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (Numerical.enrichedDomainOrderIso Numerical.nat).symm.map_inf a b
  map_sup' a b := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (Numerical.enrichedDomainOrderIso Numerical.nat).symm.map_sup a b
  map_bot' := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (Numerical.enrichedDomainOrderIso Numerical.nat).symm.map_bot
  map_top' := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (Numerical.enrichedDomainOrderIso Numerical.nat).symm.map_top

/-- A numerical complementary pair gives a global internal complementary pair. -/
def globalDomainPair (a : ComplementaryPair (Numerical.Domain Numerical.nat)) :
    ComplementaryPair (⊤_ Type ⟶ Numerical.enrichedRestriction.domainObject Numerical.nat) :=
  a.map domainConstants

@[simp] theorem domainPairAt_globalDomainPair
    (a : ComplementaryPair (Numerical.Domain Numerical.nat)) (t : ⊤_ Type) :
    domainPairAt (globalDomainPair a) t = a := by
  cases a with
  | mk pos neg compl =>
    change ComplementaryPair.mk
      (Numerical.enrichedDomainEquiv Numerical.nat
        ((Numerical.enrichedDomainEquiv Numerical.nat).symm pos))
      (Numerical.enrichedDomainEquiv Numerical.nat
        ((Numerical.enrichedDomainEquiv Numerical.nat).symm neg)) _ = _
    simp only [Equiv.apply_symm_apply]

/-- The internal section exists exactly when every recursive set has a strong
numeralwise definition in the theory. -/
theorem representationSection_iff_definability (T : ArithmeticTheory)
    [Entailment.Consistent T] :
    Nonempty (internalDiagonalData T).RepresentationSection ↔
      ∀ A : Set ℕ, ComputablePred (· ∈ A) →
        ∃ φ : ArithmeticSemisentence 1,
          ArithmeticRepresentation.StrongNumeralwise T (· ∈ A) φ := by
  constructor
  · rintro ⟨σ⟩
    apply (represents_all_pairs_iff T).mp
    intro a
    let g := (Numerical.enrichedRestriction.domainLattice Numerical.nat).liftComplement
      (globalDomainPair a) ≫ σ.representative
    let t : ⊤_ Type := default
    refine ⟨Numerical.enrichedTotalEquiv _ _ (g t), ?_⟩
    have h := (internal_represents_iff T (globalDomainPair a) g).mp
      (σ.represents (globalDomainPair a)) t
    have hh := domainPairAt_globalDomainPair a t
    rw [hh] at h
    convert h using 1
  · intro hdef
    exact ⟨representationSectionOfDefinability T hdef⟩

end ArithmeticSyntax
end CategoricalEssentialIncompleteness
