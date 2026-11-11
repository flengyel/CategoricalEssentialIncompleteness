/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticIncompletenessDiagonal
public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSentenceMorphisms
public import CategoricalEssentialIncompleteness.V46NumericalTuplesStructure
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsPrinted

/-! # Actual numerical sentence maps in the classical restriction splitting -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness
abbrev numericalQ := NumericalTuples.splitComparison

/-- The graph includes the genuine guarded tuple encoding at both dimensions. -/
theorem numericalQ_graph {X Y : NumericalTuples.Object} (f : X ⟶ Y) (a b : ℕ) :
    b ∈ ClassicalPrograms.J.map (numericalQ.map f).hom a ↔
      ∃ x : NumericalTuples.Point X, NumericalTuples.code X.dimension x.val = a ∧
        NumericalTuples.code Y.dimension (f.toFun x).val = b := by
  exact NumericalTuples.comparisonMap_graph f a b

theorem numericalQ_total {X Y : NumericalTuples.Object} (f : X ⟶ Y) :
    isTotal (numericalQ.map f) :=
  (NumericalTuples.classicalTotalEquivalence.functor.map f).property

theorem numericalQ_range_support {X Y : NumericalTuples.Object} (f : X ⟶ Y) :
    ClassicalPrograms.splitSupport (Ranges.range (numericalQ.map f)) =
      {b | ∃ x : NumericalTuples.Point X, NumericalTuples.code Y.dimension (f.toFun x).val = b} := by
  change EnumerableCarriers.support (Ranges.range (NumericalTuples.comparison.map f).hom) = _
  rw [EnumerableCarriers.support_range]
  ext b
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨x,_,hx⟩ := (NumericalTuples.comparisonMap_graph f a b).mp ha
    exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨NumericalTuples.code X.dimension x.val,
      (NumericalTuples.comparisonMap_graph f _ b).mpr ⟨x,rfl,hx⟩⟩

/-- A proved numerical sentence chart conjugates the actual range
idempotent, including all its coded points. -/
theorem numericalQ_range_iso {X Y Z : NumericalTuples.Object} (f : X ⟶ Y) (i : Y ≅ Z) :
    Idem.pull (numericalQ.map i.hom) (Ranges.range (numericalQ.map (f ≫ i.hom))) =
      Ranges.range (numericalQ.map f) := by
  apply ClassicalPrograms.splitSupport_injective
  rw [ClassicalPrograms.splitSupport_pull,numericalQ_range_support,numericalQ_range_support]
  ext n
  constructor
  · rintro ⟨w,hw,p,hp⟩
    obtain ⟨y,hy,hyw⟩ := (numericalQ_graph i.hom n w).mp hw
    have hv : (i.hom.toFun y).val = (i.hom.toFun (f.toFun p)).val :=
      NumericalTuples.code_injective Z.dimension (hyw.trans hp.symm)
    have he : y = f.toFun p := by
      have hpoint : i.hom.toFun y = i.hom.toFun (f.toFun p) := Subtype.ext hv
      exact (congrArg (fun m => m.toFun y) i.hom_inv_id).symm.trans
        ((congrArg i.inv.toFun hpoint).trans
          (congrArg (fun m => m.toFun (f.toFun p)) i.hom_inv_id))
    exact ⟨p,(congrArg (fun q : NumericalTuples.Point Y => NumericalTuples.code Y.dimension q.val) he.symm).trans hy⟩
  · rintro ⟨p,hp⟩
    refine ⟨NumericalTuples.code Z.dimension (i.hom.toFun (f.toFun p)).val,?_,p,rfl⟩
    exact (numericalQ_graph i.hom n _).mpr ⟨f.toFun p,hp,rfl⟩

abbrev E : SplitObject ClassicalPrograms.Rec := numericalQ.obj NumericalSentenceMorphisms.omega
abbrev S_rec : SplitObject ClassicalPrograms.Rec := numericalQ.obj NumericalSentenceMorphisms.sentence

private theorem omega_supported (n : ℕ) : n ∈ NumericalTuples.codedSupport NumericalSentenceMorphisms.omega :=
  ⟨n,Set.mem_univ _,rfl⟩

theorem omega_domain : E.domain.hom = 𝟙 ClassicalPrograms.U := by
  apply ClassicalPrograms.J.map_injective
  change ClassicalPrograms.J.map (E.domain.hom : ClassicalPrograms.U ⟶ ClassicalPrograms.U) =
    ClassicalPrograms.J.map (𝟙 ClassicalPrograms.U)
  rw [CategoryTheory.Functor.map_id]
  change (supportIdentity (NumericalTuples.codedSupport NumericalSentenceMorphisms.omega) : ℕ → Part ℕ) =
    (fun n : ℕ => Part.some n)
  apply PFun.ext
  intro x y
  rw [mem_supportIdentity,Part.mem_some_iff]
  exact and_iff_right (omega_supported x)

/-- The numerical variable carrier is compared with I(omega) by its
actual kappa_1 code, rather than by an assumed definitional equality. -/
def omegaIso : ClassicalPrograms.parameterObject ≅ E where
  hom :=
    { hom := 𝟙 ClassicalPrograms.U
      source := Category.id_comp _
      target := by
        change (𝟙 ClassicalPrograms.U) ≫ (E.domain.hom : ClassicalPrograms.U ⟶ ClassicalPrograms.U) =
          𝟙 ClassicalPrograms.U
        exact (congrArg (fun d : ClassicalPrograms.U ⟶ ClassicalPrograms.U => (𝟙 ClassicalPrograms.U) ≫ d)
          omega_domain).trans (Category.id_comp _) }
  inv :=
    { hom := 𝟙 ClassicalPrograms.U
      source := by
        change (E.domain.hom : ClassicalPrograms.U ⟶ ClassicalPrograms.U) ≫ (𝟙 ClassicalPrograms.U) =
          𝟙 ClassicalPrograms.U
        exact (congrArg (fun d : ClassicalPrograms.U ⟶ ClassicalPrograms.U => d ≫ (𝟙 ClassicalPrograms.U))
          omega_domain).trans (Category.id_comp _)
      target := Category.comp_id _ }
  hom_inv_id := SplitObject.Hom.ext (Category.id_comp _)
  inv_hom_id := by
    apply SplitObject.Hom.ext
    change (𝟙 ClassicalPrograms.U) ≫ 𝟙 ClassicalPrograms.U = E.domain.hom
    rw [omega_domain,Category.id_comp]

theorem omegaIso_hom : omegaIso.hom.hom = 𝟙 ClassicalPrograms.U := rfl

def nu : S_rec ⟶ S_rec := numericalQ.map NumericalSentenceMorphisms.negation

def theta : ClassicalPrograms.parameterObject ⟶ S_rec :=
  omegaIso.hom ≫ numericalQ.map
    (NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)

theorem nu_total : isTotal nu := numericalQ_total _
theorem theta_total : isTotal theta := isTotal_comp (iso_total omegaIso) (numericalQ_total _)

private theorem theta_underlying : theta.hom =
    (numericalQ.map (NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)).hom := Category.id_comp _

theorem theta_graph (n w : ℕ) : w ∈ ClassicalPrograms.J.map theta.hom n ↔
    w = NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val n := by
  rw [theta_underlying,numericalQ_graph]
  constructor
  · rintro ⟨x,hx,hw⟩
    change x.val = n at hx
    have he : x = NumericalSentenceMorphisms.omegaPoint n := Subtype.ext hx
    subst x
    change ((NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables).toFun
        (NumericalSentenceMorphisms.omegaPoint n)).val = w at hw
    exact hw.symm.trans (NumericalSentenceMorphisms.theta_value
      NamedArithmeticDiagonalBounds.namedAlpha NamedArithmeticDiagonalBounds.namedAlpha_freeVariables n)
  · intro hw
    refine ⟨NumericalSentenceMorphisms.omegaPoint n,rfl,?_⟩
    change ((NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables).toFun
        (NumericalSentenceMorphisms.omegaPoint n)).val = w
    exact (NumericalSentenceMorphisms.theta_value NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables n).trans hw.symm

theorem theta_sentence_supported (n : ℕ) :
    NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val n ∈
      NumericalSentenceMorphisms.sentence.support := by
  have h : ((NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables).toFun
        (NumericalSentenceMorphisms.omegaPoint n)).val =
      NamedArithmeticUnarySubstitution.value (M := ℕ) ArithmeticDiagonalCodes.alpha.val n :=
    NumericalSentenceMorphisms.theta_value NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables n
  exact h ▸ ((NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
    NamedArithmeticDiagonalBounds.namedAlpha_freeVariables).toFun (NumericalSentenceMorphisms.omegaPoint n)).property

theorem nu_graph (n w : ℕ) : w ∈ ClassicalPrograms.J.map nu.hom n ↔
    n ∈ NumericalSentenceMorphisms.sentence.support ∧
      w = NamedArithmeticProofSearch.negationWord ℕ n := by
  rw [nu,numericalQ_graph]
  constructor
  · rintro ⟨s,hs,hw⟩
    change s.val = n at hs
    change (NumericalSentenceMorphisms.negation.toFun s).val = w at hw
    subst n
    exact ⟨s.property,hw.symm.trans (NumericalSentenceMorphisms.negation_value s)⟩
  · rintro ⟨hs,hw⟩
    let s : NumericalTuples.Point NumericalSentenceMorphisms.sentence := ⟨n,hs⟩
    refine ⟨s,rfl,?_⟩
    change (NumericalSentenceMorphisms.negation.toFun s).val = w
    exact (NumericalSentenceMorphisms.negation_value s).trans hw.symm

/-- The word carrier is the proved sentence presentation of the actual
constructed categorical syntax, with its genuine sentence pullback. -/
def syntaxSentenceIso : numericalQ.obj Coordinates.numericalSyntax.sentenceObject ≅ S_rec :=
  numericalQ.mapIso (asIso Coordinates.literalSentence)

theorem syntax_negation_square :
    numericalQ.map Coordinates.numericalSyntax.sentenceNegation ≫ syntaxSentenceIso.hom =
      syntaxSentenceIso.hom ≫ nu := by
  exact (numericalQ.map_comp _ _).symm.trans
    ((congrArg numericalQ.map SentenceMorphisms.negation_literal_square).trans (numericalQ.map_comp _ _))

def syntaxTheta : ClassicalPrograms.parameterObject ⟶
    numericalQ.obj Coordinates.numericalSyntax.sentenceObject :=
  omegaIso.hom ≫ numericalQ.map SentenceMorphisms.omegaDomainIso.inv ≫
    numericalQ.map (SentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)

theorem syntax_theta_square : syntaxTheta ≫ syntaxSentenceIso.hom = theta := by
  have hs := congrArg (fun f => SentenceMorphisms.omegaDomainIso.inv ≫ f)
    (SentenceMorphisms.theta_literal NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)
  have hs' : SentenceMorphisms.omegaDomainIso.inv ≫
      SentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
        NamedArithmeticDiagonalBounds.namedAlpha_freeVariables ≫ Coordinates.literalSentence =
      NumericalSentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
        NamedArithmeticDiagonalBounds.namedAlpha_freeVariables := by
    simpa only [Category.assoc,Iso.inv_hom_id_assoc] using hs
  change (omegaIso.hom ≫ numericalQ.map SentenceMorphisms.omegaDomainIso.inv ≫
      numericalQ.map (SentenceMorphisms.theta NamedArithmeticDiagonalBounds.namedAlpha
        NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)) ≫
      numericalQ.map Coordinates.literalSentence = _
  rw [Category.assoc,Category.assoc,← numericalQ.map_comp,← numericalQ.map_comp,hs']
  rfl

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Incompleteness
