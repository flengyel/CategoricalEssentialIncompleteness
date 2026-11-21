/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPlain
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationProjection

/-! # Initiality of the mapped PA constructor algebra

The target algebra is constructed from the literal TA plain-word algebra using the
proved equivalence and polynomial comparison. Its initiality is therefore proved
independently of the PA interpretation. The constructor squares identify the PA image
with this constructed algebra.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Initial
open SyntacticSyntax
open NumericalSyntaxTreeChart (reindexAlgebra reindexComparison)

section Reindex
variable {p q p' q' : SyntaxPolynomial NumericalTuples.Object}
  (hp : p = p') (hq : q = q')
  (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))

def reindexedPairAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p' q') where
  a := A.a
  str := ((eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj A.a) hp)).inv ≫ A.str.1,
    (eqToIso (congrArg (fun a => (SyntaxPolynomial.eval a).obj A.a) hq)).inv ≫ A.str.2)

def reindexedPairIso : reindexAlgebra hp hq A ≅ reindexedPairAlgebra hp hq A := by
  cases hp
  cases hq
  refine Endofunctor.Algebra.isoMk (Iso.refl _) ?_
  apply Prod.ext
  · simp [reindexedPairAlgebra,reindexAlgebra,reindexComparison,AlgebraTransport.mappedAlgebra,
      CategoryTheory.Category.id_comp]
    change 𝟙 (p.eval.obj A.a) ≫ A.str.1 =
      𝟙 (p.eval.obj A.a) ≫ 𝟙 (p.eval.obj A.a) ≫ 𝟙 (p.eval.obj A.a) ≫ A.str.1
    simp only [CategoryTheory.Category.id_comp]
  · simp [reindexedPairAlgebra,reindexAlgebra,reindexComparison,AlgebraTransport.mappedAlgebra,
      CategoryTheory.Category.id_comp]
    change 𝟙 (q.eval.obj A.a) ≫ A.str.2 =
      𝟙 (q.eval.obj A.a) ≫ 𝟙 (q.eval.obj A.a) ≫ 𝟙 (q.eval.obj A.a) ≫ A.str.2
    simp only [CategoryTheory.Category.id_comp]

def reindexedPairInitial (h : IsInitial A) : IsInitial (reindexedPairAlgebra hp hq A) :=
  (AlgebraTransport.initial
    (CategoryTheory.Equivalence.refl : NumericalTuples.Object × NumericalTuples.Object ≌
      NumericalTuples.Object × NumericalTuples.Object)
    (reindexComparison hp hq) A h).ofIso (reindexedPairIso hp hq A)
end Reindex

section MappedPairs
variable {I : Type} (s : I → PredicateCategory 𝗣𝗔) (t : I → PredicateCategory 𝗧𝗔)
  (c : ∀ i, K.obj (s i) ≅ NumericalSyntaxTreeChart.E.functor.obj (t i))
  (p q : SyntaxPolynomial I)
  (p₀ q₀ : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (p₁ q₁ : SyntaxPolynomial (PredicateCategory 𝗧𝗔))
  (pN qN : SyntaxPolynomial NumericalTuples.Object)
  (hp₀ : (p).mapCoefficients s = p₀) (hq₀ : q.mapCoefficients s = q₀)
  (hp₁ : (p).mapCoefficients t = p₁) (hq₁ : q.mapCoefficients t = q₁)
  (hpN : (p).mapCoefficients (fun i => K.obj (s i)) = pN)
  (hqN : q.mapCoefficients (fun i => K.obj (s i)) = qN)
  (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p₀ q₀))
  (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p₁ q₁))

def mappedSourcePair : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor pN qN) where
  a := (K.prod K).obj A.a
  str := ((Polynomial.normalizedComponent s p p₀ pN hp₀ hpN A.a).inv ≫ K.map A.str.1,
    (Polynomial.normalizedComponent s q q₀ qN hq₀ hqN A.a).inv ≫ K.map A.str.2)

def mappedLiteralPair : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor pN qN) where
  a := (NumericalSyntaxTreeChart.E.prod NumericalSyntaxTreeChart.E).functor.obj B.a
  str := ((Polynomial.normalizedLiteralComponent s t c p p₁ pN hp₁ hpN B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.1,
    (Polynomial.normalizedLiteralComponent s t c q q₁ qN hq₁ hqN B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.2)

/-- Equality induction proves the complete reindexed algebra comparison,
including both structure maps; its underlying morphism is identity. -/
def mappedLiteralPairIso :
    mappedLiteralPair s t c p q p₁ q₁ pN qN hp₁ hq₁ hpN hqN B ≅
      reindexedPairAlgebra hpN hqN
        (AlgebraTransport.mappedAlgebra (NumericalSyntaxTreeChart.E.prod NumericalSyntaxTreeChart.E)
          (SyntaxPolynomialTransport.jointIso NumericalSyntaxTreeChart.E t (fun i => K.obj (s i))
            (fun i => (c i).symm) p q)
          (NumericalSyntaxTreeChart.reindexAlgebra hp₁.symm hq₁.symm B)) := by
  cases hp₁
  cases hq₁
  cases hpN
  cases hqN
  refine Endofunctor.Algebra.isoMk (Iso.refl _) ?_
  apply Prod.ext
  · simp [mappedLiteralPair,Polynomial.normalizedLiteralComponent,reindexedPairAlgebra,
      NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
      AlgebraTransport.mappedAlgebra,SyntaxPolynomialTransport.jointIso,
      CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp]
    change 𝟙 _ ≫ (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t
        (fun i => K.obj (s i)) (fun i => (c i).symm) p B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map (𝟙 ((p.mapCoefficients t).eval.obj B.a)) ≫
      NumericalSyntaxTreeChart.E.functor.map (𝟙 ((p.mapCoefficients t).eval.obj B.a)) ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.1 =
      (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t
        (fun i => K.obj (s i)) (fun i => (c i).symm) p B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.1
    rw [CategoryTheory.Functor.map_id]
    simp only [CategoryTheory.Category.id_comp]
  · simp [mappedLiteralPair,Polynomial.normalizedLiteralComponent,reindexedPairAlgebra,
      NumericalSyntaxTreeChart.reindexAlgebra,NumericalSyntaxTreeChart.reindexComparison,
      AlgebraTransport.mappedAlgebra,SyntaxPolynomialTransport.jointIso,
      CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp]
    change 𝟙 _ ≫ (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t
        (fun i => K.obj (s i)) (fun i => (c i).symm) q B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map (𝟙 ((q.mapCoefficients t).eval.obj B.a)) ≫
      NumericalSyntaxTreeChart.E.functor.map (𝟙 ((q.mapCoefficients t).eval.obj B.a)) ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.2 =
      (SyntaxPolynomialTransport.component NumericalSyntaxTreeChart.E t
        (fun i => K.obj (s i)) (fun i => (c i).symm) q B.a).inv ≫
      NumericalSyntaxTreeChart.E.functor.map B.str.2
    rw [CategoryTheory.Functor.map_id]
    simp only [CategoryTheory.Category.id_comp]

variable (bX : K.obj A.a.1 ≅ NumericalSyntaxTreeChart.E.functor.obj B.a.1)
  (bY : K.obj A.a.2 ≅ NumericalSyntaxTreeChart.E.functor.obj B.a.2)
  (hTerm : NormalizedConstructorEquation s t c A.a.1 A.a.2 A.a.1 B.a.1 B.a.2 B.a.1 bX bY bX
    p p₀ p₁ hp₀ hp₁ A.str.1 B.str.1)
  (hFormula : NormalizedConstructorEquation s t c A.a.1 A.a.2 A.a.2 B.a.1 B.a.2 B.a.2 bX bY bY
    q q₀ q₁ hq₀ hq₁ A.str.2 B.str.2)

def mappedPairIso :
    mappedSourcePair s p q p₀ q₀ pN qN hp₀ hq₀ hpN hqN A ≅
      mappedLiteralPair s t c p q p₁ q₁ pN qN hp₁ hq₁ hpN hqN B :=
  Endofunctor.Algebra.isoMk (bX.prod bY) (by
    apply Prod.ext
    · exact Polynomial.normalized_algebra_square s t c A.a.1 A.a.2 B.a.1 B.a.2 bX bY
        p p₀ p₁ pN hp₀ hp₁ hpN bX A.str.1 B.str.1 hTerm
    · exact Polynomial.normalized_algebra_square s t c A.a.1 A.a.2 B.a.1 B.a.2 bX bY
        q q₀ q₁ qN hq₀ hq₁ hqN bY A.str.2 B.str.2 hFormula)

@[simp] theorem mappedPairIso_hom_f :
    (mappedPairIso s t c p q p₀ q₀ p₁ q₁ pN qN hp₀ hq₀ hp₁ hq₁ hpN hqN A B bX bY hTerm hFormula).hom.f =
      (bX.prod bY).hom := rfl

/-- The only initiality input is that of the separately constructed TA
algebra, discharged by plainPostfixInitial in the concrete application. -/
def mappedSourcePairInitial (hB : IsInitial B) :
    IsInitial (mappedSourcePair s p q p₀ q₀ pN qN hp₀ hq₀ hpN hqN A) := by
  have hB' : IsInitial (NumericalSyntaxTreeChart.reindexAlgebra hp₁.symm hq₁.symm B) :=
    AlgebraTransport.initial
      (CategoryTheory.Equivalence.refl : PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔 ≌
        PredicateCategory 𝗧𝗔 × PredicateCategory 𝗧𝗔)
      (NumericalSyntaxTreeChart.reindexComparison hp₁.symm hq₁.symm) B hB
  have hm := SyntaxPolynomialTransport.initial NumericalSyntaxTreeChart.E t
    (fun i => K.obj (s i)) (fun i => (c i).symm) p q _ hB'
  have hr := reindexedPairInitial hpN hqN _ hm
  exact (hr.ofIso
    (mappedLiteralPairIso s t c p q p₁ q₁ pN qN hp₁ hq₁ hpN hqN B).symm).ofIso
      (mappedPairIso s t c p q p₀ q₀ p₁ q₁ pN qN hp₀ hq₀ hp₁ hq₁ hpN hqN A B bX bY hTerm hFormula).symm
end MappedPairs

section ConstructorSpecialization
variable (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ)

def mappedSourceConstructorIso
    (A : Endofunctor.Algebra
      (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    mappedSourcePair id (SyntaxPolynomial.constructors σ N) .unit
        (SyntaxPolynomial.constructors σ N) .unit
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N) .unit
        (mapCoefficients_id _) rfl
        (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N) rfl A ≅
      Projection.mappedJointAlgebra σ N A :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (SyntaxPolynomial.jointFunctor
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N) .unit).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,CategoryTheory.Category.id_comp,CategoryTheory.Category.comp_id]
    apply Prod.ext
    · rfl
    · simp [mappedSourcePair,Projection.mappedJointAlgebra,Polynomial.normalizedComponent,
        Polynomial.component,CategoryTheory.Category.assoc]
      change K.map A.str.2 = terminalComparison K ≫ 𝟙 (⊤_ NumericalTuples.Object) ≫
        inv (terminalComparison K) ≫ K.map A.str.2
      rw [CategoryTheory.Category.id_comp,IsIso.hom_inv_id_assoc])
end ConstructorSpecialization

section Actual
variable (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ)
local notation "p" => SyntaxPolynomial.constructors σ N
local notation "pN" => SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N
local notation "S" => postfixAlgebra 𝗣𝗔 p SyntaxPolynomial.unit
local notation "B" => plainPostfixAlgebra 𝗧𝗔
  (SyntaxPolynomial.mapCoefficients labelMap p) SyntaxPolynomial.unit
local notation "j₀" => realizedWordIso false p SyntaxPolynomial.unit
local notation "j₁" => realizedWordIso true p SyntaxPolynomial.unit
local notation "hN" => SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N
local notation "c" => fun C : PredicateCategory 𝗣𝗔 => Iso.symm (NumericalSyntaxTreeChart.E.counitIso.app (K.obj C))

/-- The PA mapped joint algebra is initial, with every comparison and scalar code law
supplied by the constructed syntax proofs. -/
abbrev mappedStoredPairInitial :=
  mappedSourcePairInitial id labelMap c p .unit p .unit ((p).mapCoefficients labelMap) .unit pN .unit
    (mapCoefficients_id _) rfl rfl rfl hN rfl S B j₀ j₁
    (normalized_mixed_term_constructor id labelMap c p .unit p .unit
      ((p).mapCoefficients labelMap) .unit (mapCoefficients_id _) rfl rfl rfl j₀ j₁
      (realizedWordIso_value false p .unit) (realizedWordIso_value true p .unit)
      NumericalPolynomialRepresentation.canonical_coefficient_value)
    (normalized_mixed_formula_constructor id labelMap c p .unit p .unit
      ((p).mapCoefficients labelMap) .unit (mapCoefficients_id _) rfl rfl rfl j₀ j₁
      (realizedWordIso_value false p .unit) (realizedWordIso_value true p .unit)
      NumericalPolynomialRepresentation.canonical_coefficient_value)
    (plainPostfixInitial 𝗧𝗔 _ _)

abbrev mappedStoredPairIso := mappedSourceConstructorIso σ N S

def mappedJointInitial : IsInitial (Projection.mappedJointAlgebra σ N S) :=
  (mappedStoredPairInitial σ N).ofIso (mappedStoredPairIso σ N)

/-- Initiality of the mapped first-sort algebra follows from the constructed joint algebra
and the proved projection comparison. -/
def mappedOneSortInitial :
    IsInitial (Projection.mappedOneSortAlgebra σ N (oneSortAlgebra 𝗣𝗔 σ N)) := by
  have hp := projectedConstructorInitial (fun n => K.obj (σ n)) N _ (mappedJointInitial σ N)
  exact hp.ofIso (Projection.projectedMappingIso σ N S).symm
end Actual
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Initial
