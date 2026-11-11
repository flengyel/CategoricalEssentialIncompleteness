/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralEquivalence

/-! # Constructor-compatible literal numerical tree charts

The coefficient-identity transport in mappedPlainPostfixData is eliminated
by equality induction on the complete algebra, including its structure map.
The resulting one-sort chart uses the actual plain postfix predicate.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart

theorem transported_structure {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] (E : C ≌ D) {F : C ⥤ C} {G : D ⥤ D}
    (a : F ⋙ E.functor ≅ E.functor ⋙ G) (A : Endofunctor.Algebra F) :
    (AlgebraTransport.mappedAlgebra E a A).str = a.inv.app A.a ≫ E.functor.map A.str := rfl

section Reindex
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

abbrev StableData (p q : SyntaxPolynomial D) :=
  Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q),
    IsInitial A × (∀ P : D, IsInitial (SyntaxPolynomial.algebraWithParameters p q A P))

def reindexComparison {p q p' q' : SyntaxPolynomial D} (hp : p = p') (hq : q = q') :
    SyntaxPolynomial.jointFunctor p q ⋙ (CategoryTheory.Equivalence.refl : D × D ≌ D × D).functor ≅
      (CategoryTheory.Equivalence.refl : D × D ≌ D × D).functor ⋙ SyntaxPolynomial.jointFunctor p' q' :=
  Functor.rightUnitor _ ≪≫ eqToIso (congrArg₂ SyntaxPolynomial.jointFunctor hp hq) ≪≫
    (Functor.leftUnitor _).symm

def reindexAlgebra {p q p' q' : SyntaxPolynomial D} (hp : p = p') (hq : q = q')
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p' q') :=
  AlgebraTransport.mappedAlgebra (CategoryTheory.Equivalence.refl : D × D ≌ D × D)
    (reindexComparison hp hq) A

theorem reindex_first {p q p' q' : SyntaxPolynomial D} (hp : p = p') (hq : q = q')
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    (reindexAlgebra hp hq A).str.1 =
      ((reindexComparison hp hq).inv.app A.a).1 ≫ A.str.1 := rfl

/-- Equality induction proves the structure equation as well as the carrier equation. -/
def reindexDataIso {p q p' q' : SyntaxPolynomial D} (hp : p = p') (hq : q = q')
    (B : StableData p q) :
    reindexAlgebra hp hq B.1 ≅ (Eq.mp (congrArg₂ StableData hp hq) B).1 := by
  cases hp
  cases hq
  exact Endofunctor.Algebra.isoMk (Iso.refl _) (by
    apply Prod.ext
    · simp [reindexAlgebra,reindexComparison,AlgebraTransport.mappedAlgebra]
      change B.1.str.1 = (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) ≫ B.1.str.1
      simp only [Category.id_comp]
    · simp [reindexAlgebra,reindexComparison,AlgebraTransport.mappedAlgebra]
      change B.1.str.2 = (𝟙 _) ≫ (𝟙 _) ≫ (𝟙 _) ≫ B.1.str.2
      simp only [Category.id_comp])

/-- Projection to the first recursive sort preserves complete algebra morphisms. -/
def projectHom (R : ℕ → D) (N : ℕ)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.constructors R N) .unit)} (f : A ⟶ B) :
    SyntacticSyntax.projectedConstructorAlgebra R N A ⟶
      SyntacticSyntax.projectedConstructorAlgebra R N B where
  f := f.f.1
  h := by
    apply (cancel_epi (SyntacticSyntax.constructorProjection R N A)).mp
    have hp : (SyntaxPolynomial.constructors R N).eval.map f.f ≫
        SyntacticSyntax.constructorProjection R N B =
      SyntacticSyntax.constructorProjection R N A ≫
        (SyntacticSyntax.constructorFunctor R N).map f.f.1 := by
      change (SyntaxPolynomial.constructors R N).eval.map f.f ≫
          (SyntaxPolynomial.constructors R N).eval.map
            ((𝟙 B.a.1,terminal.from B.a.2) : B.a ⟶ (B.a.1,⊤_ D)) =
        (SyntaxPolynomial.constructors R N).eval.map
          ((𝟙 A.a.1,terminal.from A.a.2) : A.a ⟶ (A.a.1,⊤_ D)) ≫
            (SyntaxPolynomial.constructors R N).eval.map
              ((f.f.1,𝟙 (⊤_ D)) : (A.a.1,⊤_ D) ⟶ (B.a.1,⊤_ D))
      rw [← Functor.map_comp,← Functor.map_comp]
      congr 1
      exact Prod.ext (by simp) (terminalIsTerminal.hom_ext _ _)
    change SyntacticSyntax.constructorProjection R N A ≫
      ((SyntacticSyntax.constructorFunctor R N).map f.f.1 ≫
        (inv (SyntacticSyntax.constructorProjection R N B) ≫ B.str.1)) =
      SyntacticSyntax.constructorProjection R N A ≫
        ((inv (SyntacticSyntax.constructorProjection R N A) ≫ A.str.1) ≫ f.f.1)
    rw [← Category.assoc,hp.symm]
    have hf := congrArg Prod.fst f.h
    change (SyntaxPolynomial.constructors R N).eval.map f.f ≫ B.str.1 = A.str.1 ≫ f.f.1 at hf
    simpa only [Category.assoc,IsIso.hom_inv_id_assoc] using hf

def projectIso (R : ℕ → D) (N : ℕ)
    {A B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.constructors R N) .unit)} (i : A ≅ B) :
    SyntacticSyntax.projectedConstructorAlgebra R N A ≅
      SyntacticSyntax.projectedConstructorAlgebra R N B :=
  Endofunctor.Algebra.isoMk
    { hom := i.hom.f.1
      inv := i.inv.f.1
      hom_inv_id := congrArg (fun h => h.f.1) i.hom_inv_id
      inv_hom_id := congrArg (fun h => h.f.1) i.inv_hom_id }
    (projectHom R N i.hom).h
end Reindex



abbrev E := NumericalNamed.literalEquivalence

def wordPresentationIso (C : PredicateCategory 𝗧𝗔) :
    E.functor.obj C ≅ NumericalCoordinates.predicateObject C :=
  NumericalCoordinates.predicatePresentationIso C

theorem coefficient_label_iff (C : NumericalTuples.Object) (n : ℕ) :
    (E.inverse.obj C).val.Evalb ![n] ↔
      ∃ x : NumericalTuples.Tuple C.dimension, x ∈ C.support ∧
        NumericalTuples.code C.dimension x = n :=
  NumericalCoordinates.codedPredicate_eval C n

/-- On every actual coefficient carrier, the input coordinate is precisely
its guarded tuple code, including dimension zero. -/
theorem coefficient_code_arrow (C : NumericalTuples.Object) :
    (E.counitIso.app C).inv ≫ (wordPresentationIso (E.inverse.obj C)).hom =
      NumericalCoordinates.encode C := by
  change (NumericalCoordinates.coefficientIso C).inv ≫
      (NumericalCoordinates.predicatePresentationIso (NumericalCoordinates.codedPredicate C)).hom = _
  simp only [NumericalCoordinates.coefficientIso,Iso.trans_inv,Category.assoc,
    Iso.inv_hom_id,Category.comp_id]
  rfl

theorem coefficient_input_code (C : NumericalTuples.Object) (x : NumericalTuples.Point C) :
    (((wordPresentationIso (E.inverse.obj C)).hom).toFun
      ((E.counitIso.app C).inv.toFun x)).val = NumericalTuples.code C.dimension x.val := by
  have h := congrArg (fun f => (f.toFun x).val) (coefficient_code_arrow C)
  exact h

def coordinateData (p q : SyntaxPolynomial NumericalTuples.Object) :=
  SyntacticSyntax.mappedPlainPostfixData 𝗧𝗔 E p q

def rawPairAlgebra (p q : SyntaxPolynomial NumericalTuples.Object) :=
  SyntacticSyntax.plainPostfixAlgebra 𝗧𝗔
    (p.mapCoefficients E.inverse.obj) (q.mapCoefficients E.inverse.obj)

def mappedPair (p q : SyntaxPolynomial NumericalTuples.Object) :=
  SyntacticSyntax.Transport.mappedAlgebra E E.inverse.obj id
    (fun X => E.counitIso.app X) p q (rawPairAlgebra p q)

def sourceData (p q : SyntaxPolynomial NumericalTuples.Object) :
    StableData (p.mapCoefficients id) (q.mapCoefficients id) :=
  ⟨mappedPair p q,
    SyntaxPolynomialTransport.initial E E.inverse.obj id (fun X => E.counitIso.app X)
      p q (rawPairAlgebra p q)
      (SyntacticSyntax.plainPostfixInitial 𝗧𝗔
        (p.mapCoefficients E.inverse.obj) (q.mapCoefficients E.inverse.obj)),
    SyntacticSyntax.Transport.mappedStable E E.inverse.obj id (fun X => E.counitIso.app X)
      p q (rawPairAlgebra p q) (fun P => SyntacticSyntax.plainWithParametersInitial 𝗧𝗔
        (p.mapCoefficients E.inverse.obj) (q.mapCoefficients E.inverse.obj) P)⟩

def normalizedPair (p q : SyntaxPolynomial NumericalTuples.Object) :=
  reindexAlgebra (SyntacticSyntax.mapCoefficients_id p)
    (SyntacticSyntax.mapCoefficients_id q) (mappedPair p q)

/-- This iso compares the actual mappedPlainPostfixData structure maps. -/
def pairChart (p q : SyntaxPolynomial NumericalTuples.Object) :
    normalizedPair p q ≅ (coordinateData p q).1 := by
  change reindexAlgebra (SyntacticSyntax.mapCoefficients_id p)
      (SyntacticSyntax.mapCoefficients_id q) (sourceData p q).1 ≅
    (Eq.mp (congrArg₂ StableData (SyntacticSyntax.mapCoefficients_id p)
      (SyntacticSyntax.mapCoefficients_id q)) (sourceData p q)).1
  exact reindexDataIso (SyntacticSyntax.mapCoefficients_id p)
    (SyntacticSyntax.mapCoefficients_id q) (sourceData p q)

variable (R : ℕ → NumericalTuples.Object) (N : ℕ)

abbrev oneSortRaw := rawPairAlgebra (SyntaxPolynomial.constructors R N) .unit
abbrev oneSortMapped := normalizedPair (SyntaxPolynomial.constructors R N) .unit
abbrev oneSortNormalized := SyntacticSyntax.projectedConstructorAlgebra R N (oneSortMapped R N)

/-- The source predicate is the plain parser with named, ordered coefficient labels. -/
abbrev treePredicate : PredicateCategory 𝗧𝗔 :=
  SyntacticSyntax.Postfix.plainCarrier false
    ((SyntaxPolynomial.constructors R N).mapCoefficients E.inverse.obj)
    ((SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object).mapCoefficients E.inverse.obj)

/-- Its carrier is the actual image of the plain-word predicate, not a freshly chosen tree type. -/
theorem oneSortNormalized_carrier : (oneSortNormalized R N).a = E.functor.obj (treePredicate R N) := rfl

def coordinateOneSort : Endofunctor.Algebra (SyntacticSyntax.constructorFunctor R N) :=
  SyntacticSyntax.projectedConstructorAlgebra R N
    (coordinateData (SyntaxPolynomial.constructors R N) .unit).1

def coordinateOneSortInitial : IsInitial (coordinateOneSort R N) :=
  SyntacticSyntax.projectedConstructorInitial R N
    (coordinateData (SyntaxPolynomial.constructors R N) .unit).1
    (coordinateData (SyntaxPolynomial.constructors R N) .unit).2.1

/-- Initiality gives a complete constructor-preserving comparison to the
already constructed numerical syntax algebra. -/
def coordinateOneSortIso : coordinateOneSort R N ≅ NumericalSyntax.oneSortAlgebra R N :=
  (coordinateOneSortInitial R N).uniqueUpToIso (NumericalSyntax.oneSortInitial R N)

def normalizedOneSortChart : oneSortNormalized R N ≅ NumericalSyntax.oneSortAlgebra R N :=
  projectIso R N (pairChart (SyntaxPolynomial.constructors R N) .unit) ≪≫ coordinateOneSortIso R N

/-- The input comparison consists only of the projection, coefficient-identity
reindexing and canonical polynomial comparison. -/
def rawConstructorInput :
    (SyntacticSyntax.constructorFunctor R N).obj (oneSortNormalized R N).a ⟶
      E.functor.obj (((SyntaxPolynomial.constructors R N).mapCoefficients
        E.inverse.obj).eval.obj (oneSortRaw R N).a) :=
  inv (SyntacticSyntax.constructorProjection R N (oneSortMapped R N)) ≫
    ((reindexComparison (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.constructors R N))
      (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object))).inv.app
        (mappedPair (SyntaxPolynomial.constructors R N) .unit).a).1 ≫
      (SyntaxPolynomialTransport.component E E.inverse.obj id
        (fun X => E.counitIso.app X) (SyntaxPolynomial.constructors R N)
        (oneSortRaw R N).a).inv

/-- In particular, the transported constructor is the actual plain-parser
constructor after these specified input comparisons. -/
theorem normalized_raw_constructor :
    (oneSortNormalized R N).str = rawConstructorInput R N ≫
      E.functor.map (oneSortRaw R N).str.1 := by
  have hr := reindex_first
    (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.constructors R N))
    (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object))
    (mappedPair (SyntaxPolynomial.constructors R N) .unit)
  have hm : (mappedPair (SyntaxPolynomial.constructors R N) .unit).str.1 =
      (SyntaxPolynomialTransport.component E E.inverse.obj id
        (fun X => E.counitIso.app X) (SyntaxPolynomial.constructors R N)
        (oneSortRaw R N).a).inv ≫ E.functor.map (oneSortRaw R N).str.1 := rfl
  let j := inv (SyntacticSyntax.constructorProjection R N (oneSortMapped R N))
  let r := ((reindexComparison
    (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.constructors R N))
    (SyntacticSyntax.mapCoefficients_id (SyntaxPolynomial.unit : SyntaxPolynomial NumericalTuples.Object))).inv.app
      (mappedPair (SyntaxPolynomial.constructors R N) .unit).a).1
  have h1 := congrArg (fun f => j ≫ f) hr
  have h2 := congrArg (fun f => j ≫ (r ≫ f)) hm
  exact h1.trans (h2.trans (by simp only [rawConstructorInput,Category.assoc,j,r]))

def treeObject : NumericalTuples.Object := NumericalCoordinates.predicateObject (treePredicate R N)

@[simp] theorem treeObject_dimension : (treeObject R N).dimension = 1 := rfl

@[simp] theorem treeObject_mem (n : ℕ) :
    n ∈ (treeObject R N).support ↔ (treePredicate R N).val.Evalb ![n] := Iff.rfl

/-- The chart is to the literal unary numerical carrier of the parser words. -/
def treeChart : (NumericalSyntax.oneSortAlgebra R N).a ≅ treeObject R N :=
  ((Endofunctor.Algebra.forget (SyntacticSyntax.constructorFunctor R N)).mapIso
    (normalizedOneSortChart R N)).symm ≪≫
      wordPresentationIso (treePredicate R N)

def literalOneSort : Endofunctor.Algebra (SyntacticSyntax.constructorFunctor R N) where
  a := treeObject R N
  str := (SyntacticSyntax.constructorFunctor R N).map
      (wordPresentationIso (treePredicate R N)).inv ≫
    (oneSortNormalized R N).str ≫
      (wordPresentationIso (treePredicate R N)).hom

def literalNormalizedIso : oneSortNormalized R N ≅ literalOneSort R N :=
  Endofunctor.Algebra.isoMk
    (wordPresentationIso (treePredicate R N)) (by
      change (SyntacticSyntax.constructorFunctor R N).map _ ≫
        ((SyntacticSyntax.constructorFunctor R N).map _ ≫ _ ≫ _) = _
      rw [← Category.assoc,← Functor.map_comp,Iso.hom_inv_id,
        (SyntacticSyntax.constructorFunctor R N).map_id,Category.id_comp])

def literalOneSortIso : NumericalSyntax.oneSortAlgebra R N ≅ literalOneSort R N :=
  (normalizedOneSortChart R N).symm ≪≫ literalNormalizedIso R N

def literalOneSortInitial : IsInitial (literalOneSort R N) :=
  (NumericalSyntax.oneSortInitial R N).ofIso (literalOneSortIso R N)

/-- Every ordered constructor, with its original coefficient, commutes with the chart. -/
abbrev tree_constructor := (literalOneSortIso R N).hom.h

theorem algebra_constructor_apply {G : NumericalTuples.Object ⥤ NumericalTuples.Object}
    {A B : Endofunctor.Algebra G} (i : A ≅ B)
    (x : NumericalTuples.Point (G.obj A.a)) :
    B.str.toFun ((G.map i.hom.f).toFun x) = i.hom.f.toFun (A.str.toFun x) :=
  congrArg (fun k => k.toFun x) i.hom.h

abbrev tree_constructor_apply := algebra_constructor_apply (literalOneSortIso R N)

/-- This raw constructor equation is proved before identifying the chosen syntax algebra. -/
theorem literal_raw_constructor :
    (SyntacticSyntax.constructorFunctor R N).map
        (wordPresentationIso (treePredicate R N)).hom ≫
      (literalOneSort R N).str = (oneSortNormalized R N).str ≫
        (wordPresentationIso (treePredicate R N)).hom :=
  (literalNormalizedIso R N).hom.h

/-- The unprojected raw polynomial comparison retains both recursive sorts,
all coefficient counits, and the plain-parser constructor morphism. -/
abbrev mappedPair_constructor (p q : SyntaxPolynomial NumericalTuples.Object) :=
  transported_structure (E.prod E)
    (SyntaxPolynomialTransport.jointIso E E.inverse.obj id
      (fun X => E.counitIso.app X) p q) (rawPairAlgebra p q)

end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
