/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPolynomial

/-! # Projection of the actual mapped constructor algebra

The canonical polynomial comparison commutes with the projection to the
first recursive sort. The proof uses its proved naturality and the unique
terminal morphism. No initial algebra is assumed to be preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Projection
open SyntacticSyntax

variable (σ : ℕ → PredicateCategory 𝗣𝗔) (N : ℕ)

def constructorInputIso (A : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) :
    K.obj ((SyntaxPolynomial.constructors σ N).eval.obj A) ≅
      (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.obj ((K.prod K).obj A) :=
  Polynomial.normalizedComponent id (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N)
    (mapCoefficients_id _) (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N) A

theorem constructorInputIso_natural {A B : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    (f : A ⟶ B) :
    K.map ((SyntaxPolynomial.constructors σ N).eval.map f) ≫ (constructorInputIso σ N B).hom =
      (constructorInputIso σ N A).hom ≫
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.map ((K.prod K).map f) :=
  Polynomial.normalizedComponent_natural id (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors σ N)
    (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N)
    (mapCoefficients_id _) (SyntaxOperationsTransport.mapCoefficients_constructors K.obj σ N) f

def oneSortInputIso (X : PredicateCategory 𝗣𝗔) :
    K.obj ((constructorFunctor σ N).obj X) ≅
      (constructorFunctor (fun n => K.obj (σ n)) N).obj (K.obj X) :=
  constructorInputIso σ N (X,⊤_ (PredicateCategory 𝗣𝗔)) ≪≫
    (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.mapIso
      ((@Iso.refl NumericalTuples.Object inferInstance (K.obj X)).prod (asIso (terminalComparison K)))

/-- This is mapping of the displayed polynomial algebra only. -/
def mappedJointAlgebra
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    Endofunctor.Algebra
      (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N) .unit) where
  a := (K.prod K).obj A.a
  str := ((constructorInputIso σ N A.a).inv ≫ K.map A.str.1,
    (asIso (terminalComparison K)).inv ≫ K.map A.str.2)

def mappedOneSortAlgebra (B : Endofunctor.Algebra (constructorFunctor σ N)) :
    Endofunctor.Algebra (constructorFunctor (fun n => K.obj (σ n)) N) where
  a := K.obj B.a
  str := (oneSortInputIso σ N B.a).inv ≫ K.map B.str

/-- The entire projection square is proved before any postfix carrier
or constructor operation is substituted. -/
theorem projection_square
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    K.map (constructorProjection σ N A) ≫ (oneSortInputIso σ N A.a.1).hom =
      (constructorInputIso σ N A.a).hom ≫
        constructorProjection (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A) := by
  let sourceLeg : @Quiver.Hom (PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) inferInstance
      A.a (A.a.1,⊤_ (PredicateCategory 𝗣𝗔)) := (𝟙 A.a.1,terminal.from A.a.2)
  let terminalLeg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj (A.a.1,⊤_ (PredicateCategory 𝗣𝗔)))
      (K.obj A.a.1,⊤_ NumericalTuples.Object) := (𝟙 _,terminalComparison K)
  let targetLeg : @Quiver.Hom (NumericalTuples.Object × NumericalTuples.Object) inferInstance
      ((K.prod K).obj A.a) (K.obj A.a.1,⊤_ NumericalTuples.Object) :=
    (𝟙 _,terminal.from (K.obj A.a.2))
  have he : (K.prod K).map sourceLeg ≫ terminalLeg = targetLeg := by
    apply Prod.ext
    · change K.map (𝟙 A.a.1) ≫ 𝟙 (K.obj A.a.1) = 𝟙 (K.obj A.a.1)
      rw [CategoryTheory.Functor.map_id,Category.id_comp]
    · exact terminal.hom_ext _ _
  change K.map ((SyntaxPolynomial.constructors σ N).eval.map sourceLeg) ≫
      ((constructorInputIso σ N (A.a.1,⊤_ (PredicateCategory 𝗣𝗔))).hom ≫
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.map terminalLeg) =
      (constructorInputIso σ N A.a).hom ≫
        (SyntaxPolynomial.constructors (fun n => K.obj (σ n)) N).eval.map targetLeg
  rw [← Category.assoc,constructorInputIso_natural,Category.assoc,← CategoryTheory.Functor.map_comp,he]

/-- Mapping and first-sort projection give the same actual structure
morphism. The inverse projection maps are justified by the existing
constructor-polynomial theorem, including arity zero. -/
theorem projected_mapping_str
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    (mappedOneSortAlgebra σ N (projectedConstructorAlgebra σ N A)).str =
      (projectedConstructorAlgebra (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A)).str := by
  let sourceProjection := constructorProjection σ N A
  let targetProjection := constructorProjection (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A)
  let a := constructorInputIso σ N A.a
  let b := oneSortInputIso σ N A.a.1
  let _ : IsIso sourceProjection := constructorProjection_isIso σ N A
  let _ : IsIso targetProjection := constructorProjection_isIso _ _ _
  have hp : K.map sourceProjection ≫ b.hom = a.hom ≫ targetProjection := projection_square σ N A
  have hs : K.map sourceProjection ≫ K.map (inv sourceProjection) =
      𝟙 (K.obj ((SyntaxPolynomial.constructors σ N).eval.obj A.a)) :=
    (K.map_comp sourceProjection (inv sourceProjection)).symm.trans
      ((congrArg K.map (IsIso.hom_inv_id sourceProjection)).trans (K.map_id _))
  apply (cancel_epi (K.map sourceProjection ≫ b.hom)).mp
  change (K.map sourceProjection ≫ b.hom) ≫
      (b.inv ≫ K.map (inv sourceProjection ≫ A.str.1)) =
    (K.map sourceProjection ≫ b.hom) ≫
      (inv targetProjection ≫ a.inv ≫ K.map A.str.1)
  calc
    _ = K.map A.str.1 := by
      simp only [CategoryTheory.Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]
      rw [← Category.assoc,hs,Category.id_comp]
    _ = _ := by
      rw [hp]
      simp only [Category.assoc,IsIso.hom_inv_id_assoc,Iso.hom_inv_id_assoc]

def projectedMappingIso
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.constructors σ N) .unit)) :
    mappedOneSortAlgebra σ N (projectedConstructorAlgebra σ N A) ≅
      projectedConstructorAlgebra (fun n => K.obj (σ n)) N (mappedJointAlgebra σ N A) :=
  Endofunctor.Algebra.isoMk (Iso.refl _) (by
    change (constructorFunctor (fun n => K.obj (σ n)) N).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id,Category.id_comp,Category.comp_id,projected_mapping_str])

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation.Projection
