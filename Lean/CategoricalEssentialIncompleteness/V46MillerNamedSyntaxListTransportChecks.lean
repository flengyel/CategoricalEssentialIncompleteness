/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransport


/-! # Parameter-list folds under the PA interpretation functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
open NamedSyntaxComparison.ListTransport
variable {C D : Type} [Category C] [Category D]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] (U V : C) (W : D) (e : F.obj V ≅ W)
example : sliceFunctor F U=Over.post F := rfl
example : PreservesFiniteLimits (sliceFunctor F U) := inferInstance
example (X : C) : (Over.post F).obj (constantFamily U X) ≅ constantFamily (F.obj U) (F.obj X) :=
  familyComparison F U X
example (X : C) : (familyComparison F U X).hom.left ≫ prod.snd=F.map (prod.snd : U ⨯ X ⟶ X) :=
  familyComparison_snd F U X
example {A B : ListAlgebra V} (f : A.asAlgebra ⟶ B.asAlgebra) :
    (mappedList F V W e A).asAlgebra ⟶ (mappedList F V W e B).asAlgebra := mappedHom F V W e f
example (L : ListAlgebra V) :
    (mappedList (Over.post F) (constantFamily U V) (constantFamily (F.obj U) W)
      (coefficientComparison F U V W e) (L.withParameters U)).asAlgebra ≅
        ((mappedList F V W e L).withParameters (F.obj U)).asAlgebra :=
  mappedParametersIso F U V W e L
example (L : StableListAlgebra V) (R : StableListAlgebra W)
    (a : (mappedList F V W e L.algebra).asAlgebra ≅ R.algebra.asAlgebra)
    (B₀ : ListAlgebra (constantFamily U V)) (B₁ : ListAlgebra (constantFamily (F.obj U) W))
    (i : (mappedList (Over.post F) (constantFamily U V) (constantFamily (F.obj U) W)
      (coefficientComparison F U V W e) B₀).asAlgebra ≅ B₁.asAlgebra) :
    (familyComparison F U L.algebra.carrier).inv ≫ (Over.post F).map (L.foldWithParameters U B₀) ≫
      i.hom.f=(constantFamilyFunctor (F.obj U)).map a.hom.f ≫ R.foldWithParameters (F.obj U) B₁ :=
  parameterFold_comparison F U V W e L R a B₀ B₁ i
