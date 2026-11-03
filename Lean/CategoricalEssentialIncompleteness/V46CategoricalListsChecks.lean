import CategoricalEssentialIncompleteness.V46CategoricalLists

/-! The list fold is checked at morphism types in every parameter slice. -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]

example (V X : D) : (listFunctor V).obj X = ((⊤_ D) ⨿ (V ⨯ X)) := rfl

example {V X Y : D} (f : X ⟶ Y) :
    (listFunctor V).map f = coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) f) := rfl

example {V : D} (L : StableListAlgebra V) (P : D)
    (B : ListAlgebra (constantFamily P V)) :
    constantFamily P L.algebra.carrier ⟶ B.carrier :=
  L.foldWithParameters P B

example {V : D} (L : StableListAlgebra V) (P : D)
    (B : ListAlgebra (constantFamily P V)) :
    (L.foldWithParameters P B).left ≫ B.carrier.hom =
      (constantFamily P L.algebra.carrier).hom :=
  L.foldWithParameters_over P B

example {V : D} (L : StableListAlgebra V) (P : D)
    (B : ListAlgebra (constantFamily P V))
    (f : constantFamily P L.algebra.carrier ⟶ B.carrier)
    (hnil : (L.algebra.withParameters P).nil ≫ f = B.nil)
    (hcons : (L.algebra.withParameters P).cons ≫ f =
      prod.map (𝟙 (constantFamily P V)) f ≫ B.cons) :
    f = L.foldWithParameters P B :=
  L.foldWithParameters_unique P B f hnil hcons

example {V : D} (L : StableListAlgebra V) :
    L.algebra.carrier ⨯ L.algebra.carrier ⟶ L.algebra.carrier := L.append

example (F : D ⥤ D) (A : Endofunctor.Algebra F) (hA : IsInitial A)
    (B : Endofunctor.Algebra F) (m : B ⟶ A) [Mono m.f] : IsIso m.f :=
  initial_algebra_monic_induction F A hA B m
