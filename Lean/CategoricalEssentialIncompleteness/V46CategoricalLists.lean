/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Over

/-! # Parameter-stable categorical list algebras and folds -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

section ListFunctor

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] [HasFiniteCoproducts D]

/-- The list endofunctor with coefficient object `V`. -/
def listFunctor (V : D) : D ⥤ D where
  obj X := (⊤_ D) ⨿ (V ⨯ X)
  map f := coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) f)
  map_id X := by simp
  map_comp f g := by
    simp only [prod.map_id_comp, coprod.map_id_comp]

/-- The two constructor morphisms of a list algebra. -/
structure ListAlgebra (V : D) where
  carrier : D
  nil : ⊤_ D ⟶ carrier
  cons : V ⨯ carrier ⟶ carrier

namespace ListAlgebra

variable {V : D}

def asAlgebra (L : ListAlgebra V) : Endofunctor.Algebra (listFunctor V) :=
  ⟨L.carrier, coprod.desc L.nil L.cons⟩

/-- Every initial list algebra has a unique fold to each list algebra. -/
def fold (L : ListAlgebra V) (hL : IsInitial L.asAlgebra) (B : ListAlgebra V) :
    L.carrier ⟶ B.carrier := (hL.to B.asAlgebra).f

theorem fold_nil (L : ListAlgebra V) (hL : IsInitial L.asAlgebra) (B : ListAlgebra V) :
    L.nil ≫ L.fold hL B = B.nil := by
  have h := (hL.to B.asAlgebra).h
  change coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) (L.fold hL B)) ≫
    coprod.desc B.nil B.cons = coprod.desc L.nil L.cons ≫ L.fold hL B at h
  have hh := congrArg (fun k => coprod.inl ≫ k) h
  rw [← Category.assoc, coprod.inl_map, Category.id_comp, coprod.inl_desc,
    ← Category.assoc, coprod.inl_desc] at hh
  exact hh.symm

theorem fold_cons (L : ListAlgebra V) (hL : IsInitial L.asAlgebra) (B : ListAlgebra V) :
    L.cons ≫ L.fold hL B = prod.map (𝟙 V) (L.fold hL B) ≫ B.cons := by
  have h := (hL.to B.asAlgebra).h
  change coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) (L.fold hL B)) ≫
    coprod.desc B.nil B.cons = coprod.desc L.nil L.cons ≫ L.fold hL B at h
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  rw [← Category.assoc, coprod.inr_map, Category.assoc, coprod.inr_desc,
    ← Category.assoc, coprod.inr_desc] at hh
  exact hh.symm

theorem fold_unique (L : ListAlgebra V) (hL : IsInitial L.asAlgebra)
    (B : ListAlgebra V) (f : L.carrier ⟶ B.carrier)
    (hnil : L.nil ≫ f = B.nil)
    (hcons : L.cons ≫ f = prod.map (𝟙 V) f ≫ B.cons) : f = L.fold hL B := by
  let m : L.asAlgebra ⟶ B.asAlgebra :=
    { f := f
      h := by
        change coprod.map (𝟙 (⊤_ D)) (prod.map (𝟙 V) f) ≫
          coprod.desc B.nil B.cons = coprod.desc L.nil L.cons ≫ f
        apply coprod.hom_ext
        · rw [← Category.assoc, coprod.inl_map, Category.id_comp, coprod.inl_desc,
            ← Category.assoc, coprod.inl_desc]
          exact hnil.symm
        · rw [← Category.assoc, coprod.inr_map, Category.assoc, coprod.inr_desc,
            ← Category.assoc, coprod.inr_desc]
          exact hcons.symm }
  exact congrArg Endofunctor.Algebra.Hom.f (hL.hom_ext m (hL.to B.asAlgebra))

end ListAlgebra

end ListFunctor

section ParameterStability

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]

/-- The constant family with fiber `X` over a parameter object `P`. -/
def constantFamily (P X : D) : Over P := Over.mk (prod.fst : P ⨯ X ⟶ P)

/-- Base change of objects and morphisms along `P → 1`. -/
def constantFamilyFunctor (P : D) : D ⥤ Over P where
  obj := constantFamily P
  map f := Over.homMk (prod.map (𝟙 P) f) (by simp [constantFamily])
  map_id X := by
    apply Over.OverMorphism.ext
    change prod.map (𝟙 P) (𝟙 X) = 𝟙 (P ⨯ X)
    exact prod.map_id_id
  map_comp f g := by
    apply Over.OverMorphism.ext
    change prod.map (𝟙 P) (f ≫ g) = prod.map (𝟙 P) f ≫ prod.map (𝟙 P) g
    exact prod.map_id_comp f g

/-- Pull back the two list constructors to the slice over `P`.
The underlying carrier is `P × W → P`; the products and coproducts used
by its list endofunctor are products and coproducts in `D/P`. -/
def ListAlgebra.withParameters {V : D} (L : ListAlgebra V) (P : D) :
    ListAlgebra (constantFamily P V) where
  carrier := constantFamily P L.carrier
  nil := Over.homMk (prod.lift (⊤_ (Over P)).hom
    (terminal.from (⊤_ (Over P)).left ≫ L.nil)) (by simp [constantFamily])
  cons := Over.homMk (prod.lift
    ((constantFamily P V ⨯ constantFamily P L.carrier).hom)
    ((prod.lift
      ((prod.fst : constantFamily P V ⨯ constantFamily P L.carrier ⟶
        constantFamily P V).left ≫ prod.snd)
      ((prod.snd : constantFamily P V ⨯ constantFamily P L.carrier ⟶
        constantFamily P L.carrier).left ≫ prod.snd)) ≫
      L.cons)) (by simp [constantFamily])

/-- Definition A.1's list-algebra assumption, including initiality in
every parameter slice. -/
structure StableListAlgebra (V : D) where
  algebra : ListAlgebra V
  initial : IsInitial algebra.asAlgebra
  stable : ∀ P : D, IsInitial (algebra.withParameters P).asAlgebra

namespace StableListAlgebra

variable {V : D} (L : StableListAlgebra V)

/-- The fold in `D/P`, whose target may be any family over `P`. -/
def foldWithParameters (P : D) (B : ListAlgebra (constantFamily P V)) :
    constantFamily P L.algebra.carrier ⟶ B.carrier :=
  (L.algebra.withParameters P).fold (L.stable P) B

theorem foldWithParameters_over (P : D) (B : ListAlgebra (constantFamily P V)) :
    (L.foldWithParameters P B).left ≫ B.carrier.hom =
      (constantFamily P L.algebra.carrier).hom :=
  Over.w _

theorem foldWithParameters_nil (P : D) (B : ListAlgebra (constantFamily P V)) :
    (L.algebra.withParameters P).nil ≫ L.foldWithParameters P B = B.nil :=
  (L.algebra.withParameters P).fold_nil (L.stable P) B

theorem foldWithParameters_cons (P : D) (B : ListAlgebra (constantFamily P V)) :
    (L.algebra.withParameters P).cons ≫ L.foldWithParameters P B =
      prod.map (𝟙 (constantFamily P V)) (L.foldWithParameters P B) ≫ B.cons :=
  (L.algebra.withParameters P).fold_cons (L.stable P) B

theorem foldWithParameters_unique (P : D) (B : ListAlgebra (constantFamily P V))
    (f : constantFamily P L.algebra.carrier ⟶ B.carrier)
    (hnil : (L.algebra.withParameters P).nil ≫ f = B.nil)
    (hcons : (L.algebra.withParameters P).cons ≫ f =
      prod.map (𝟙 (constantFamily P V)) f ≫ B.cons) :
    f = L.foldWithParameters P B :=
  (L.algebra.withParameters P).fold_unique (L.stable P) B f hnil hcons

/-- For concatenation, the parameter is the second list. The empty
input returns this parameter, and the step uses the list constructor. -/
def appendAlgebra : ListAlgebra (constantFamily L.algebra.carrier V) where
  carrier := constantFamily L.algebra.carrier L.algebra.carrier
  nil := Over.homMk (prod.lift (⊤_ (Over L.algebra.carrier)).hom
    (⊤_ (Over L.algebra.carrier)).hom) (by simp [constantFamily])
  cons := (L.algebra.withParameters L.algebra.carrier).cons

/-- Concatenation as a morphism of families. Its source coordinates are
the fixed second list followed by the recursively consumed first list. -/
def appendWithParameter :
    constantFamily L.algebra.carrier L.algebra.carrier ⟶
      constantFamily L.algebra.carrier L.algebra.carrier :=
  L.foldWithParameters L.algebra.carrier L.appendAlgebra

theorem appendWithParameter_nil :
    (L.algebra.withParameters L.algebra.carrier).nil ≫ L.appendWithParameter =
      L.appendAlgebra.nil :=
  L.foldWithParameters_nil L.algebra.carrier L.appendAlgebra

theorem appendWithParameter_cons :
    (L.algebra.withParameters L.algebra.carrier).cons ≫ L.appendWithParameter =
      prod.map (𝟙 (constantFamily L.algebra.carrier V)) L.appendWithParameter ≫
        (L.algebra.withParameters L.algebra.carrier).cons :=
  L.foldWithParameters_cons L.algebra.carrier L.appendAlgebra

/-- The concatenation morphism has the manuscript order `(w,w')`.
The swap puts the second list in the parameter coordinate of the fold. -/
def append : L.algebra.carrier ⨯ L.algebra.carrier ⟶ L.algebra.carrier :=
  prod.lift prod.snd prod.fst ≫ L.appendWithParameter.left ≫ prod.snd

end StableListAlgebra

end ParameterStability

/-- Initial-algebra induction: the inclusion of a monic subalgebra of
an initial algebra is invertible. This applies in every parameter slice. -/
theorem initial_algebra_monic_induction {D : Type u} [Category.{v} D]
    (F : D ⥤ D) (A : Endofunctor.Algebra F) (hA : IsInitial A)
    (B : Endofunctor.Algebra F) (m : B ⟶ A) [Mono m.f] : IsIso m.f := by
  let n := hA.to B
  have h : n ≫ m = 𝟙 A := hA.hom_ext _ _
  have hn : n.f ≫ m.f = 𝟙 A.a := congrArg Endofunctor.Algebra.Hom.f h
  have hm : m.f ≫ n.f = 𝟙 B.a := by
    apply (cancel_mono m.f).mp
    rw [Category.assoc, hn, Category.comp_id, Category.id_comp]
  exact ⟨⟨n.f, hm, hn⟩⟩

end CategoricalEssentialIncompleteness.V46
