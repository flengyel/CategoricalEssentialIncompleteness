/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalRuleRebase
public import CategoricalEssentialIncompleteness.V46NumericalDerivationTreeUniqueness
public import CategoricalEssentialIncompleteness.V46NumericalDerivationConstructorValues

/-! # Formula-coordinate changes preserve the original derivation word -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.NumericalRuleRebase
open SyntacticDerivation
variable {F G : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) (e : F ≅ G)

private theorem matching_fst {H : NumericalTuples.Object} {m : ℕ}
    (S : RulePresentation H m) (Z : Over H) (i : Fin (m + 1)) :
    CheckedRoot.matchingMap S Z i ≫ prod.fst = pullback.fst _ _ :=
  prod.lift_fst _ _

private theorem matching_snd {H : NumericalTuples.Object} {m : ℕ}
    (S : RulePresentation H m) (Z : Over H) (i : Fin (m + 1)) :
    CheckedRoot.matchingMap S Z i ≫ prod.snd = pullback.snd _ _ :=
  prod.lift_snd _ _

/-- Changing formula coordinates leaves the ordinary labelled tree input
unchanged, including its ordered tuple of children. -/
theorem component_forget (Q : Over F) :
    (component R e Q).hom.left ≫
        InputGeometry.forget (rules R e) ((slice e).functor.obj Q) =
      InputGeometry.forget R Q := by
  apply Sigma.hom_ext
  intro i
  change Sigma.ι (R.ruleObject Q) i ≫
      (Limits.Sigma.mapIso (inputIso R e Q)).hom ≫
        Sigma.desc (fun i => CheckedRoot.matchingMap (rules R e) ((slice e).functor.obj Q) i ≫
          Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower Q.left i.val) i) =
    Sigma.ι (R.ruleObject Q) i ≫ Sigma.desc (fun i =>
      CheckedRoot.matchingMap R Q i ≫
        Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower Q.left i.val) i)
  rw [Sigma.ι_mapIso_hom_assoc,Sigma.ι_comp_desc]
  erw [Sigma.ι_comp_desc]
  have hm : (inputIso R e Q i).hom ≫
      CheckedRoot.matchingMap (rules R e) ((slice e).functor.obj Q) i =
        CheckedRoot.matchingMap R Q i := by
    apply prod.hom_ext
    · calc
        _ = (inputIso R e Q i).hom ≫
            (CheckedRoot.matchingMap (rules R e) ((slice e).functor.obj Q) i ≫ prod.fst) :=
          Category.assoc _ _ _
        _ = (inputIso R e Q i).hom ≫ pullback.fst _ _ :=
          congrArg (fun f => (inputIso R e Q i).hom ≫ f)
            (matching_fst (rules R e) ((slice e).functor.obj Q) i)
        _ = pullback.fst _ _ := input_fst R e Q i
        _ = _ := (matching_fst R Q i).symm
    · calc
        _ = (inputIso R e Q i).hom ≫
            (CheckedRoot.matchingMap (rules R e) ((slice e).functor.obj Q) i ≫ prod.snd) :=
          Category.assoc _ _ _
        _ = (inputIso R e Q i).hom ≫ pullback.snd _ _ :=
          congrArg (fun f => (inputIso R e Q i).hom ≫ f)
            (matching_snd (rules R e) ((slice e).functor.obj Q) i)
        _ = pullback.snd _ _ := input_snd R e Q i
        _ = _ := (matching_snd R Q i).symm
  simpa only [Category.assoc] using congrArg (fun h => h ≫
    Sigma.ι (fun i : Fin (N + 1) => R.instances i ⨯ finitePower Q.left i.val) i) hm

/-- The constructor diagram can be checked before specializing either
algebra to a chosen initial carrier. -/
theorem tree_hom (A : Endofunctor.Algebra R.inference)
    (B : Endofunctor.Algebra (rules R e).inference)
    (W : Endofunctor.Algebra (PolynomialComparison.ordinary R))
    (f : (slice e).functor.obj A.a ⟶ B.a) (j : B.a.left ⟶ W.a)
    (hf : (slice e).functor.map A.str ≫ f =
      (component R e A.a).hom ≫ (rules R e).inference.map f ≫ B.str)
    (hj : B.str.left ≫ j =
      InputGeometry.forget (rules R e) B.a ≫
        (PolynomialComparison.ordinary R).map j ≫ W.str) :
    A.str.left ≫ (f.left ≫ j) =
      InputGeometry.forget R A.a ≫
        (PolynomialComparison.ordinary R).map (f.left ≫ j) ≫ W.str := by
  let O := PolynomialComparison.ordinary R
  have hc := congrArg (fun h : (slice e).functor.obj (R.inference.obj A.a) ⟶ B.a =>
    h.left ≫ j) hf
  have hn := InputGeometry.forget_natural (rules R e) f
  calc
    _ = (component R e A.a).hom.left ≫ ((rules R e).inference.map f).left ≫
        B.str.left ≫ j := by
      simp only [Over.comp_left,Category.assoc] at hc
      change A.str.left ≫ f.left ≫ j = _ at hc
      exact hc
    _ = (component R e A.a).hom.left ≫ ((rules R e).inference.map f).left ≫
        InputGeometry.forget (rules R e) B.a ≫ O.map j ≫ W.str := by rw [hj]
    _ = (component R e A.a).hom.left ≫
        InputGeometry.forget (rules R e) ((slice e).functor.obj A.a) ≫
          O.map f.left ≫ O.map j ≫ W.str := by
      have h := congrArg (fun h =>
        (component R e A.a).hom.left ≫ h ≫ O.map j ≫ W.str) hn
      simp only [Category.assoc] at h
      exact h
    _ = _ := by
      have h := congrArg (fun k => k ≫ O.map (f.left ≫ j) ≫ W.str)
        (component_forget R e A.a)
      simpa only [Category.assoc,Functor.map_comp] using h

/-- Slice initiality determines the map into the ordinary tree algebra. -/
theorem code_tree :
    (codeIso R e).hom ≫ NumericalDerivation.codeTreeInclusion (rules R e) =
      NumericalDerivation.codeTreeInclusion R := by
  apply NumericalDerivation.code_tree_unique R
  exact tree_hom R e (NumericalDerivation.codeAlgebra R)
    (NumericalDerivation.codeAlgebra (rules R e)) (NumericalDerivation.ordinaryTree R)
    (overIso R e).hom (NumericalDerivation.codeTreeInclusion (rules R e))
    (constructor R e) (NumericalDerivation.code_constructor_tree (rules R e))

/-- The ordinary-word chart depends on the unchanged rule labels. -/
theorem word_square :
    (codeIso R e).hom ≫ NumericalDerivation.codeWordInclusion (rules R e) =
      NumericalDerivation.codeWordInclusion R := by
  have ho : (NumericalDerivation.ordinaryWordAlgebraIso (rules R e)).hom.f =
      (NumericalDerivation.ordinaryWordAlgebraIso R).hom.f := rfl
  have h₁ := congrArg (fun k => (codeIso R e).hom ≫ k)
    (NumericalDerivation.codeWordInclusion_tree (rules R e))
  have h₂ := congrArg (fun k => k ≫
    (NumericalDerivation.ordinaryWordAlgebraIso (rules R e)).hom.f) (code_tree R e)
  have h₃ := congrArg (fun k => NumericalDerivation.codeTreeInclusion R ≫ k) ho
  exact h₁.symm.trans ((Category.assoc _ _ _).symm.trans
    (h₂.trans (h₃.trans (NumericalDerivation.codeWordInclusion_tree R))))

theorem scalar_from_inclusions {C D W : NumericalTuples.Object}
    (f : C ⟶ D) (i : C ⟶ W) (j : D ⟶ W)
    (vC : NumericalTuples.Point C → ℕ) (vD : NumericalTuples.Point D → ℕ)
    (vW : NumericalTuples.Point W → ℕ)
    (hi : ∀ x, vW (i.toFun x) = vC x) (hj : ∀ x, vW (j.toFun x) = vD x)
    (he : f ≫ j = i) (x : NumericalTuples.Point C) :
    vD (f.toFun x) = vC x := by
  have h := congrArg (fun k => vW (k.toFun x)) he
  exact (hj (f.toFun x)).symm.trans (h.trans (hi x))

theorem inverse_scalar {C D : NumericalTuples.Object} (i : C ≅ D)
    (vC : NumericalTuples.Point C → ℕ) (vD : NumericalTuples.Point D → ℕ)
    (he : ∀ x, vD (i.hom.toFun x) = vC x) (x : NumericalTuples.Point D) :
    vC (i.inv.toFun x) = vD x := by
  have h := congrArg (fun k => vD (k.toFun x)) i.inv_hom_id
  exact (he (i.inv.toFun x)).symm.trans h

/-- The computable isomorphism fixes every original unary proof word. -/
abbrev code_word := scalar_from_inclusions
  (C := NumericalDerivation.codeObject R)
  (D := NumericalDerivation.codeObject (rules R e))
  (W := NumericalSyntaxTreeChart.treeObject (PolynomialComparison.coefficients R) N)
  (codeIso R e).hom
  (NumericalDerivation.codeWordInclusion R) (NumericalDerivation.codeWordInclusion (rules R e))
  (fun x => x.val) (fun x => x.val) (fun x => x.val)
  (NumericalDerivation.codeWordInclusion_value R)
  (NumericalDerivation.codeWordInclusion_value (rules R e)) (word_square R e)

abbrev inverse_code_word := inverse_scalar
  (C := NumericalDerivation.codeObject R)
  (D := NumericalDerivation.codeObject (rules R e)) (codeIso R e) (fun x => x.val) (fun x => x.val)
  (code_word R e)

/-- A checked word comparison can be sealed without evaluating its
chosen initial-algebra fold when projecting a scalar value. -/
structure WordIdentityData (C D : SyntacticPredicates.PredicateCategory 𝗧𝗔)
    (source : NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D) where
  iso : NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D
  comparison : iso = source
  hom_word : ∀ x : NumericalTuples.Point (NumericalCoordinates.predicateObject C),
    (iso.hom.toFun x).val = x.val
  inv_word : ∀ x : NumericalTuples.Point (NumericalCoordinates.predicateObject D),
    (iso.inv.toFun x).val = x.val

private def wordIdentityData (C D W : SyntacticPredicates.PredicateCategory 𝗧𝗔)
    (source : NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D)
    (i : NumericalCoordinates.predicateObject C ⟶ NumericalCoordinates.predicateObject W)
    (j : NumericalCoordinates.predicateObject D ⟶ NumericalCoordinates.predicateObject W)
    (hi : ∀ x, (i.toFun x).val = x.val) (hj : ∀ x, (j.toFun x).val = x.val)
    (he : source.hom ≫ j = i) : WordIdentityData C D source := by
  have h := scalar_from_inclusions
    (C := NumericalCoordinates.predicateObject C) (D := NumericalCoordinates.predicateObject D)
    (W := NumericalCoordinates.predicateObject W) source.hom i j
    (fun x => x.val) (fun x => x.val) (fun x => x.val) hi hj he
  refine ⟨source,rfl,h,?_⟩
  exact inverse_scalar source (fun x => x.val) (fun x => x.val) h

/-- Its defining value is checked from the proved constructor/uniqueness
comparison. Opacity keeps the initiality implementation behind this value. -/
opaque wordData : WordIdentityData (NumericalDerivation.successfulCodes R)
    (NumericalDerivation.successfulCodes (rules R e)) (codeIso R e) :=
  wordIdentityData (NumericalDerivation.successfulCodes R)
    (NumericalDerivation.successfulCodes (rules R e)) (NumericalDerivation.rawTreePredicate R)
    (codeIso R e) (NumericalDerivation.codeWordInclusion R)
    (NumericalDerivation.codeWordInclusion (rules R e))
    (NumericalDerivation.codeWordInclusion_value R)
    (NumericalDerivation.codeWordInclusion_value (rules R e)) (word_square R e)

namespace WordIdentityData
variable (C D : SyntacticPredicates.PredicateCategory 𝗧𝗔)
  (source : NumericalCoordinates.predicateObject C ≅ NumericalCoordinates.predicateObject D)
  (data : WordIdentityData C D source)

include data in
theorem source_hom_coded (x : NumericalTuples.Point (NumericalCoordinates.predicateObject C)) :
    NumericalTuples.code (NumericalCoordinates.predicateObject D).dimension
        (source.hom.toFun x).val =
      NumericalTuples.code (NumericalCoordinates.predicateObject C).dimension x.val := by
  change (source.hom.toFun x).val = x.val
  have h := congrArg (fun u : NumericalCoordinates.predicateObject C ≅
      NumericalCoordinates.predicateObject D => (u.hom.toFun x).val) data.comparison
  exact h.symm.trans (data.hom_word x)

include data in
theorem source_inv_coded (x : NumericalTuples.Point (NumericalCoordinates.predicateObject D)) :
    NumericalTuples.code (NumericalCoordinates.predicateObject C).dimension
        (source.inv.toFun x).val =
      NumericalTuples.code (NumericalCoordinates.predicateObject D).dimension x.val := by
  change (source.inv.toFun x).val = x.val
  have h := congrArg (fun u : NumericalCoordinates.predicateObject C ≅
      NumericalCoordinates.predicateObject D => (u.inv.toFun x).val) data.comparison
  exact h.symm.trans (data.inv_word x)
end WordIdentityData

/-- The word coordinates use κ₁, which is the identity. Both proof
carriers have dimension one by `NumericalDerivation.codeObject_dimension`. -/
abbrev code_word_coded := WordIdentityData.source_hom_coded
  (NumericalDerivation.successfulCodes R) (NumericalDerivation.successfulCodes (rules R e))
  (codeIso (F := F) (G := G) (N := N) R e) (wordData (F := F) (G := G) (N := N) R e)

abbrev inverse_code_word_coded := WordIdentityData.source_inv_coded
  (NumericalDerivation.successfulCodes R) (NumericalDerivation.successfulCodes (rules R e))
  (codeIso (F := F) (G := G) (N := N) R e) (wordData (F := F) (G := G) (N := N) R e)

end CategoricalEssentialIncompleteness.V46.NumericalRuleRebase
