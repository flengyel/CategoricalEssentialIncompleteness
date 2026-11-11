/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPullback

/-! # Full finite-derivation comparison under PA numerical interpretation

The comparison uses the original rule-input pullbacks, the proved ordinary
initial algebra and validator fold, and the two successful pullbacks.
Constructor compatibility is proved by their monic tree inclusions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
open SyntacticDerivation

namespace TreeComparison
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
  (W : Endofunctor.Algebra (PolynomialComparison.ordinary R))
  (A B : Endofunctor.Algebra R.inference)
  (jA : A.a.left ⟶ W.a) (jB : B.a.left ⟶ W.a) [Mono jB]
  (hA : A.str.left ≫ jA = InputGeometry.forget R A.a ≫
    (PolynomialComparison.ordinary R).map jA ≫ W.str)
  (hB : B.str.left ≫ jB = InputGeometry.forget R B.a ≫
    (PolynomialComparison.ordinary R).map jB ≫ W.str)
  (e : A.a ≅ B.a) (he : e.hom.left ≫ jB = jA)

/-- A comparison of the actual successful pullbacks is an algebra iso
once their proved constructor-to-tree diagrams commute. -/
def ofTree : A ≅ B :=
  Endofunctor.Algebra.isoMk e (by
    apply Over.OverMorphism.ext
    apply (cancel_mono jB).mp
    change ((R.inference.map e.hom).left ≫ B.str.left) ≫ jB =
      (A.str.left ≫ e.hom.left) ≫ jB
    calc
      _ = (R.inference.map e.hom).left ≫
          (InputGeometry.forget R B.a ≫ (PolynomialComparison.ordinary R).map jB ≫ W.str) := by
        rw [CategoryTheory.Category.assoc,hB]
      _ = (InputGeometry.forget R A.a ≫ (PolynomialComparison.ordinary R).map e.hom.left) ≫
          (PolynomialComparison.ordinary R).map jB ≫ W.str := by
        rw [← CategoryTheory.Category.assoc,← CategoryTheory.Category.assoc,InputGeometry.forget_natural]
        simp only [CategoryTheory.Category.assoc]
      _ = InputGeometry.forget R A.a ≫
          (PolynomialComparison.ordinary R).map (e.hom.left ≫ jB) ≫ W.str := by
        simp only [CategoryTheory.Functor.map_comp,CategoryTheory.Category.assoc]
      _ = InputGeometry.forget R A.a ≫ (PolynomialComparison.ordinary R).map jA ≫ W.str := by rw [he]
      _ = A.str.left ≫ jA := hA.symm
      _ = _ := by rw [← he,CategoryTheory.Category.assoc])

include W jA jB hA hB he in
/-- The whole constructor equation is derived before actual proof
carriers are substituted; its body is the constructed algebra morphism law. -/
theorem ofTree_constructor :
    R.inference.map e.hom ≫ B.str = A.str ≫ e.hom :=
  (ofTree R W A B jA jB hA hB e he).hom.h
end TreeComparison

section MappedTree
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

theorem mappedAlgebra_str_left (A : Endofunctor.Algebra R.inference) :
    (mappedAlgebra R A).str.left = (sumIso R A.a).inv ≫ K.map A.str.left := rfl

/-- The original inference-to-tree diagram is transported through the
proved premise pullback and ordinary-input comparisons. -/
theorem mapped_tree
    (A : Endofunctor.Algebra R.inference)
    (W : Endofunctor.Algebra (PolynomialComparison.ordinary R)) (j : A.a.left ⟶ W.a)
    (hj : A.str.left ≫ j = InputGeometry.forget R A.a ≫
      (PolynomialComparison.ordinary R).map j ≫ W.str) :
    (mappedAlgebra R A).str.left ≫ K.map j =
      InputGeometry.forget (interpretedRules R) ((overFunctor R).obj A.a) ≫
        (PolynomialComparison.ordinary (interpretedRules R)).map (K.map j) ≫
          (mappedOrdinaryAlgebra R W).str := by
  have hf := congrArg (fun k => (sumIso R A.a).inv ≫ k ≫ (ordinaryObjectIso R A.a.left).inv)
    (forget_comparison R A.a)
  simp only [CategoryTheory.Category.assoc,Iso.hom_inv_id,CategoryTheory.Category.comp_id,Iso.inv_hom_id_assoc] at hf
  have hn := congrArg (fun k => (ordinaryObjectIso R A.a.left).inv ≫ k ≫
      (ordinaryObjectIso R W.a).inv) (ordinaryObjectIso_natural R j)
  simp only [CategoryTheory.Category.assoc,Iso.hom_inv_id,CategoryTheory.Category.comp_id,Iso.inv_hom_id_assoc] at hn
  have hm := congrArg K.map hj
  simp only [CategoryTheory.Functor.map_comp] at hm
  rw [mappedAlgebra_str_left,CategoryTheory.Category.assoc]
  calc
    _ = (sumIso R A.a).inv ≫ (K.map (InputGeometry.forget R A.a) ≫
        K.map ((PolynomialComparison.ordinary R).map j) ≫ K.map W.str) :=
      congrArg (fun k => (sumIso R A.a).inv ≫ k) hm
    _ = ((sumIso R A.a).inv ≫ K.map (InputGeometry.forget R A.a)) ≫
        K.map ((PolynomialComparison.ordinary R).map j) ≫ K.map W.str := by simp only [CategoryTheory.Category.assoc]
    _ = (InputGeometry.forget (interpretedRules R) ((overFunctor R).obj A.a) ≫
        (ordinaryObjectIso R A.a.left).inv) ≫
        K.map ((PolynomialComparison.ordinary R).map j) ≫ K.map W.str :=
      congrArg (fun k => k ≫ K.map ((PolynomialComparison.ordinary R).map j) ≫ K.map W.str) hf
    _ = InputGeometry.forget (interpretedRules R) ((overFunctor R).obj A.a) ≫
        (PolynomialComparison.ordinary (interpretedRules R)).map (K.map j) ≫
          ((ordinaryObjectIso R W.a).inv ≫ K.map W.str) := by
      simpa only [CategoryTheory.Category.assoc] using
        congrArg (fun f => InputGeometry.forget (interpretedRules R) ((overFunctor R).obj A.a) ≫
          f ≫ K.map W.str) hn
    _ = _ := rfl
end MappedTree

namespace TreeComparison
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)

theorem postcompose
    (A : Endofunctor.Algebra R.inference)
    (W W' : Endofunctor.Algebra (PolynomialComparison.ordinary R))
    (j : A.a.left ⟶ W.a)
    (hj : A.str.left ≫ j = InputGeometry.forget R A.a ≫
      (PolynomialComparison.ordinary R).map j ≫ W.str) (e : W ≅ W') :
    A.str.left ≫ (j ≫ e.hom.f) = InputGeometry.forget R A.a ≫
      (PolynomialComparison.ordinary R).map (j ≫ e.hom.f) ≫ W'.str := by
  rw [← CategoryTheory.Category.assoc,hj,CategoryTheory.Category.assoc,CategoryTheory.Category.assoc,← e.hom.h]
  simp only [CategoryTheory.Functor.map_comp,CategoryTheory.Category.assoc]
end TreeComparison

section Actual
variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

theorem mappedDerivation_tree :
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).str.left ≫ sourceTreeMap R =
      InputGeometry.forget (interpretedRules R)
        (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).a ≫
      (PolynomialComparison.ordinary (interpretedRules R)).map (sourceTreeMap R) ≫
        (NumericalDerivation.ordinaryTree (interpretedRules R)).str :=
  TreeComparison.postcompose (interpretedRules R)
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R))
    (mappedOrdinaryAlgebra R (SyntacticDerivation.ordinaryTree 𝗣𝗔 R))
    (NumericalDerivation.ordinaryTree (interpretedRules R))
    (K.map (SyntacticDerivation.treeInclusion 𝗣𝗔 R))
    (mapped_tree R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)
      (SyntacticDerivation.ordinaryTree 𝗣𝗔 R) (SyntacticDerivation.treeInclusion 𝗣𝗔 R)
      (SyntacticDerivation.derivationConstructor_tree 𝗣𝗔 R)) (sourceOrdinaryIso R)

/-- The actual comparison preserves every inference constructor in the
original formula slice; all morphisms are included in its universal property. -/
def interpretationAlgebraIso :
    NumericalDerivation.codeAlgebra (interpretedRules R) ≅
      mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R) :=
  TreeComparison.ofTree (interpretedRules R)
    (NumericalDerivation.ordinaryTree (interpretedRules R))
    (NumericalDerivation.codeAlgebra (interpretedRules R))
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R))
    (NumericalDerivation.codeTreeInclusion (interpretedRules R)) (sourceTreeMap R)
    (NumericalDerivation.code_constructor_tree (interpretedRules R)) (mappedDerivation_tree R)
    (interpretationOverIso R) (interpretationCarrierIso_tree R)

/-- Original PA derivation carrier, actual numerical successful-tree carrier. -/
def interpretationCodeIso : NumericalDerivation.codeObject (interpretedRules R) ≅
    K.obj (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.left := interpretationCarrierIso R

@[reassoc] theorem interpretationCodeIso_conclusion :
    (interpretationCodeIso R).hom ≫ K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom =
      NumericalDerivation.codeConclusion (interpretedRules R) := interpretationCarrierIso_conclusion R

@[reassoc] theorem interpretationCodeIso_inverse_conclusion :
    (interpretationCodeIso R).inv ≫ NumericalDerivation.codeConclusion (interpretedRules R) =
      K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom := by
  apply (cancel_epi (interpretationCodeIso R).hom).mp
  rw [Iso.hom_inv_id_assoc,interpretationCodeIso_conclusion]


abbrev interpretationCodeIso_constructor :=
  TreeComparison.ofTree_constructor (interpretedRules R)
    (NumericalDerivation.ordinaryTree (interpretedRules R))
    (NumericalDerivation.codeAlgebra (interpretedRules R))
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R))
    (NumericalDerivation.codeTreeInclusion (interpretedRules R)) (sourceTreeMap R)
    (NumericalDerivation.code_constructor_tree (interpretedRules R)) (mappedDerivation_tree R)
    (interpretationOverIso R) (interpretationCarrierIso_tree R)

def mappedDerivationInitial :
    IsInitial (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)) :=
  (NumericalDerivation.codeInitial (interpretedRules R)).ofIso (interpretationAlgebraIso R)

def interpretedDerivationFold
    (B : Endofunctor.Algebra (interpretedRules R).inference) :
    mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R) ⟶ B :=
  (mappedDerivationInitial R).to B

theorem interpretedDerivationFold_conclusion
    (B : Endofunctor.Algebra (interpretedRules R).inference) :
    (interpretedDerivationFold R B).f.left ≫ B.a.hom =
      K.map (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R).a.hom :=
  Over.w (interpretedDerivationFold R B).f

theorem interpretedDerivationFold_constructor
    (B : Endofunctor.Algebra (interpretedRules R).inference) :
    (mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R)).str ≫
        (interpretedDerivationFold R B).f =
      (interpretedRules R).inference.map (interpretedDerivationFold R B).f ≫ B.str :=
  (interpretedDerivationFold R B).h.symm

theorem interpretedDerivationFold_unique
    (B : Endofunctor.Algebra (interpretedRules R).inference)
    (f : mappedAlgebra R (SyntacticDerivation.derivationAlgebra 𝗣𝗔 R) ⟶ B) :
    f = interpretedDerivationFold R B := (mappedDerivationInitial R).hom_ext f _
end Actual
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
