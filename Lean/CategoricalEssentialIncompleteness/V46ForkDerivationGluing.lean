/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationAlgebra
public import CategoricalEssentialIncompleteness.V46ForkDerivationComponents

/-! # Compatible constructors and folds on the original proof fork -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

theorem pointwiseAlgebra_naturality (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    Naturality.AlgebraNaturality
      (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (pointwiseAlgebra a b j) (pointwiseAlgebra a b k)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
      ((componentTransition g).app (proofObject a b)) (componentOver_transition (proofSlice a b) g) :=
  Naturality.algebraNaturalityOfIso
    (componentSupport_re j a) (componentSupport_re j b)
    (componentSupport_re k a) (componentSupport_re k b)
    (pointwiseAlgebraIso a b j) (pointwiseAlgebraIso a b k)
    (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
    ((componentTransition g).app (proofObject a b))
    (Naturality.proofMap (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b))
    (componentOver_transition (proofSlice a b) g)
    (Naturality.proofMap_conclusion (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b))
    (component_proof_transition a b g)
    (Naturality.native_algebra_naturality
      (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b))

/-- The original proof constructors form a total fork morphism.
Their naturality is proved on the selected valid input decomposition. -/
theorem constructorComponents_natural (a b : Idem EffectiveFork.V)
    {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app ((rules a b).inference.obj (proofSlice a b)).left ≫
        constructorComponent a b k =
      constructorComponent a b j ≫ (componentTransition g).app (proofObject a b) := by
  apply NumericalTuples.Map.ext
  funext x
  let u := (componentInputIso a b (proofSlice a b) j).hom.toFun x
  obtain ⟨n,hn⟩ := Component.nodeInput_surjective (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b) (componentOver (proofSlice a b) j) u
  have hi := congrArg (fun f => f.toFun x) (componentInputIso_transition a b (proofSlice a b) g)
  have hm := componentInputTransition_node a b (proofSlice a b) g n
  have hv := hi.trans ((congrArg (componentInputTransition a b (proofSlice a b) g).toFun hn.symm).trans hm)
  have hs := Naturality.node_natural
    (componentSupport_re j a) (componentSupport_re j b)
    (componentSupport_re k a) (componentSupport_re k b)
    (pointwiseAlgebra a b j) (pointwiseAlgebra a b k)
    (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
    ((componentTransition g).app (proofObject a b)) (componentOver_transition (proofSlice a b) g)
    (pointwiseAlgebra_naturality a b g) n
  exact (congrArg (pointwiseAlgebra a b k).str.left.toFun hv).trans
    (hs.symm.trans (congrArg
      (fun v => ((componentTransition g).app (proofObject a b)).toFun
        ((pointwiseAlgebra a b j).str.left.toFun v)) hn))

/-- Every supplied global inference algebra has a compatible family of
component folds. The target operations are arbitrary carrier-total maps. -/
theorem foldComponents_natural (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app (proofObject a b) ≫ foldedComponent a b B k =
      foldedComponent a b B j ≫ (componentTransition g).app B.a.left := by
  have hn := Naturality.fold_natural
    (componentSupport_re j a) (componentSupport_re j b)
    (componentSupport_re k a) (componentSupport_re k b)
    (componentAlgebra a b B j) (componentAlgebra a b B k)
    (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
    ((componentTransition g).app B.a.left) (componentOver_transition B.a g)
    (componentAlgebra_naturality a b B g)
  calc
    _ = (componentTransition g).app (proofObject a b) ≫
        ((componentProofIso a b k).hom ≫
          Naturality.fold (componentSupport k a) (componentSupport k b)
            (componentSupport_re k a) (componentSupport_re k b) (componentAlgebra a b B k)) := by
      rw [foldedComponent_eq_native]
    _ = ((componentProofIso a b j).hom ≫ Naturality.proofMap
        (componentSupport_re j a) (componentSupport_re j b)
        (componentSupport_re k a) (componentSupport_re k b)
        (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)) ≫
          Naturality.fold (componentSupport k a) (componentSupport k b)
            (componentSupport_re k a) (componentSupport_re k b) (componentAlgebra a b B k) := by
      rw [← Category.assoc,component_proof_transition]
    _ = (componentProofIso a b j).hom ≫
        (Naturality.fold (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b) (componentAlgebra a b B j) ≫
            (componentTransition g).app B.a.left) := by rw [Category.assoc,← hn]
    _ = _ := by rw [← Category.assoc,← foldedComponent_eq_native]

end CategoricalEssentialIncompleteness.V46.ForkDerivation
