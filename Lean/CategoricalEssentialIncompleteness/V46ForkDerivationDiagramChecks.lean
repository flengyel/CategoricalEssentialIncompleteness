import CategoricalEssentialIncompleteness.V46ForkDerivationDiagram
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Diagram.Checks

example : EffectiveFork.Total ≌ (WalkingSpan ⥤ NumericalTuples.Object) := equivalence
example (X : EffectiveFork.Total) (j : WalkingSpan) :
    (realization.obj X).obj j = (componentFunctor j).obj X := rfl
example {X Y : EffectiveFork.Total} (f : X ⟶ Y) (j : WalkingSpan) :
    (realization.map f).app j = (componentFunctor j).map f := rfl
example (a b : Idem EffectiveFork.V) :
    (rules a b).instances 0 = realization.obj (axiomObject a b) := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).instances 1 = ⊥_ Object := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).instances 2 = (sentences ⨯ sentences) := rfl
example (a b : Idem EffectiveFork.V) :
    (rules a b).premises 2 = prod.lift prod.fst implication := rfl
example (a b : Idem EffectiveFork.V) :
    (rules a b).conclusion 0 = realization.map (ForkDerivation.lambda a b) := rfl
example (a b : Idem EffectiveFork.V) : (rules a b).conclusion 2 = prod.snd := rfl
example (a b : Idem EffectiveFork.V) :
    (∐ fun i => realization.obj (axiomCoefficients a b i)) ≅ axioms a b := axiomCoproductIso a b
example (a b : Idem EffectiveFork.V) : coefficientShape a b =
    ![sentences ⨯ sentences,(sentences ⨯ sentences) ⨯ sentences,sentences ⨯ sentences,
      realization.obj (axiomDomain a),realization.obj (axiomDomain b)] := rfl
example (a b : Idem EffectiveFork.V) : axioms a b ≅ ∐ coefficientShape a b := axiomShapeIso a b
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeIso a b 0).hom = prodComparison realization sentenceObject sentenceObject := rfl
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeIso a b 1).hom =
      prodComparison realization (sentenceObject ⨯ sentenceObject) sentenceObject ≫
        prod.map (prodComparison realization sentenceObject sentenceObject) (𝟙 _) := rfl
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeIso a b 3).hom = 𝟙 (realization.obj (axiomDomain a)) := rfl
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeIso a b 4).hom = 𝟙 (realization.obj (axiomDomain b)) := rfl
example (a b : Idem EffectiveFork.V) (i : Fin 5) :
    Sigma.ι (fun i => realization.obj (axiomCoefficients a b i)) i ≫
        (axiomCoproductIso a b).hom ≫ lambda a b =
      realization.map (axiomConclusions a b i) := axiomCoproductIso_conclusion a b i
example (a b : Idem EffectiveFork.V) (i : Fin 5) :
    realization.map (Sigma.ι (axiomCoefficients a b) i) ≫ (axiomShapeIso a b).hom =
      (coefficientShapeIso a b i).hom ≫ Sigma.ι (coefficientShape a b) i := axiomShapeIso_branch a b i
example (a b : Idem EffectiveFork.V) (i : Fin 5) :
    Sigma.ι (coefficientShape a b) i ≫ shapedLambda a b =
      (coefficientShapeIso a b i).inv ≫ realization.map (axiomConclusions a b i) := shapedLambda_branch a b i
example (a b : Idem EffectiveFork.V) :
    (axiomShapeIso a b).hom ≫ shapedLambda a b = lambda a b := axiomShapeIso_conclusion a b
example (a b : Idem EffectiveFork.V) :
    (axiomShapeIso a b).inv ≫ lambda a b = shapedLambda a b := axiomShapeIso_inverse_conclusion a b
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeConclusion a b 0) =
      inv (prodComparison realization sentenceObject sentenceObject) ≫
        realization.map ForkDerivation.H1 := rfl
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeConclusion a b 3) =
      (𝟙 (realization.obj (axiomDomain a))) ≫
        realization.map (axiomInclusion a ≫ atom) := rfl
example (a b : Idem EffectiveFork.V) :
    (coefficientShapeConclusion a b 4) =
      (𝟙 (realization.obj (axiomDomain b))) ≫
        realization.map (axiomInclusion b ≫ atom ≫ negation) := rfl
example (a b : Idem EffectiveFork.V) :
    (ForkDerivation.rules a b).inference ⋙ sliceEquivalence.functor ≅
      sliceEquivalence.functor ⋙ (rules a b).inference := inferenceComparison a b
example (a b : Idem EffectiveFork.V) (i : Fin 3) :
    realization.map ((ForkDerivation.rules a b).premises i) ≫
      (ArithmeticIndexedFibers.InferenceTransport.power equivalence sentenceObject i.val).hom =
        ((transportData a b).coefficient i).hom ≫ (rules a b).premises i := (transportData a b).premises i
example (a b : Idem EffectiveFork.V) (i : Fin 3) :
    realization.map ((ForkDerivation.rules a b).conclusion i) =
      ((transportData a b).coefficient i).hom ≫ (rules a b).conclusion i := (transportData a b).conclusion i
example (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (i : Fin 3) :
    (ruleInputIso a b Q i).hom ≫ pullback.fst _ _ =
      realization.map (pullback.fst ((ForkDerivation.rules a b).premises i)
        (finitePowerMap Q.hom i.val)) ≫ (coefficientIso a b i).hom := ruleInputIso_label a b Q i
example (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (i : Fin 3) :
    (ruleInputIso a b Q i).hom ≫ pullback.snd _ _ =
      realization.map (pullback.snd ((ForkDerivation.rules a b).premises i)
        (finitePowerMap Q.hom i.val)) ≫
          (ArithmeticIndexedFibers.InferenceTransport.power equivalence Q.left i.val).hom := ruleInputIso_children a b Q i
example (a b : Idem EffectiveFork.V) : IsInitial (inferenceAlgebra a b) := inferenceInitial a b
example (a b : Idem EffectiveFork.V) : IsInitial (printedAlgebra a b) := printedInitial a b
example (a b : Idem EffectiveFork.V) (i : Fin 3) :
    (ruleInputIso a b (proofSlice a b) i).hom ≫
        Sigma.ι ((rules a b).ruleObject (inferenceAlgebra a b).a) i ≫
          (inferenceAlgebra a b).str.left =
      realization.map (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i ≫
        (ForkDerivation.inferenceAlgebra a b).str.left) := inference_constructor_branch a b i
example (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).a.left = realization.obj (proofObject a b) := rfl
example (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) := rfl
example (a b : Idem EffectiveFork.V) (Q : WalkingSpan ⥤ NumericalTuples.Object)
    (q : Q ⟶ sentences) (η : (printedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : Over.mk (realization.map (ForkDerivation.conclusion a b)) ⟶ Over.mk q,
      (printedH a b).map u ≫ η = (printedAlgebra a b).str ≫ u := printed_unique a b Q q η

example (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    ((shapedH a b).obj Q).left = ((∐ coefficientShape a b) ⨿
      pullback (prod.lift prod.fst implication) (prod.map Q.hom Q.hom)) := rfl
example (a b : Idem EffectiveFork.V) : printedH a b ≅ shapedH a b := shapedInferenceIso a b
example (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inl ≫ (shapedInputIso a b Q).hom.left =
      (axiomShapeIso a b).hom ≫ coprod.inl := shapedInputIso_axiom a b Q
example (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inr ≫ (shapedInputIso a b Q).hom.left = coprod.inr := shapedInputIso_mp a b Q
example (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inl ≫ (shapedInputIso a b Q).inv.left =
      (axiomShapeIso a b).inv ≫ coprod.inl := shapedInputIso_inverse_axiom a b Q
example (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inr ≫ (shapedInputIso a b Q).inv.left = coprod.inr := shapedInputIso_inverse_mp a b Q
example (a b : Idem EffectiveFork.V) : IsInitial (shapedAlgebra a b) := shapedInitial a b
example (a b : Idem EffectiveFork.V) :
    (shapedAlgebra a b).a.left = realization.obj (proofObject a b) := rfl
example (a b : Idem EffectiveFork.V) :
    (shapedAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) := rfl
example (a b : Idem EffectiveFork.V) :
    (shapedInputIso a b (printedAlgebra a b).a).hom ≫ (shapedAlgebra a b).str =
      (printedAlgebra a b).str := shaped_constructor a b
example (a b : Idem EffectiveFork.V) (Q : WalkingSpan ⥤ NumericalTuples.Object)
    (q : Q ⟶ sentences) (η : (shapedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : Over.mk (realization.map (ForkDerivation.conclusion a b)) ⟶ Over.mk q,
      (shapedH a b).map u ≫ η = (shapedAlgebra a b).str ≫ u := shaped_unique a b Q q η
end CategoricalEssentialIncompleteness.V46.ForkDerivation.Diagram.Checks
