/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationInitial
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersTransport
public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps
public import Mathlib.Tactic.FinCases

/-! # The derivation universal property in the numerical diagram category

The explicit unary equivalence retains the old scalar proof and formula
coordinates. The existing generic inference transport constructs the
premise-pullback and algebra comparisons from the coefficient diagrams.
-/

@[expose] public section
noncomputable section
universe u₁ u₂ v₁ v₂
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Diagram

abbrev Object := WalkingSpan ⥤ NumericalTuples.Object

/-- This equivalence uses the explicit unary program, rather than an
unspecified inverse presentation of each numerical object. -/
def equivalence : EffectiveFork.Total ≌ Object :=
  EffectiveFork.totalEquivalence.trans
    (Naturality.unaryFunctor.asEquivalence.congrRight (E := WalkingSpan))

abbrev realization := equivalence.functor

@[simp] theorem realization_obj_component (X : EffectiveFork.Total) (j : WalkingSpan) :
    (realization.obj X).obj j = (componentFunctor j).obj X := rfl

@[simp] theorem realization_map_component {X Y : EffectiveFork.Total} (f : X ⟶ Y)
    (j : WalkingSpan) : (realization.map f).app j = (componentFunctor j).map f := rfl

def sentences : Object := realization.obj sentenceObject
def axioms (a b : Idem EffectiveFork.V) : Object := realization.obj (axiomObject a b)
def lambda (a b : Idem EffectiveFork.V) : axioms a b ⟶ sentences :=
  realization.map (ForkDerivation.lambda a b)
def implication : sentences ⨯ sentences ⟶ sentences :=
  inv (prodComparison realization sentenceObject sentenceObject) ≫
    realization.map ForkDerivation.implication

def rules (a b : Idem EffectiveFork.V) : RulePresentation sentences 2 :=
  ForkInference.rules (lambda a b) implication

def printedH (a b : Idem EffectiveFork.V) : Over sentences ⥤ Over sentences :=
  ForkInference.printedH (lambda a b) implication

def axiomCoproductIso (a b : Idem EffectiveFork.V) :
    (∐ fun i => realization.obj (axiomCoefficients a b i)) ≅ axioms a b :=
  asIso (sigmaComparison realization (axiomCoefficients a b))

def coefficientShape (a b : Idem EffectiveFork.V) : Fin 5 → Object :=
  ![sentences ⨯ sentences,(sentences ⨯ sentences) ⨯ sentences,sentences ⨯ sentences,
    realization.obj (axiomDomain a),realization.obj (axiomDomain b)]

/-- In particular the three logical parameter objects are the displayed
ordered powers, and the two atomic predicates are unchanged images. -/
def coefficientShapeIso (a b : Idem EffectiveFork.V) :
    ∀ i, realization.obj (axiomCoefficients a b i) ≅ coefficientShape a b i :=
  Fin.cases (asIso (prodComparison realization sentenceObject sentenceObject))
    (Fin.cases
      (asIso (prodComparison realization (sentenceObject ⨯ sentenceObject) sentenceObject) ≪≫
        prod.mapIso (asIso (prodComparison realization sentenceObject sentenceObject)) (Iso.refl _))
      (Fin.cases (asIso (prodComparison realization sentenceObject sentenceObject))
        (Fin.cases (Iso.refl _) (Fin.cases (Iso.refl _) (fun i => Fin.elim0 i)))))

def axiomShapeIso (a b : Idem EffectiveFork.V) : axioms a b ≅ ∐ coefficientShape a b :=
  (axiomCoproductIso a b).symm ≪≫ Sigma.mapIso (coefficientShapeIso a b)

/-- Each displayed parameter object is related by its ordered product comparison to the
mapped source coefficient. -/
def coefficientShapeConclusion (a b : Idem EffectiveFork.V) (i : Fin 5) :
    coefficientShape a b i ⟶ sentences :=
  (coefficientShapeIso a b i).inv ≫ realization.map (axiomConclusions a b i)

def shapedLambda (a b : Idem EffectiveFork.V) : (∐ coefficientShape a b) ⟶ sentences :=
  Sigma.desc (coefficientShapeConclusion a b)

@[reassoc] theorem shapedLambda_branch (a b : Idem EffectiveFork.V) (i : Fin 5) :
    Sigma.ι (coefficientShape a b) i ≫ shapedLambda a b =
      (coefficientShapeIso a b i).inv ≫ realization.map (axiomConclusions a b i) :=
  Sigma.ι_comp_desc (coefficientShapeConclusion a b) i

@[reassoc] theorem coefficientShape_conclusion (a b : Idem EffectiveFork.V) (i : Fin 5) :
    (coefficientShapeIso a b i).hom ≫ coefficientShapeConclusion a b i =
      realization.map (axiomConclusions a b i) := by
  simp only [coefficientShapeConclusion,← Category.assoc,Iso.hom_inv_id,Category.id_comp]

@[reassoc] theorem axiomShapeIso_branch (a b : Idem EffectiveFork.V) (i : Fin 5) :
    realization.map (Sigma.ι (axiomCoefficients a b) i) ≫ (axiomShapeIso a b).hom =
      (coefficientShapeIso a b i).hom ≫ Sigma.ι (coefficientShape a b) i := by
  simp only [axiomShapeIso,axiomCoproductIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

@[reassoc] theorem axiomCoproductIso_conclusion (a b : Idem EffectiveFork.V) (i : Fin 5) :
    Sigma.ι (fun i => realization.obj (axiomCoefficients a b i)) i ≫
        (axiomCoproductIso a b).hom ≫ lambda a b =
      realization.map (axiomConclusions a b i) := by
  rw [axiomCoproductIso,asIso_hom,ι_comp_sigmaComparison_assoc,lambda,
    ← CategoryTheory.Functor.map_comp]
  exact congrArg realization.map (Sigma.ι_comp_desc (axiomConclusions a b) i)

/-- The finite coproduct comparison preserves λ, rather than merely
identifying its underlying coefficient carrier. -/
theorem axiomShapeIso_conclusion (a b : Idem EffectiveFork.V) :
    (axiomShapeIso a b).hom ≫ shapedLambda a b = lambda a b := by
  apply (cancel_epi (axiomCoproductIso a b).hom).mp
  apply Sigma.hom_ext
  intro i
  calc
    _ = (coefficientShapeIso a b i).hom ≫
        Sigma.ι (coefficientShape a b) i ≫ shapedLambda a b := by
      simp only [axiomShapeIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
        Iso.hom_inv_id_assoc,Sigma.ι_mapIso_hom_assoc]
    _ = (coefficientShapeIso a b i).hom ≫ coefficientShapeConclusion a b i := by
      rw [shapedLambda_branch]
      rfl
    _ = realization.map (axiomConclusions a b i) := coefficientShape_conclusion a b i
    _ = _ := (axiomCoproductIso_conclusion a b i).symm

theorem axiomShapeIso_inverse_conclusion (a b : Idem EffectiveFork.V) :
    (axiomShapeIso a b).inv ≫ lambda a b = shapedLambda a b := by
  rw [← axiomShapeIso_conclusion]
  simp only [← Category.assoc,Iso.inv_hom_id,Category.id_comp]

def coefficientIso (a b : Idem EffectiveFork.V) :
    ∀ i, realization.obj ((ForkDerivation.rules a b).instances i) ≅ (rules a b).instances i :=
  Fin.cases (Iso.refl _)
    (Fin.cases (asIso (initialComparison realization)).symm
      (Fin.cases (asIso (prodComparison realization sentenceObject sentenceObject))
        (fun i => Fin.elim0 i)))

private theorem map_binary_premise {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D] [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) (S : C) (m : S ⨯ S ⟶ S) [IsIso (prodComparison F S S)] :
    F.map (prod.lift (prod.fst : S ⨯ S ⟶ S) m) ≫ prodComparison F S S =
      prodComparison F S S ≫ prod.lift
        (prod.fst : F.obj S ⨯ F.obj S ⟶ F.obj S)
        (inv (prodComparison F S S) ≫ F.map m) := by
  apply prod.hom_ext
  · rw [Category.assoc,prodComparison_fst,← CategoryTheory.Functor.map_comp,prod.lift_fst,
      Category.assoc,prod.lift_fst,prodComparison_fst]
  · rw [Category.assoc,prodComparison_snd,← CategoryTheory.Functor.map_comp,prod.lift_snd,
      Category.assoc,prod.lift_snd,← Category.assoc,IsIso.hom_inv_id,Category.id_comp]

private theorem power_two :
    (ArithmeticIndexedFibers.InferenceTransport.power equivalence sentenceObject 2).hom =
      prodComparison realization sentenceObject sentenceObject := by
  change prodComparison realization sentenceObject sentenceObject ≫
    prod.map (𝟙 (realization.obj sentenceObject)) (𝟙 (realization.obj sentenceObject)) = _
  rw [prod.map_id_id,Category.comp_id]

theorem coefficient_premises (a b : Idem EffectiveFork.V) (i : Fin 3) :
    realization.map ((ForkDerivation.rules a b).premises i) ≫
        (ArithmeticIndexedFibers.InferenceTransport.power equivalence sentenceObject i.val).hom =
      (coefficientIso a b i).hom ≫ (rules a b).premises i := by
  fin_cases i
  · exact terminal.hom_ext _ _
  · exact (IsInitial.isInitialObj realization (⊥_ EffectiveFork.Total) initialIsInitial).hom_ext _ _
  · change realization.map (prod.lift prod.fst ForkDerivation.implication) ≫
        (ArithmeticIndexedFibers.InferenceTransport.power equivalence sentenceObject 2).hom =
      prodComparison realization sentenceObject sentenceObject ≫ prod.lift prod.fst implication
    rw [power_two]
    exact map_binary_premise realization sentenceObject ForkDerivation.implication

theorem coefficient_conclusion (a b : Idem EffectiveFork.V) (i : Fin 3) :
    realization.map ((ForkDerivation.rules a b).conclusion i) =
      (coefficientIso a b i).hom ≫ (rules a b).conclusion i := by
  fin_cases i
  · exact (Category.id_comp _).symm
  · exact (IsInitial.isInitialObj realization (⊥_ EffectiveFork.Total) initialIsInitial).hom_ext _ _
  · exact (prodComparison_snd realization sentenceObject sentenceObject).symm

/-- Every field is a coefficient or premise/conclusion comparison. -/
def transportData (a b : Idem EffectiveFork.V) :
    ArithmeticIndexedFibers.InferenceTransport.Data equivalence (ForkDerivation.rules a b) (rules a b) where
  coefficient := coefficientIso a b
  premises := coefficient_premises a b
  conclusion := coefficient_conclusion a b

abbrev sliceEquivalence : Over sentenceObject ≌ Over sentences :=
  Over.postEquiv sentenceObject equivalence

def inferenceComparison (a b : Idem EffectiveFork.V) :
    (ForkDerivation.rules a b).inference ⋙ sliceEquivalence.functor ≅
      sliceEquivalence.functor ⋙ (rules a b).inference :=
  ArithmeticIndexedFibers.InferenceTransport.comparison equivalence
    (ForkDerivation.rules a b) (rules a b) (transportData a b)

def inferenceAlgebra (a b : Idem EffectiveFork.V) : Endofunctor.Algebra (rules a b).inference :=
  AlgebraTransport.mappedAlgebra sliceEquivalence (inferenceComparison a b)
    (ForkDerivation.inferenceAlgebra a b)

def inferenceInitial (a b : Idem EffectiveFork.V) : IsInitial (inferenceAlgebra a b) :=
  AlgebraTransport.initial sliceEquivalence (inferenceComparison a b)
    (ForkDerivation.inferenceAlgebra a b) (ForkDerivation.inferenceInitial a b)

@[simp] theorem inference_carrier (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a.left = realization.obj (proofObject a b) := rfl

@[simp] theorem inference_conclusion (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) := rfl

theorem inference_constructor (a b : Idem EffectiveFork.V) :
    (inferenceAlgebra a b).str = (inferenceComparison a b).inv.app (proofSlice a b) ≫
      sliceEquivalence.functor.map (ForkDerivation.inferenceAlgebra a b).str := rfl

/-- Every mapped root injection is sent to its same arity branch, by
the proved original premise pullback comparison. -/
def ruleInputIso (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (i : Fin 3) :
    realization.obj ((ForkDerivation.rules a b).ruleObject Q i) ≅
      (rules a b).ruleObject (sliceEquivalence.functor.obj Q) i :=
  ArithmeticIndexedFibers.InferenceTransport.inputIso equivalence
    (ForkDerivation.rules a b) (rules a b) (transportData a b) Q i

@[reassoc] theorem ruleInputIso_label (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (i : Fin 3) :
    (ruleInputIso a b Q i).hom ≫ pullback.fst _ _ =
      realization.map (pullback.fst ((ForkDerivation.rules a b).premises i)
        (finitePowerMap Q.hom i.val)) ≫ (coefficientIso a b i).hom :=
  ArithmeticIndexedFibers.InferenceTransport.inputIso_fst equivalence
    (ForkDerivation.rules a b) (rules a b) (transportData a b) Q i

@[reassoc] theorem ruleInputIso_children (a b : Idem EffectiveFork.V)
    (Q : Over sentenceObject) (i : Fin 3) :
    (ruleInputIso a b Q i).hom ≫ pullback.snd _ _ =
      realization.map (pullback.snd ((ForkDerivation.rules a b).premises i)
        (finitePowerMap Q.hom i.val)) ≫
          (ArithmeticIndexedFibers.InferenceTransport.power equivalence Q.left i.val).hom :=
  ArithmeticIndexedFibers.InferenceTransport.inputIso_snd equivalence
    (ForkDerivation.rules a b) (rules a b) (transportData a b) Q i

theorem inference_constructor_branch (a b : Idem EffectiveFork.V) (i : Fin 3) :
    (ruleInputIso a b (proofSlice a b) i).hom ≫
        Sigma.ι ((rules a b).ruleObject (inferenceAlgebra a b).a) i ≫
          (inferenceAlgebra a b).str.left =
      realization.map (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i ≫
        (ForkDerivation.inferenceAlgebra a b).str.left) := by
  have hs := ArithmeticIndexedFibers.InferenceTransport.sumIso_iota equivalence
    (ForkDerivation.rules a b) (rules a b) (transportData a b) (proofSlice a b) i
  change realization.map (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i) ≫
      (ArithmeticIndexedFibers.InferenceTransport.sumIso equivalence
        (ForkDerivation.rules a b) (rules a b) (transportData a b) (proofSlice a b)).hom =
    (ruleInputIso a b (proofSlice a b) i).hom ≫
      Sigma.ι ((rules a b).ruleObject (inferenceAlgebra a b).a) i at hs
  have hstructure : (inferenceComparison a b).hom.app (proofSlice a b) ≫
      (inferenceAlgebra a b).str =
        sliceEquivalence.functor.map (ForkDerivation.inferenceAlgebra a b).str := by
    rw [inference_constructor,← Category.assoc,Iso.hom_inv_id_app,Category.id_comp]
  calc
    _ = realization.map (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i) ≫
        (ArithmeticIndexedFibers.InferenceTransport.sumIso equivalence
          (ForkDerivation.rules a b) (rules a b) (transportData a b) (proofSlice a b)).hom ≫
            (inferenceAlgebra a b).str.left := by
      simpa only [Category.assoc] using
        (congrArg (fun k => k ≫ (inferenceAlgebra a b).str.left) hs).symm
    _ = realization.map (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i) ≫
        realization.map (ForkDerivation.inferenceAlgebra a b).str.left := by
      exact congrArg (fun k => realization.map
        (Sigma.ι ((ForkDerivation.rules a b).ruleObject (proofSlice a b)) i) ≫ k.left) hstructure
    _ = _ := (CategoryTheory.Functor.map_comp realization _ _).symm

def printedComparison (a b : Idem EffectiveFork.V) :
    (rules a b).inference ⋙ 𝟭 (Over sentences) ≅ 𝟭 (Over sentences) ⋙ printedH a b :=
  CategoryTheory.Functor.rightUnitor (rules a b).inference ≪≫ ForkInference.inferenceIso (lambda a b) implication ≪≫
    (CategoryTheory.Functor.leftUnitor (printedH a b)).symm

def printedAlgebra (a b : Idem EffectiveFork.V) : Endofunctor.Algebra (printedH a b) :=
  AlgebraTransport.mappedAlgebra (CategoryTheory.Equivalence.refl (C := Over sentences))
    (printedComparison a b) (inferenceAlgebra a b)

def printedInitial (a b : Idem EffectiveFork.V) : IsInitial (printedAlgebra a b) :=
  AlgebraTransport.initial (CategoryTheory.Equivalence.refl (C := Over sentences))
    (printedComparison a b) (inferenceAlgebra a b) (inferenceInitial a b)

@[simp] theorem printed_carrier (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).a.left = realization.obj (proofObject a b) := rfl

@[simp] theorem printed_conclusion (a b : Idem EffectiveFork.V) :
    (printedAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) := rfl

/-- The universal property in the literal diagram category, for every
natural computable target operation on arbitrary carriers. -/
theorem printed_unique (a b : Idem EffectiveFork.V) (Q : Object) (q : Q ⟶ sentences)
    (η : (printedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : Over.mk (realization.map (ForkDerivation.conclusion a b)) ⟶ Over.mk q,
      (printedH a b).map u ≫ η = (printedAlgebra a b).str ≫ u := by
  let B : Endofunctor.Algebra (printedH a b) := ⟨Over.mk q,η⟩
  let m := (printedInitial a b).to B
  refine ⟨m.f,m.h,?_⟩
  intro u hu
  exact congrArg Endofunctor.Algebra.Hom.f
    ((printedInitial a b).hom_ext (⟨u,hu⟩ : printedAlgebra a b ⟶ B) m)

/-- The displayed H uses the explicit ordered powers and the two
unchanged atom predicates in its Fin5 coefficient object. -/
def shapedH (a b : Idem EffectiveFork.V) : Over sentences ⥤ Over sentences :=
  ForkInference.printedH (shapedLambda a b) implication

def shapedInputIso (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    (printedH a b).obj Q ≅ (shapedH a b).obj Q :=
  Over.isoMk (coprod.mapIso (axiomShapeIso a b) (Iso.refl _)) (by
    change coprod.map (axiomShapeIso a b).hom (𝟙 _) ≫
      coprod.desc (shapedLambda a b) (ForkInference.mpConclusion implication Q) =
        coprod.desc (lambda a b) (ForkInference.mpConclusion implication Q)
    apply coprod.hom_ext
    · simp only [coprod.inl_map_assoc,coprod.inl_desc]
      exact axiomShapeIso_conclusion a b
    · simp only [coprod.inr_map_assoc,coprod.inr_desc,Category.id_comp])

/-- This natural isomorphism preserves the axiom constructors and keeps the same matched
ordered MP input. -/
def shapedInferenceIso (a b : Idem EffectiveFork.V) : printedH a b ≅ shapedH a b :=
  NatIso.ofComponents (shapedInputIso a b) (by
    intro Q Q' f
    apply Over.OverMorphism.ext
    change coprod.map (𝟙 (axioms a b)) (ForkInference.mpMap implication f) ≫
        coprod.map (axiomShapeIso a b).hom (𝟙 _) =
      coprod.map (axiomShapeIso a b).hom (𝟙 _) ≫
        coprod.map (𝟙 (∐ coefficientShape a b)) (ForkInference.mpMap implication f)
    simp only [coprod.map_map,Category.id_comp,Category.comp_id])

@[reassoc] theorem shapedInputIso_axiom (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inl ≫ (shapedInputIso a b Q).hom.left =
      (axiomShapeIso a b).hom ≫ coprod.inl := by
  exact coprod.inl_map _ _

@[reassoc] theorem shapedInputIso_mp (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inr ≫ (shapedInputIso a b Q).hom.left = coprod.inr := by
  change coprod.inr ≫ coprod.map (axiomShapeIso a b).hom (𝟙 _) = _
  rw [coprod.inr_map,Category.id_comp]

@[reassoc] theorem shapedInputIso_inverse_axiom (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inl ≫ (shapedInputIso a b Q).inv.left =
      (axiomShapeIso a b).inv ≫ coprod.inl := by
  exact coprod.inl_map _ _

@[reassoc] theorem shapedInputIso_inverse_mp (a b : Idem EffectiveFork.V) (Q : Over sentences) :
    coprod.inr ≫ (shapedInputIso a b Q).inv.left = coprod.inr := by
  change coprod.inr ≫ coprod.map (axiomShapeIso a b).inv (𝟙 _) = _
  rw [coprod.inr_map,Category.id_comp]

def shapedComparison (a b : Idem EffectiveFork.V) :
    printedH a b ⋙ 𝟭 (Over sentences) ≅ 𝟭 (Over sentences) ⋙ shapedH a b :=
  CategoryTheory.Functor.rightUnitor (printedH a b) ≪≫ shapedInferenceIso a b ≪≫
    (CategoryTheory.Functor.leftUnitor (shapedH a b)).symm

/-- Transport changes only the constructor input chart. The conclusion
and old proof carrier in every component are kept verbatim. -/
def shapedAlgebra (a b : Idem EffectiveFork.V) : Endofunctor.Algebra (shapedH a b) :=
  AlgebraTransport.mappedAlgebra (CategoryTheory.Equivalence.refl (C := Over sentences))
    (shapedComparison a b) (printedAlgebra a b)

def shapedInitial (a b : Idem EffectiveFork.V) : IsInitial (shapedAlgebra a b) :=
  AlgebraTransport.initial (CategoryTheory.Equivalence.refl (C := Over sentences))
    (shapedComparison a b) (printedAlgebra a b) (printedInitial a b)

@[simp] theorem shaped_carrier (a b : Idem EffectiveFork.V) :
    (shapedAlgebra a b).a.left = realization.obj (proofObject a b) := rfl

@[simp] theorem shaped_conclusion (a b : Idem EffectiveFork.V) :
    (shapedAlgebra a b).a.hom = realization.map (ForkDerivation.conclusion a b) := rfl

theorem shaped_constructor (a b : Idem EffectiveFork.V) :
    (shapedInputIso a b (printedAlgebra a b).a).hom ≫ (shapedAlgebra a b).str =
      (printedAlgebra a b).str := by
  change (shapedInputIso a b (printedAlgebra a b).a).hom ≫
    ((shapedInputIso a b (printedAlgebra a b).a).inv ≫ (printedAlgebra a b).str) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]

theorem shaped_unique (a b : Idem EffectiveFork.V) (Q : Object) (q : Q ⟶ sentences)
    (η : (shapedH a b).obj (Over.mk q) ⟶ Over.mk q) :
    ∃! u : Over.mk (realization.map (ForkDerivation.conclusion a b)) ⟶ Over.mk q,
      (shapedH a b).map u ≫ η = (shapedAlgebra a b).str ≫ u := by
  let B : Endofunctor.Algebra (shapedH a b) := ⟨Over.mk q,η⟩
  let m := (shapedInitial a b).to B
  refine ⟨m.f,m.h,?_⟩
  intro u hu
  exact congrArg Endofunctor.Algebra.Hom.f
    ((shapedInitial a b).hom_ext (⟨u,hu⟩ : shapedAlgebra a b ⟶ B) m)

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Diagram
