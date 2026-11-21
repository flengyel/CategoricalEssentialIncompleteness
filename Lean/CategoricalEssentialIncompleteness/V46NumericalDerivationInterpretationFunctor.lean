/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationRules
public import CategoricalEssentialIncompleteness.V46NumericalUnderlyingCoproducts

/-! # Preserved inference inputs under the PA numerical functor

The natural isomorphism is derived from the already proved finite powers,
pullbacks and finite coproducts. No equivalence or preservation of initial
algebras is asserted for this functor.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation

instance preservesFiniteCoproducts : PreservesFiniteCoproducts K := by
  let _ : PreservesFiniteCoproducts NumericalUnderlying.functor := ⟨fun _ => inferInstance⟩
  let _ : PreservesFiniteCoproducts (K ⋙ NumericalUnderlying.functor) :=
    { preserves _ := preservesColimitsOfShape_of_natIso NumericalArithmetic.Geometry.standardComparison.symm }
  exact preservesFiniteCoproducts_of_reflects_of_preserves K NumericalUnderlying.functor

variable {F : PredicateCategory 𝗣𝗔} {N : ℕ} (R : RulePresentation F N)

def sumIso (Q : Over F) : K.obj (∐ R.ruleObject Q) ≅
    ∐ (interpretedRules R).ruleObject ((overFunctor R).obj Q) :=
  (asIso (sigmaComparison K (R.ruleObject Q))).symm ≪≫ Sigma.mapIso (inputIso R Q)

@[simp,reassoc] theorem sumIso_iota (Q : Over F) (i : Fin (N+1)) :
    K.map (Sigma.ι (R.ruleObject Q) i) ≫ (sumIso R Q).hom =
      (inputIso R Q i).hom ≫ Sigma.ι ((interpretedRules R).ruleObject ((overFunctor R).obj Q)) i := by
  simp only [sumIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

theorem mapSum_hom_ext {I : Type} [Finite I] (X : I → PredicateCategory 𝗣𝗔) {Y : NumericalTuples.Object}
    (f g : K.obj (∐ X) ⟶ Y)
    (hh : ∀ i, K.map (Sigma.ι X i) ≫ f = K.map (Sigma.ι X i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using hh i

/-- The displayed conclusion equality makes this an isomorphism in the
original formula slice, as required for generated-theory comparison. -/
def overIso (Q : Over F) :
    (overFunctor R).obj (R.inference.obj Q) ≅
      (interpretedRules R).inference.obj ((overFunctor R).obj Q) :=
  Over.isoMk (sumIso R Q) (by
    apply mapSum_hom_ext (R.ruleObject Q)
    intro i
    rw [← Category.assoc,sumIso_iota,Category.assoc]
    change (inputIso R Q i).hom ≫
        Sigma.ι ((interpretedRules R).ruleObject ((overFunctor R).obj Q)) i ≫
          Sigma.desc ((interpretedRules R).ruleConclusion ((overFunctor R).obj Q)) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [Sigma.ι_comp_desc]
    change (inputIso R Q i).hom ≫
        pullback.fst _ _ ≫ (interpretedRules R).conclusion i =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (R.inference.obj Q).hom
    rw [inputIso_fst_assoc]
    change K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        K.map (R.conclusion i) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [← Functor.map_comp]
    change K.map (R.ruleConclusion Q i) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [← Functor.map_comp,Sigma.ι_comp_desc])

private theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N+1)) :
    K.map (R.ruleMap f i) ≫ (inputIso R Q' i).hom =
      (inputIso R Q i).hom ≫ (interpretedRules R).ruleMap ((overFunctor R).map f) i := by
  apply pullback.hom_ext
  · simp only [Category.assoc,inputIso_fst,RulePresentation.ruleMap_fst]
    change K.map (R.ruleMap f i) ≫
        K.map (pullback.fst (R.premises i) (finitePowerMap Q'.hom i.val)) =
      K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val))
    exact (K.map_comp _ _).symm.trans (congrArg K.map (RulePresentation.ruleMap_fst R f i))
  · simp only [Category.assoc,inputIso_snd,RulePresentation.ruleMap_snd]
    rw [← Functor.map_comp_assoc,RulePresentation.ruleMap_snd,Functor.map_comp_assoc,finitePowerIso_natural]
    change K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso Q.left i.val).hom ≫ finitePowerMap (K.map f.left) i.val =
      (inputIso R Q i).hom ≫ pullback.snd _ _ ≫ finitePowerMap (K.map f.left) i.val
    rw [inputIso_snd_assoc]

theorem overIso_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (overFunctor R).map (R.inference.map f) ≫ (overIso R Q').hom =
      (overIso R Q).hom ≫ (interpretedRules R).inference.map ((overFunctor R).map f) := by
  apply Over.OverMorphism.ext
  change K.map (Limits.Sigma.map (R.ruleMap f)) ≫ (sumIso R Q').hom =
    (sumIso R Q).hom ≫ Limits.Sigma.map ((interpretedRules R).ruleMap ((overFunctor R).map f))
  apply mapSum_hom_ext (R.ruleObject Q)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [Sigma.ι_map,Functor.map_comp_assoc,sumIso_iota_assoc]
  rw [sumIso_iota,← Category.assoc,input_natural,Category.assoc]

/-- The endofunctor comparison is proved from preserved finite powers,
rule-input pullbacks and finite coproducts. -/
def comparison : R.inference ⋙ (overFunctor R) ≅
    (overFunctor R) ⋙ (interpretedRules R).inference :=
  NatIso.ofComponents (overIso R) (fun f => overIso_natural R f)

/-- The comparison of inference functors transports a source algebra to the target slice. -/
def mappedAlgebra (A : Endofunctor.Algebra R.inference) :
    Endofunctor.Algebra (interpretedRules R).inference where
  a := (overFunctor R).obj A.a
  str := (comparison R).inv.app A.a ≫ (overFunctor R).map A.str

theorem mappedAlgebra_conclusion (A : Endofunctor.Algebra R.inference) :
    (mappedAlgebra R A).a.hom = K.map A.a.hom := rfl

/-- A rule-labelled ordinary-tree input retains the label and the ordered children under
the arithmetic interpretation. -/
def ordinaryInputIso (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    K.obj (R.instances i ⨯ finitePower X i.val) ≅
      (interpretedRules R).instances i ⨯ finitePower (K.obj X) i.val :=
  asIso (prodComparison K (R.instances i) (finitePower X i.val)) ≪≫
    prod.mapIso (Iso.refl _) (finitePowerIso X i.val)

@[simp,reassoc] theorem ordinaryInputIso_fst (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    (ordinaryInputIso R X i).hom ≫ prod.fst = K.map prod.fst := by
  simp [ordinaryInputIso]

@[simp,reassoc] theorem ordinaryInputIso_snd (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    (ordinaryInputIso R X i).hom ≫ prod.snd = K.map prod.snd ≫ (finitePowerIso X i.val).hom := by
  simp [ordinaryInputIso]

/-- Canonical finite-coproduct and ordered-power comparison for the
ordinary polynomial, proved independently of initiality. -/
def ordinaryObjectIso (X : PredicateCategory 𝗣𝗔) :
    K.obj ((SyntacticDerivation.PolynomialComparison.ordinary R).obj X) ≅
      (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).obj (K.obj X) :=
  (asIso (sigmaComparison K (fun i : Fin (N+1) => R.instances i ⨯ finitePower X i.val))).symm ≪≫
    Sigma.mapIso (ordinaryInputIso R X)

@[simp,reassoc] theorem ordinaryObjectIso_iota (X : PredicateCategory 𝗣𝗔) (i : Fin (N+1)) :
    K.map (Sigma.ι (fun i : Fin (N+1) => R.instances i ⨯ finitePower X i.val) i) ≫
      (ordinaryObjectIso R X).hom =
      (ordinaryInputIso R X i).hom ≫
        Sigma.ι (fun i : Fin (N+1) => (interpretedRules R).instances i ⨯ finitePower (K.obj X) i.val) i := by
  simp only [ordinaryObjectIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

theorem ordinaryObjectIso_natural {X Y : PredicateCategory 𝗣𝗔} (f : X ⟶ Y) :
    K.map ((SyntacticDerivation.PolynomialComparison.ordinary R).map f) ≫
      (ordinaryObjectIso R Y).hom =
      (ordinaryObjectIso R X).hom ≫
        (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map (K.map f) := by
  apply mapSum_hom_ext (fun i : Fin (N+1) => R.instances i ⨯ finitePower X i.val)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [SyntacticDerivation.PolynomialComparison.ordinary,Sigma.ι_map,
    Functor.map_comp_assoc,ordinaryObjectIso_iota_assoc]
  rw [ordinaryObjectIso_iota]
  rw [← Category.assoc,← Category.assoc]
  apply congrArg (fun k => k ≫ Sigma.ι
    (fun i : Fin (N+1) => (interpretedRules R).instances i ⨯ finitePower (K.obj Y) i.val) i)
  apply prod.hom_ext
  · simp only [Category.assoc,ordinaryInputIso_fst,
      prod.map_fst,Category.comp_id]
    rw [← Functor.map_comp,prod.map_fst,Category.comp_id]
  · simp only [Category.assoc,ordinaryInputIso_snd,ordinaryInputIso_snd_assoc,prod.map_snd]
    rw [← Functor.map_comp_assoc,prod.map_snd,Functor.map_comp_assoc,finitePowerIso_natural]

/-- The inference input comparison preserves the rule label and ordered children inside
the ordinary tree input. -/
theorem input_forget_square (Q : Over F) (i : Fin (N+1)) :
    K.map (SyntacticDerivation.CheckedRoot.matchingMap R Q i) ≫
        (ordinaryInputIso R Q.left i).hom =
      (inputIso R Q i).hom ≫
        SyntacticDerivation.CheckedRoot.matchingMap (interpretedRules R) ((overFunctor R).obj Q) i := by
  apply prod.hom_ext
  · have hsrc : SyntacticDerivation.CheckedRoot.matchingMap R Q i ≫ prod.fst =
        pullback.fst (R.premises i) (finitePowerMap Q.hom i.val) := prod.lift_fst _ _
    have htgt : SyntacticDerivation.CheckedRoot.matchingMap (interpretedRules R)
        ((overFunctor R).obj Q) i ≫ prod.fst =
        pullback.fst ((interpretedRules R).premises i)
          (finitePowerMap (K.map Q.hom) i.val) := prod.lift_fst _ _
    rw [Category.assoc,ordinaryInputIso_fst]
    have he := (K.map_comp (SyntacticDerivation.CheckedRoot.matchingMap R Q i) prod.fst).symm.trans
      ((congrArg K.map hsrc).trans ((inputIso_fst R Q i).symm.trans
        (congrArg (fun k => (inputIso R Q i).hom ≫ k) htgt.symm)))
    exact he
  · simp only [Category.assoc,ordinaryInputIso_snd,
      SyntacticDerivation.CheckedRoot.matchingMap,prod.lift_snd,← Functor.map_comp_assoc,inputIso_snd]

theorem forget_comparison (Q : Over F) :
    K.map (SyntacticDerivation.InputGeometry.forget R Q) ≫ (ordinaryObjectIso R Q.left).hom =
      (sumIso R Q).hom ≫ SyntacticDerivation.InputGeometry.forget (interpretedRules R)
        ((overFunctor R).obj Q) := by
  apply mapSum_hom_ext (R.ruleObject Q)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [SyntacticDerivation.InputGeometry.forget,Sigma.ι_comp_desc,
    Functor.map_comp_assoc,ordinaryObjectIso_iota]
  rw [sumIso_iota_assoc]
  simp only [Sigma.ι_comp_desc]
  rw [← Category.assoc,input_forget_square,Category.assoc]
  rfl

/-- The arithmetic functor intertwines the ordinary-tree functors. -/
def ordinaryComparison :
    SyntacticDerivation.PolynomialComparison.ordinary R ⋙ K ≅
      K ⋙ SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R) :=
  NatIso.ofComponents (ordinaryObjectIso R) (fun f => ordinaryObjectIso_natural R f)

def mappedOrdinaryAlgebra
    (A : Endofunctor.Algebra (SyntacticDerivation.PolynomialComparison.ordinary R)) :
    Endofunctor.Algebra (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)) where
  a := K.obj A.a
  str := (ordinaryComparison R).inv.app A.a ≫ K.map A.str

/-- Algebra morphisms are transported through the proved ordinary
endofunctor comparison. This does not assert that arbitrary initial
algebras are preserved by arithmetic interpretation. -/
def mappedOrdinaryHom
    {A B : Endofunctor.Algebra (SyntacticDerivation.PolynomialComparison.ordinary R)} (f : A ⟶ B) :
    mappedOrdinaryAlgebra R A ⟶ mappedOrdinaryAlgebra R B where
  f := K.map f.f
  h := by
    change (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map (K.map f.f) ≫
        (ordinaryComparison R).inv.app B.a ≫ K.map B.str =
      ((ordinaryComparison R).inv.app A.a ≫ K.map A.str) ≫ K.map f.f
    have hn := (ordinaryComparison R).inv.naturality f.f
    change (SyntacticDerivation.PolynomialComparison.ordinary (interpretedRules R)).map (K.map f.f) ≫
        (ordinaryComparison R).inv.app B.a =
      (ordinaryComparison R).inv.app A.a ≫ K.map
        ((SyntacticDerivation.PolynomialComparison.ordinary R).map f.f) at hn
    rw [← Category.assoc,hn,Category.assoc,← Functor.map_comp,f.h,Functor.map_comp,Category.assoc]

end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
