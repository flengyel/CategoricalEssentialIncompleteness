/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation
public import CategoricalEssentialIncompleteness.V46AlgebraTransport

/-! # Changing formula coordinates in numerical derivation algebras -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalRuleRebase
variable {F G : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) (e : F ≅ G)

/-- The labels and the order of premises are unchanged. -/
def rules : RulePresentation G N where
  instances := R.instances
  premises i := R.premises i ≫ finitePowerMap e.hom i.val
  conclusion i := R.conclusion i ≫ e.hom

def powerIso (n : ℕ) : finitePower F n ≅ finitePower G n where
  hom := finitePowerMap e.hom n
  inv := finitePowerMap e.inv n
  hom_inv_id := by rw [← finitePowerMap_comp,e.hom_inv_id,finitePowerMap_id]
  inv_hom_id := by rw [← finitePowerMap_comp,e.inv_hom_id,finitePowerMap_id]

abbrev slice : Over F ≌ Over G := Over.mapIso e

def inputHom (Q : Over F) (i : Fin (N + 1)) :
    R.ruleObject Q i ⟶ (rules R e).ruleObject ((slice e).functor.obj Q) i :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    change pullback.fst _ _ ≫ (R.premises i ≫ finitePowerMap e.hom i.val) =
      pullback.snd _ _ ≫ finitePowerMap (Q.hom ≫ e.hom) i.val
    rw [finitePowerMap_comp,← Category.assoc,← Category.assoc,pullback.condition])

def inputInv (Q : Over F) (i : Fin (N + 1)) :
    (rules R e).ruleObject ((slice e).functor.obj Q) i ⟶ R.ruleObject Q i :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _) (by
    apply (cancel_mono (powerIso e i.val).hom).mp
    change (pullback.fst _ _ ≫ R.premises i) ≫ finitePowerMap e.hom i.val =
      (pullback.snd _ _ ≫ finitePowerMap Q.hom i.val) ≫ finitePowerMap e.hom i.val
    rw [Category.assoc,Category.assoc,← finitePowerMap_comp]
    exact pullback.condition)

def inputIso (Q : Over F) (i : Fin (N + 1)) :
    R.ruleObject Q i ≅ (rules R e).ruleObject ((slice e).functor.obj Q) i where
  hom := inputHom R e Q i
  inv := inputInv R e Q i
  hom_inv_id := by apply pullback.hom_ext <;> simp [inputHom,inputInv]
  inv_hom_id := by apply pullback.hom_ext <;> simp [inputHom,inputInv]

@[reassoc (attr := simp)] theorem input_fst (Q : Over F) (i : Fin (N + 1)) :
    (inputIso R e Q i).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [inputIso,inputHom]

@[reassoc (attr := simp)] theorem input_snd (Q : Over F) (i : Fin (N + 1)) :
    (inputIso R e Q i).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [inputIso,inputHom]

/-- This isomorphism is induced by the original rule-input pullbacks. -/
def component (Q : Over F) :
    (slice e).functor.obj (R.inference.obj Q) ≅
      (rules R e).inference.obj ((slice e).functor.obj Q) :=
  Over.isoMk (Limits.Sigma.mapIso (inputIso R e Q)) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (R.ruleObject Q) i ≫
        (Limits.Sigma.mapIso (inputIso R e Q)).hom ≫
          Sigma.desc ((rules R e).ruleConclusion ((slice e).functor.obj Q)) =
      (Sigma.ι (R.ruleObject Q) i ≫ Sigma.desc (R.ruleConclusion Q)) ≫ e.hom
    rw [Sigma.ι_mapIso_hom_assoc,Sigma.ι_comp_desc,Sigma.ι_comp_desc]
    simpa only [RulePresentation.ruleConclusion,rules,Category.assoc] using
      congrArg (fun f => f ≫ R.conclusion i ≫ e.hom) (input_fst R e Q i))

theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N + 1)) :
    R.ruleMap f i ≫ (inputIso R e Q' i).hom =
      (inputIso R e Q i).hom ≫
        (rules R e).ruleMap ((slice e).functor.map f) i := by
  apply pullback.hom_ext <;> simp [inputIso,inputHom,RulePresentation.ruleMap]

def comparison : R.inference ⋙ (slice e).functor ≅
    (slice e).functor ⋙ (rules R e).inference :=
  NatIso.ofComponents (component R e) (by
    intro Q Q' f
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (R.ruleObject Q) i ≫
        (Limits.Sigma.map (R.ruleMap f) ≫ Limits.Sigma.map (fun i => (inputIso R e Q' i).hom)) =
      Sigma.ι (R.ruleObject Q) i ≫
        (Limits.Sigma.map (fun i => (inputIso R e Q i).hom) ≫
          Limits.Sigma.map ((rules R e).ruleMap ((slice e).functor.map f)))
    simp only [Sigma.ι_map_assoc,Sigma.ι_map]
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ Sigma.ι ((rules R e).ruleObject ((slice e).functor.obj Q')) i)
      (input_natural R e f i))

def mappedAlgebra : Endofunctor.Algebra (rules R e).inference :=
  AlgebraTransport.mappedAlgebra (slice e) (comparison R e) (NumericalDerivation.codeAlgebra R)

def mappedInitial : IsInitial (mappedAlgebra R e) :=
  AlgebraTransport.initial (slice e) (comparison R e) _ (NumericalDerivation.codeInitial R)

def algebraIso : mappedAlgebra R e ≅ NumericalDerivation.codeAlgebra (rules R e) :=
  (mappedInitial R e).uniqueUpToIso (NumericalDerivation.codeInitial (rules R e))

def overIso : (slice e).functor.obj (NumericalDerivation.codeAlgebra R).a ≅
    (NumericalDerivation.codeAlgebra (rules R e)).a :=
  (Endofunctor.Algebra.forget (rules R e).inference).mapIso (algebraIso R e)

def codeIso : NumericalDerivation.codeObject R ≅ NumericalDerivation.codeObject (rules R e) :=
  (Over.forget G).mapIso (overIso R e)

@[reassoc (attr := simp)] theorem conclusion :
    (codeIso R e).hom ≫ NumericalDerivation.codeConclusion (rules R e) =
      NumericalDerivation.codeConclusion R ≫ e.hom :=
  Over.w (overIso R e).hom

@[reassoc (attr := simp)] theorem inverse_conclusion :
    (codeIso R e).inv ≫ (NumericalDerivation.codeConclusion R ≫ e.hom) =
      NumericalDerivation.codeConclusion (rules R e) :=
  Over.w (overIso R e).inv

theorem constructor :
    (slice e).functor.map (NumericalDerivation.codeAlgebra R).str ≫ (overIso R e).hom =
      (comparison R e).hom.app (NumericalDerivation.codeAlgebra R).a ≫
        (rules R e).inference.map (overIso R e).hom ≫
          (NumericalDerivation.codeAlgebra (rules R e)).str := by
  have h := (algebraIso R e).hom.h
  change (rules R e).inference.map (overIso R e).hom ≫
      (NumericalDerivation.codeAlgebra (rules R e)).str =
    ((comparison R e).inv.app (NumericalDerivation.codeAlgebra R).a ≫
      (slice e).functor.map (NumericalDerivation.codeAlgebra R).str) ≫ (overIso R e).hom at h
  rw [h]
  have hi := (comparison R e).hom_inv_id_app (NumericalDerivation.codeAlgebra R).a
  simpa only [Category.assoc,Category.id_comp] using
    (congrArg (fun f => f ≫ (slice e).functor.map (NumericalDerivation.codeAlgebra R).str ≫
      (overIso R e).hom) hi).symm

def inputRebase (i : Fin (N + 1)) :
    R.ruleObject (NumericalDerivation.codeAlgebra R).a i ⟶
      (rules R e).ruleObject (NumericalDerivation.codeAlgebra (rules R e)).a i :=
  (inputIso R e (NumericalDerivation.codeAlgebra R).a i).hom ≫
    (rules R e).ruleMap (overIso R e).hom i

@[reassoc (attr := simp)] theorem input_label (i : Fin (N + 1)) :
    inputRebase R e i ≫ pullback.fst _ _ = pullback.fst _ _ := by
  calc
    _ = (inputIso R e (NumericalDerivation.codeAlgebra R).a i).hom ≫
        pullback.fst _ _ := by simp [inputRebase]
    _ = _ := input_fst R e (NumericalDerivation.codeAlgebra R).a i

@[reassoc (attr := simp)] theorem input_children (i : Fin (N + 1)) :
    inputRebase R e i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (codeIso R e).hom i.val := by
  calc
    _ = (inputIso R e (NumericalDerivation.codeAlgebra R).a i).hom ≫
        pullback.snd _ _ ≫ finitePowerMap (overIso R e).hom.left i.val := by
      simp [inputRebase]
    _ = _ := by
      simpa only [Category.assoc,codeIso,Functor.mapIso_hom,Over.forget_map] using
        congrArg (fun f => f ≫ finitePowerMap (overIso R e).hom.left i.val)
          (input_snd R e (NumericalDerivation.codeAlgebra R).a i)

end CategoricalEssentialIncompleteness.V46.NumericalRuleRebase
