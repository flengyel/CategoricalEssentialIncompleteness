/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonSchemes
public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersTransport
public import CategoricalEssentialIncompleteness.V46MillerDerivationTotal

/-! # Finite-rule inference transport with the formula chart

This is the finite-power, pullback and finite-sum construction, with the final formula
isomorphism included in the slice. All fields of the data below concern rule
coefficients and their ordered diagrams; no inference comparison or initiality is a
field.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.Inference
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {F : C} {F' : D} (iF : E.functor.obj F ≅ F') {N : ℕ}

def powerIso {X Y : D} (i : X ≅ Y) (n : ℕ) : finitePower X n ≅ finitePower Y n where
  hom := finitePowerMap i.hom n
  inv := finitePowerMap i.inv n
  hom_inv_id := by rw [← finitePowerMap_comp, i.hom_inv_id, finitePowerMap_id]
  inv_hom_id := by rw [← finitePowerMap_comp, i.inv_hom_id, finitePowerMap_id]

def formulaPower (n : ℕ) : E.functor.obj (finitePower F n) ≅ finitePower F' n :=
  ArithmeticIndexedFibers.InferenceTransport.power E F n ≪≫ powerIso iF n

abbrev slice : Over F ≌ Over F' := (Over.postEquiv F E).trans (Over.mapIso iF)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem childPower (Q : Over F) (n : ℕ) :
    E.functor.map (finitePowerMap Q.hom n) ≫ (formulaPower E iF n).hom =
      (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n).hom ≫
        finitePowerMap ((slice E iF).functor.obj Q).hom n := by
  dsimp only [formulaPower, Iso.trans_hom, powerIso]
  rw [← Category.assoc, ArithmeticIndexedFibers.InferenceTransport.power_natural,
    Category.assoc, ← finitePowerMap_comp]
  rfl

variable (R : RulePresentation F N) (R' : RulePresentation F' N)

structure Data where
  coefficient : ∀ n, E.functor.obj (R.instances n) ≅ R'.instances n
  premises : ∀ n, E.functor.map (R.premises n) ≫ (formulaPower E iF n.val).hom =
    (coefficient n).hom ≫ R'.premises n
  conclusion : ∀ n, E.functor.map (R.conclusion n) ≫ iF.hom =
    (coefficient n).hom ≫ R'.conclusion n

variable (h : Data E iF R R')

def inputIso (Q : Over F) (n : Fin (N+1)) :
    E.functor.obj (R.ruleObject Q n) ≅ R'.ruleObject ((slice E iF).functor.obj Q) n :=
  pullbackChart E (h.coefficient n)
    (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val) (formulaPower E iF n.val)
    (R.premises n) (finitePowerMap Q.hom n.val) (R'.premises n)
    (finitePowerMap ((slice E iF).functor.obj Q).hom n.val)
    (h.premises n) (childPower E iF Q n.val)

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem input_fst (Q : Over F) (n : Fin (N+1)) :
    (inputIso E iF R R' h Q n).hom ≫ pullback.fst _ _ =
      E.functor.map (pullback.fst _ _) ≫ (h.coefficient n).hom :=
  (pullbackChart_fst E (h.coefficient n)
    (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val) (formulaPower E iF n.val)
    _ _ _ _ (h.premises n) (childPower E iF Q n.val)).symm

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem input_snd (Q : Over F) (n : Fin (N+1)) :
    (inputIso E iF R R' h Q n).hom ≫ pullback.snd _ _ =
      E.functor.map (pullback.snd _ _) ≫
        (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val).hom :=
  (pullbackChart_snd E (h.coefficient n)
    (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val) (formulaPower E iF n.val)
    _ _ _ _ (h.premises n) (childPower E iF Q n.val)).symm

def sumIso (Q : Over F) : E.functor.obj (∐ R.ruleObject Q) ≅
    ∐ R'.ruleObject ((slice E iF).functor.obj Q) :=
  (asIso (sigmaComparison E.functor (R.ruleObject Q))).symm ≪≫
    Sigma.mapIso (inputIso E iF R R' h Q)

@[reassoc] theorem sum_iota (Q : Over F) (n : Fin (N+1)) :
    E.functor.map (Sigma.ι (R.ruleObject Q) n) ≫ (sumIso E iF R R' h Q).hom =
      (inputIso E iF R R' h Q n).hom ≫ Sigma.ι (R'.ruleObject ((slice E iF).functor.obj Q)) n := by
  simp only [sumIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_mapIso_hom]

omit [Regular C] [Regular D] in
theorem map_sum_ext {I : Type} [Finite I] (X : I → C) {Y : D}
    (f g : E.functor.obj (∐ X) ⟶ Y)
    (hs : ∀ n, E.functor.map (Sigma.ι X n) ≫ f = E.functor.map (Sigma.ι X n) ≫ g) : f=g := by
  apply (cancel_epi (sigmaComparison E.functor X)).mp
  apply Sigma.hom_ext
  intro n
  simpa only [ι_comp_sigmaComparison_assoc] using hs n

def component (Q : Over F) :
    (slice E iF).functor.obj (R.inference.obj Q) ≅ R'.inference.obj ((slice E iF).functor.obj Q) :=
  Over.isoMk (sumIso E iF R R' h Q) (by
    apply map_sum_ext E (R.ruleObject Q)
    intro n
    rw [← Category.assoc, sum_iota, Category.assoc]
    change (inputIso E iF R R' h Q n).hom ≫
      Sigma.ι (R'.ruleObject ((slice E iF).functor.obj Q)) n ≫
        Sigma.desc (R'.ruleConclusion ((slice E iF).functor.obj Q)) =
      E.functor.map (Sigma.ι (R.ruleObject Q) n) ≫
        (E.functor.map (Sigma.desc (R.ruleConclusion Q)) ≫ iF.hom)
    rw [Sigma.ι_comp_desc]
    change (inputIso E iF R R' h Q n).hom ≫ pullback.fst _ _ ≫ R'.conclusion n = _
    rw [← Category.assoc, input_fst, Category.assoc, ← h.conclusion n,
      ← Functor.map_comp_assoc]
    change E.functor.map (R.ruleConclusion Q n) ≫ iF.hom =
      E.functor.map (Sigma.ι (R.ruleObject Q) n) ≫
        E.functor.map (Sigma.desc (R.ruleConclusion Q)) ≫ iF.hom
    rw [← Functor.map_comp_assoc, Sigma.ι_comp_desc])

omit [FinitaryExtensive C] [FinitaryExtensive D] in
theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') (n : Fin (N+1)) :
    E.functor.map (R.ruleMap f n) ≫ (inputIso E iF R R' h Q' n).hom =
      (inputIso E iF R R' h Q n).hom ≫ R'.ruleMap ((slice E iF).functor.map f) n := by
  apply pullback.hom_ext
  · simp only [Category.assoc, input_fst, RulePresentation.ruleMap_fst]
    rw [← Functor.map_comp_assoc, RulePresentation.ruleMap_fst]
  · simp only [Category.assoc, input_snd, RulePresentation.ruleMap_snd]
    rw [← Functor.map_comp_assoc, RulePresentation.ruleMap_snd, Functor.map_comp_assoc,
      ArithmeticIndexedFibers.InferenceTransport.power_natural]
    change E.functor.map (pullback.snd (R.premises n) (finitePowerMap Q.hom n.val)) ≫
        (ArithmeticIndexedFibers.InferenceTransport.power E Q.left n.val).hom ≫
          finitePowerMap (E.functor.map f.left) n.val =
      (inputIso E iF R R' h Q n).hom ≫ pullback.snd _ _ ≫
        finitePowerMap (E.functor.map f.left) n.val
    simpa only [Category.assoc] using congrArg
      (fun k => k ≫ finitePowerMap (E.functor.map f.left) n.val)
      (input_snd E iF R R' h Q n).symm

theorem component_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (slice E iF).functor.map (R.inference.map f) ≫ (component E iF R R' h Q').hom =
      (component E iF R R' h Q).hom ≫ R'.inference.map ((slice E iF).functor.map f) := by
  apply Over.OverMorphism.ext
  change E.functor.map (Limits.Sigma.map (R.ruleMap f)) ≫ (sumIso E iF R R' h Q').hom =
    (sumIso E iF R R' h Q).hom ≫ Limits.Sigma.map (R'.ruleMap ((slice E iF).functor.map f))
  apply map_sum_ext E (R.ruleObject Q)
  intro n
  rw [← Functor.map_comp_assoc]
  simp only [Sigma.ι_map, Functor.map_comp_assoc, sum_iota_assoc]
  rw [sum_iota, ← Category.assoc, input_natural, Category.assoc]

def comparison : R.inference ⋙ (slice E iF).functor ≅ (slice E iF).functor ⋙ R'.inference :=
  NatIso.ofComponents (component E iF R R' h) (fun f => component_natural E iF R R' h f)

def mappedAlgebra (A : Endofunctor.Algebra R.inference) : Endofunctor.Algebra R'.inference :=
  AlgebraTransport.mappedAlgebra (slice E iF) (comparison E iF R R' h) A

def mappedInitial (A : Endofunctor.Algebra R.inference) (hA : IsInitial A) :
    IsInitial (mappedAlgebra E iF R R' h A) :=
  AlgebraTransport.initial (slice E iF) (comparison E iF R R' h) A hA
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation.Inference
