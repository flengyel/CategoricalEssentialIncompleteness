/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ForkDerivationCoordinates
import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation

/-! # Finite-rule inputs under component evaluation

The construction repeats the finite-power/pullback/coproduct comparison
already proved for arithmetic interpretation, now with the source category
of total forks. It transfers operations, without an initiality assertion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Evaluation
variable {K : EffectiveFork.Total ⥤ NumericalTuples.Object}
variable [PreservesFiniteLimits K] [PreservesFiniteCoproducts K]
/-- Ordered powers include the chosen nullary terminal object. -/
def finitePowerIso (X : EffectiveFork.Total) :
    (n : ℕ) → K.obj (finitePower X n) ≅ finitePower (K.obj X) n
  | 0 => asIso (terminalComparison K)
  | 1 => Iso.refl _
  | n + 2 => asIso (prodComparison K (finitePower X (n+1)) X) ≪≫
      prod.mapIso (finitePowerIso X (n+1)) (Iso.refl _)

omit [PreservesFiniteCoproducts K] in
@[reassoc] theorem finitePowerIso_natural {X Y : EffectiveFork.Total} (f : X ⟶ Y) (n : ℕ) :
    K.map (finitePowerMap f n) ≫ (finitePowerIso (K := K) Y n).hom =
      (finitePowerIso (K := K) X n).hom ≫ finitePowerMap (K.map f) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
      cases n with
      | zero =>
          change K.map f ≫ (𝟙 _) = (𝟙 _) ≫ K.map f
          rw [Category.comp_id,Category.id_comp]
      | succ n =>
          simp only [finitePowerIso,Iso.trans_hom,asIso_hom,prod.mapIso_hom,Iso.refl_hom,finitePowerMap]
          rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,ih]
          simp [prod.map_map]

variable {F : EffectiveFork.Total} {N : ℕ} (R : RulePresentation F N)

/-- The coefficients and conclusions are the actual source images;
premises use the canonical ordered finite-power comparison. -/
def interpretedRules : RulePresentation (K.obj F) N where
  instances i := K.obj (R.instances i)
  premises i := K.map (R.premises i) ≫ (finitePowerIso (K := K) F i.val).hom
  conclusion i := K.map (R.conclusion i)

abbrev overFunctor (_R : RulePresentation F N) : Over F ⥤ Over (K.obj F) := Over.post K

omit [PreservesFiniteCoproducts K] in
private theorem input_square (Q : Over F) (i : Fin (N+1)) :
    IsPullback
      (K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)))
      (K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso (K := K) Q.left i.val).hom)
      ((interpretedRules (K := K) R).premises i) (finitePowerMap (K.map Q.hom) i.val) := by
  apply ((IsPullback.of_hasPullback (R.premises i) (finitePowerMap Q.hom i.val)).map K).of_iso
    (Iso.refl _) (Iso.refl _) (finitePowerIso (K := K) Q.left i.val) (finitePowerIso (K := K) F i.val)
  · simp
  · simp
  · simp only [Iso.refl_hom,Category.id_comp,interpretedRules]
  · exact finitePowerIso_natural (K := K) Q.hom i.val

def inputIso (Q : Over F) (i : Fin (N+1)) :
    K.obj (R.ruleObject Q i) ≅ (interpretedRules (K := K) R).ruleObject ((overFunctor (K := K) R).obj Q) i :=
  (input_square (K := K) R Q i).isoPullback

omit [PreservesFiniteCoproducts K] in
@[simp,reassoc] theorem inputIso_fst (Q : Over F) (i : Fin (N+1)) :
    (inputIso (K := K) R Q i).hom ≫ pullback.fst _ _ =
      K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) :=
  (input_square (K := K) R Q i).isoPullback_hom_fst

omit [PreservesFiniteCoproducts K] in
@[simp,reassoc] theorem inputIso_snd (Q : Over F) (i : Fin (N+1)) :
    (inputIso (K := K) R Q i).hom ≫ pullback.snd _ _ =
      K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso (K := K) Q.left i.val).hom :=
  (input_square (K := K) R Q i).isoPullback_hom_snd


def sumIso (Q : Over F) : K.obj (∐ R.ruleObject Q) ≅
    ∐ (interpretedRules (K := K) R).ruleObject ((overFunctor (K := K) R).obj Q) :=
  (asIso (sigmaComparison K (R.ruleObject Q))).symm ≪≫ Sigma.mapIso (inputIso (K := K) R Q)

@[simp,reassoc] theorem sumIso_iota (Q : Over F) (i : Fin (N+1)) :
    K.map (Sigma.ι (R.ruleObject Q) i) ≫ (sumIso (K := K) R Q).hom =
      (inputIso (K := K) R Q i).hom ≫ Sigma.ι ((interpretedRules (K := K) R).ruleObject ((overFunctor (K := K) R).obj Q)) i := by
  simp only [sumIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

omit [PreservesFiniteLimits K] in
private theorem mapSum_hom_ext {I : Type} [Finite I] (X : I → EffectiveFork.Total) {Y : NumericalTuples.Object}
    (f g : K.obj (∐ X) ⟶ Y)
    (hh : ∀ i, K.map (Sigma.ι X i) ≫ f = K.map (Sigma.ι X i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using hh i

/-- The displayed conclusion equality makes this an isomorphism in the
original formula slice, as required for generated-theory comparison. -/
def overIso (Q : Over F) :
    (overFunctor (K := K) R).obj (R.inference.obj Q) ≅
      (interpretedRules (K := K) R).inference.obj ((overFunctor (K := K) R).obj Q) :=
  Over.isoMk (sumIso (K := K) R Q) (by
    apply mapSum_hom_ext (K := K) (R.ruleObject Q)
    intro i
    rw [← Category.assoc,sumIso_iota (K := K),Category.assoc]
    change (inputIso (K := K) R Q i).hom ≫
        Sigma.ι ((interpretedRules (K := K) R).ruleObject ((overFunctor (K := K) R).obj Q)) i ≫
          Sigma.desc ((interpretedRules (K := K) R).ruleConclusion ((overFunctor (K := K) R).obj Q)) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [Sigma.ι_comp_desc]
    change (inputIso (K := K) R Q i).hom ≫
        pullback.fst _ _ ≫ (interpretedRules (K := K) R).conclusion i =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (R.inference.obj Q).hom
    rw [inputIso_fst_assoc]
    change K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        K.map (R.conclusion i) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [← Functor.map_comp]
    change K.map (R.ruleConclusion Q i) =
      K.map (Sigma.ι (R.ruleObject Q) i) ≫ K.map (Sigma.desc (R.ruleConclusion Q))
    rw [← Functor.map_comp,Sigma.ι_comp_desc])

omit [PreservesFiniteCoproducts K] in
private theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N+1)) :
    K.map (R.ruleMap f i) ≫ (inputIso (K := K) R Q' i).hom =
      (inputIso (K := K) R Q i).hom ≫ (interpretedRules (K := K) R).ruleMap ((overFunctor (K := K) R).map f) i := by
  apply pullback.hom_ext
  · simp only [Category.assoc,inputIso_fst (K := K),RulePresentation.ruleMap_fst]
    change K.map (R.ruleMap f i) ≫
        K.map (pullback.fst (R.premises i) (finitePowerMap Q'.hom i.val)) =
      K.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val))
    exact (K.map_comp _ _).symm.trans (congrArg K.map (RulePresentation.ruleMap_fst R f i))
  · simp only [Category.assoc,inputIso_snd (K := K),RulePresentation.ruleMap_snd]
    rw [← Functor.map_comp_assoc,RulePresentation.ruleMap_snd,Functor.map_comp_assoc,finitePowerIso_natural (K := K)]
    change K.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (finitePowerIso (K := K) Q.left i.val).hom ≫ finitePowerMap (K.map f.left) i.val =
      (inputIso (K := K) R Q i).hom ≫ pullback.snd _ _ ≫ finitePowerMap (K.map f.left) i.val
    rw [inputIso_snd_assoc]

theorem overIso_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (overFunctor (K := K) R).map (R.inference.map f) ≫ (overIso (K := K) R Q').hom =
      (overIso (K := K) R Q).hom ≫ (interpretedRules (K := K) R).inference.map ((overFunctor (K := K) R).map f) := by
  apply Over.OverMorphism.ext
  change K.map (Limits.Sigma.map (R.ruleMap f)) ≫ (sumIso (K := K) R Q').hom =
    (sumIso (K := K) R Q).hom ≫ Limits.Sigma.map ((interpretedRules (K := K) R).ruleMap ((overFunctor (K := K) R).map f))
  apply mapSum_hom_ext (K := K) (R.ruleObject Q)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [Sigma.ι_map,Functor.map_comp_assoc,sumIso_iota_assoc]
  rw [sumIso_iota (K := K),← Category.assoc,input_natural (K := K),Category.assoc]

/-- The endofunctor comparison is proved from preserved finite powers,
rule-input pullbacks and finite coproducts. -/
def comparison : R.inference ⋙ (overFunctor (K := K) R) ≅
    (overFunctor (K := K) R) ⋙ (interpretedRules (K := K) R).inference :=
  NatIso.ofComponents (overIso (K := K) R) (fun f => overIso_natural (K := K) R f)

/-- Mapping a source algebra uses the proved comparison; its initiality
is a separate literal-code obligation. -/
def mappedAlgebra (A : Endofunctor.Algebra R.inference) :
    Endofunctor.Algebra (interpretedRules (K := K) R).inference where
  a := (overFunctor (K := K) R).obj A.a
  str := (comparison (K := K) R).inv.app A.a ≫ (overFunctor (K := K) R).map A.str

theorem mappedAlgebra_conclusion (A : Endofunctor.Algebra R.inference) :
    (mappedAlgebra (K := K) R A).a.hom = K.map A.a.hom := rfl



section Transformations
variable {L : EffectiveFork.Total ⥤ NumericalTuples.Object}
variable [PreservesFiniteLimits L] [PreservesFiniteCoproducts L]
variable (α : K ⟶ L)

omit [PreservesFiniteCoproducts K] [PreservesFiniteCoproducts L] in
@[reassoc] theorem productComparison_transformation (A B : EffectiveFork.Total) :
    α.app (A ⨯ B) ≫ prodComparison L A B =
      prodComparison K A B ≫ prod.map (α.app A) (α.app B) := by
  apply prod.hom_ext
  · simpa only [Category.assoc,prodComparison_fst,prod.map_fst,prodComparison_fst_assoc] using
      (α.naturality (prod.fst : A ⨯ B ⟶ A)).symm
  · simpa only [Category.assoc,prodComparison_snd,prod.map_snd,prodComparison_snd_assoc] using
      (α.naturality (prod.snd : A ⨯ B ⟶ B)).symm

omit [PreservesFiniteCoproducts K] [PreservesFiniteCoproducts L] in
/-- An arbitrary transformation respects the ordered finite-power charts.
No cartesianness condition on the transformation is required. -/
@[reassoc] theorem finitePowerIso_transformation (X : EffectiveFork.Total) (n : ℕ) :
    α.app (finitePower X n) ≫ (finitePowerIso (K := L) X n).hom =
      (finitePowerIso (K := K) X n).hom ≫ finitePowerMap (α.app X) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
    cases n with
    | zero =>
      change α.app X ≫ (𝟙 _) = (𝟙 _) ≫ α.app X
      rw [Category.comp_id,Category.id_comp]
    | succ n =>
      simp only [finitePowerIso,Iso.trans_hom,asIso_hom,prod.mapIso_hom,Iso.refl_hom,finitePowerMap]
      erw [← Category.assoc,productComparison_transformation,Category.assoc,prod.map_map,ih]
      erw [Category.assoc,prod.map_map,Category.id_comp,Category.comp_id]

omit [PreservesFiniteLimits K] [PreservesFiniteLimits L] in
/-- The finite coproduct chart is natural under the same arbitrary
transformation, including empty coefficient objects. -/
@[reassoc] theorem sigmaComparison_transformation {I : Type} [Finite I]
    (X : I → EffectiveFork.Total) :
    α.app (∐ X) ≫ inv (sigmaComparison L X) =
      inv (sigmaComparison K X) ≫ Limits.Sigma.map (fun i => α.app (X i)) := by
  apply (cancel_epi (sigmaComparison K X)).mp
  apply Sigma.hom_ext
  intro i
  calc
    Sigma.ι (fun i => K.obj (X i)) i ≫
        (sigmaComparison K X ≫ α.app (∐ X) ≫ inv (sigmaComparison L X)) =
        K.map (Sigma.ι X i) ≫ α.app (∐ X) ≫ inv (sigmaComparison L X) := by
          rw [← Category.assoc,ι_comp_sigmaComparison]
    _ = α.app (X i) ≫ L.map (Sigma.ι X i) ≫ inv (sigmaComparison L X) := by
          rw [← Category.assoc,α.naturality,Category.assoc]
    _ = α.app (X i) ≫ Sigma.ι (fun i => L.obj (X i)) i := by
          rw [map_ι_comp_inv_sigmaComparison]
    _ = Sigma.ι (fun i => K.obj (X i)) i ≫
        (sigmaComparison K X ≫
          (inv (sigmaComparison K X) ≫ Limits.Sigma.map (fun i => α.app (X i)))) := by
          simp only [IsIso.hom_inv_id_assoc,Sigma.ι_map]
end Transformations
end CategoricalEssentialIncompleteness.V46.ForkDerivation.Evaluation
