/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersInference
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Actual inference transport across the predicate equivalence

Only coefficient isomorphisms and their original premise/conclusion
diagrams are supplied. The inference and algebra comparisons are derived.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.InferenceTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (E : C ≌ D)

def power (X : C) : (n : ℕ) → E.functor.obj (finitePower X n) ≅ finitePower (E.functor.obj X) n
  | 0 => asIso (terminalComparison E.functor)
  | 1 => Iso.refl _
  | n + 2 => asIso (prodComparison E.functor (finitePower X (n+1)) X) ≪≫
      prod.mapIso (power X (n+1)) (Iso.refl _)

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
@[reassoc] theorem power_natural {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    E.functor.map (finitePowerMap f n) ≫ (power E Y n).hom =
      (power E X n).hom ≫ finitePowerMap (E.functor.map f) n := by
  induction n with
  | zero => exact terminal.hom_ext _ _
  | succ n ih =>
      cases n with
      | zero => simp only [power,finitePowerMap,Iso.refl_hom,Category.comp_id,Category.id_comp]
      | succ n =>
          simp only [power,Iso.trans_hom,asIso_hom,prod.mapIso_hom,Iso.refl_hom,finitePowerMap]
          rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,ih]
          simp [prod.map_map]

variable {F : C} {N : ℕ} (R : RulePresentation F N)
variable (R' : RulePresentation (E.functor.obj F) N)

structure Data where
  coefficient : ∀ i, E.functor.obj (R.instances i) ≅ R'.instances i
  premises : ∀ i, E.functor.map (R.premises i) ≫ (power E F i.val).hom =
    (coefficient i).hom ≫ R'.premises i
  conclusion : ∀ i, E.functor.map (R.conclusion i) = (coefficient i).hom ≫ R'.conclusion i

variable (h : Data E R R')

abbrev overEquivalence : Over F ≌ Over (E.functor.obj F) := Over.postEquiv F E

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
private theorem input_square (Q : Over F) (i : Fin (N+1)) :
    IsPullback
      (E.functor.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) ≫ (h.coefficient i).hom)
      (E.functor.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫ (power E Q.left i.val).hom)
      (R'.premises i) (finitePowerMap (E.functor.map Q.hom) i.val) := by
  apply ((IsPullback.of_hasPullback (R.premises i) (finitePowerMap Q.hom i.val)).map E.functor).of_iso
    (Iso.refl _) (h.coefficient i) (power E Q.left i.val) (power E F i.val)
  · simp
  · simp
  · exact h.premises i
  · exact power_natural E Q.hom i.val

def inputIso (Q : Over F) (i : Fin (N+1)) :
    E.functor.obj (R.ruleObject Q i) ≅ R'.ruleObject ((overEquivalence E).functor.obj Q) i :=
  (input_square E R R' h Q i).isoPullback

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
@[simp,reassoc] theorem inputIso_fst (Q : Over F) (i : Fin (N+1)) :
    (inputIso E R R' h Q i).hom ≫ pullback.fst _ _ =
      E.functor.map (pullback.fst (R.premises i) (finitePowerMap Q.hom i.val)) ≫ (h.coefficient i).hom := by
  exact (input_square E R R' h Q i).isoPullback_hom_fst

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
@[simp,reassoc] theorem inputIso_snd (Q : Over F) (i : Fin (N+1)) :
    (inputIso E R R' h Q i).hom ≫ pullback.snd _ _ =
      E.functor.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫ (power E Q.left i.val).hom := by
  exact (input_square E R R' h Q i).isoPullback_hom_snd

/-- This comparison includes the actual arity-zero coefficient object. -/
def sumIso (Q : Over F) : E.functor.obj (∐ R.ruleObject Q) ≅
    ∐ R'.ruleObject ((overEquivalence E).functor.obj Q) :=
  (asIso (sigmaComparison E.functor (R.ruleObject Q))).symm ≪≫ Sigma.mapIso (inputIso E R R' h Q)

@[simp,reassoc] theorem sumIso_iota (Q : Over F) (i : Fin (N+1)) :
    E.functor.map (Sigma.ι (R.ruleObject Q) i) ≫ (sumIso E R R' h Q).hom =
      (inputIso E R R' h Q i).hom ≫ Sigma.ι (R'.ruleObject ((overEquivalence E).functor.obj Q)) i := by
  simp only [sumIso,Iso.trans_hom,Iso.symm_hom,asIso_inv,
    map_ι_comp_inv_sigmaComparison_assoc,Sigma.ι_mapIso_hom]

omit [Regular C] [Regular D] in
private theorem mapSum_hom_ext {I : Type} [Finite I] (X : I → C) {Y : D}
    (f g : E.functor.obj (∐ X) ⟶ Y)
    (hh : ∀ i, E.functor.map (Sigma.ι X i) ≫ f = E.functor.map (Sigma.ι X i) ≫ g) : f = g := by
  apply (cancel_epi (sigmaComparison E.functor X)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [ι_comp_sigmaComparison_assoc] using hh i

/-- The displayed conclusion equality makes this an isomorphism in the
original formula slice, as required for generated-theory comparison. -/
def overIso (Q : Over F) :
    (overEquivalence E).functor.obj (R.inference.obj Q) ≅
      R'.inference.obj ((overEquivalence E).functor.obj Q) :=
  Over.isoMk (sumIso E R R' h Q) (by
    apply mapSum_hom_ext E (R.ruleObject Q)
    intro i
    rw [← Category.assoc,sumIso_iota,Category.assoc]
    change (inputIso E R R' h Q i).hom ≫
        Sigma.ι (R'.ruleObject ((overEquivalence E).functor.obj Q)) i ≫
          Sigma.desc (R'.ruleConclusion ((overEquivalence E).functor.obj Q)) =
      E.functor.map (Sigma.ι (R.ruleObject Q) i) ≫ E.functor.map (Sigma.desc (R.ruleConclusion Q))
    rw [Sigma.ι_comp_desc]
    change (inputIso E R R' h Q i).hom ≫
        pullback.fst _ _ ≫ R'.conclusion i =
      E.functor.map (Sigma.ι (R.ruleObject Q) i) ≫ E.functor.map (R.inference.obj Q).hom
    rw [inputIso_fst_assoc,← h.conclusion i,← Functor.map_comp]
    change E.functor.map (R.ruleConclusion Q i) =
      E.functor.map (Sigma.ι (R.ruleObject Q) i) ≫ E.functor.map (Sigma.desc (R.ruleConclusion Q))
    rw [← Functor.map_comp,Sigma.ι_comp_desc])

omit [HasFiniteCoproducts C] [HasFiniteCoproducts D] in
private theorem input_natural {Q Q' : Over F} (f : Q ⟶ Q') (i : Fin (N+1)) :
    E.functor.map (R.ruleMap f i) ≫ (inputIso E R R' h Q' i).hom =
      (inputIso E R R' h Q i).hom ≫ R'.ruleMap ((overEquivalence E).functor.map f) i := by
  apply pullback.hom_ext
  · simp only [Category.assoc,inputIso_fst,RulePresentation.ruleMap_fst]
    rw [← Functor.map_comp_assoc,RulePresentation.ruleMap_fst]
  · simp only [Category.assoc,inputIso_snd,RulePresentation.ruleMap_snd]
    rw [← Functor.map_comp_assoc,RulePresentation.ruleMap_snd,Functor.map_comp_assoc,power_natural]
    change E.functor.map (pullback.snd (R.premises i) (finitePowerMap Q.hom i.val)) ≫
        (power E Q.left i.val).hom ≫ finitePowerMap (E.functor.map f.left) i.val =
      (inputIso E R R' h Q i).hom ≫ pullback.snd _ _ ≫ finitePowerMap (E.functor.map f.left) i.val
    rw [inputIso_snd_assoc]

theorem overIso_natural {Q Q' : Over F} (f : Q ⟶ Q') :
    (overEquivalence E).functor.map (R.inference.map f) ≫ (overIso E R R' h Q').hom =
      (overIso E R R' h Q).hom ≫ R'.inference.map ((overEquivalence E).functor.map f) := by
  apply Over.OverMorphism.ext
  change E.functor.map (Limits.Sigma.map (R.ruleMap f)) ≫ (sumIso E R R' h Q').hom =
    (sumIso E R R' h Q).hom ≫ Limits.Sigma.map (R'.ruleMap ((overEquivalence E).functor.map f))
  apply mapSum_hom_ext E (R.ruleObject Q)
  intro i
  rw [← Functor.map_comp_assoc]
  simp only [Sigma.ι_map,Functor.map_comp_assoc,sumIso_iota_assoc]
  rw [sumIso_iota,← Category.assoc,input_natural,Category.assoc]

/-- The endofunctor comparison is proved from preserved finite powers,
rule-input pullbacks and finite coproducts. -/
def comparison : R.inference ⋙ (overEquivalence E).functor ≅
    (overEquivalence E).functor ⋙ R'.inference :=
  NatIso.ofComponents (overIso E R R' h) (fun f => overIso_natural E R R' h f)

def algebraEquivalence : Endofunctor.Algebra R.inference ≌ Endofunctor.Algebra R'.inference :=
  AlgebraTransport.equivalence (overEquivalence E) (comparison E R R' h)

def mappedInitial (A : Endofunctor.Algebra R.inference) (hA : IsInitial A) :
    IsInitial ((algebraEquivalence E R R' h).functor.obj A) :=
  AlgebraTransport.initial (overEquivalence E) (comparison E R R' h) A hA

/-- Expose the whole underlying comparison before any concrete encoded
proof carrier is substituted for A. -/
def carrierIso (A : Endofunctor.Algebra R.inference) (B : Endofunctor.Algebra R'.inference)
    (c : B ≅ (algebraEquivalence E R R' h).functor.obj A) :
    B.a.left ≅ E.functor.obj A.a.left :=
  (Over.forget (E.functor.obj F)).mapIso
    ((Endofunctor.Algebra.forget R'.inference).mapIso c)

@[reassoc] theorem carrierIso_conclusion
    (A : Endofunctor.Algebra R.inference) (B : Endofunctor.Algebra R'.inference)
    (c : B ≅ (algebraEquivalence E R R' h).functor.obj A) :
    (carrierIso E R R' h A B c).hom ≫ E.functor.map A.a.hom = B.a.hom :=
  Over.w c.hom.f

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.InferenceTransport
