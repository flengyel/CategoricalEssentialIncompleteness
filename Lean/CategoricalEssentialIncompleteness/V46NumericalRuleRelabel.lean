/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationPresentation

/-! # Computable relabelling of the constructed numerical derivation words -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalRuleRelabel
variable {F : NumericalTuples.Object} {N : ℕ} {R R' : RulePresentation F N}
variable (ι : RulePresentation.Hom R R') (κ : RulePresentation.Hom R' R)
  (hικ : ∀ i, ι.map i ≫ κ.map i = 𝟙 _) (hκι : ∀ i, κ.map i ≫ ι.map i = 𝟙 _)

/-- The rule label changes while each ordered child remains in place. -/
theorem mapRule_inverse (h : ∀ i, ι.map i ≫ κ.map i = 𝟙 _) (Q : Over F) (i : Fin (N + 1)) :
    ι.mapRule Q i ≫ κ.mapRule Q i = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [Category.assoc,RulePresentation.Hom.mapRule_fst,
      RulePresentation.Hom.mapRule_fst_assoc,Category.id_comp]
    erw [h i,Category.comp_id]
  · simp only [Category.assoc,RulePresentation.Hom.mapRule_snd,
      Category.id_comp]

/-- The original inference functors, including their prescribed
premise pullbacks, are naturally isomorphic. -/
def inferenceIso : R.inference ≅ R'.inference where
  hom := ι.inferenceTransformation
  inv := κ.inferenceTransformation
  hom_inv_id := by
    apply NatTrans.ext
    funext Q
    apply Over.OverMorphism.ext
    change Limits.Sigma.map (ι.mapRule Q) ≫ Limits.Sigma.map (κ.mapRule Q) = 𝟙 _
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_map, Sigma.ι_map_assoc,Category.comp_id]
    rw [← Category.assoc,mapRule_inverse ι κ hικ]
    simp
  inv_hom_id := by
    apply NatTrans.ext
    funext Q
    apply Over.OverMorphism.ext
    change Limits.Sigma.map (κ.mapRule Q) ≫ Limits.Sigma.map (ι.mapRule Q) = 𝟙 _
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_map, Sigma.ι_map_assoc,Category.comp_id]
    rw [← Category.assoc,mapRule_inverse κ ι hκι]
    simp

section Generic
universe u v
variable {C : Type u} [Category.{v} C] {H K : C ⥤ C}
variable (α : H ≅ K) {A : Endofunctor.Algebra H} {B : Endofunctor.Algebra K}

/-- Opposite relabelling folds compose to an algebra endomorphism. -/
def compositionHom (f : A.a ⟶ B.a) (g : B.a ⟶ A.a)
    (hf : H.map f ≫ (α.hom.app B.a ≫ B.str) = A.str ≫ f)
    (hg : K.map g ≫ (α.inv.app A.a ≫ A.str) = B.str ≫ g) : A ⟶ A where
  f := f ≫ g
  h := by
    rw [← Category.assoc,α.inv.naturality,Category.assoc] at hg
    have hgi : H.map g ≫ A.str = α.hom.app B.a ≫ B.str ≫ g := by
      apply (cancel_epi (α.inv.app B.a)).mp
      simpa only [Category.assoc,Iso.inv_hom_id_app_assoc] using hg
    rw [Functor.map_comp,Category.assoc,hgi]
    simpa only [Category.assoc] using congrArg (fun h => h ≫ g) hf

/-- The two unique folds are inverse, including their algebra equations. -/
def initialFoldIso (hA : IsInitial A) (hB : IsInitial B) : A.a ≅ B.a := by
  let f := hA.to ((Endofunctor.Algebra.functorOfNatTrans α.hom).obj B)
  let g := hB.to ((Endofunctor.Algebra.functorOfNatTrans α.inv).obj A)
  refine ⟨f.f,g.f,?_,?_⟩
  · exact congrArg Endofunctor.Algebra.Hom.f
      (hA.hom_ext (compositionHom (A := A) (B := B) α f.f g.f f.h g.h) (𝟙 _))
  · exact congrArg Endofunctor.Algebra.Hom.f
      (hB.hom_ext (compositionHom (A := B) (B := A) α.symm g.f f.f g.h f.h) (𝟙 _))

theorem initialFoldIso_hom (hA : IsInitial A) (hB : IsInitial B) :
    (initialFoldIso α hA hB).hom =
      (hA.to ((Endofunctor.Algebra.functorOfNatTrans α.hom).obj B)).f := rfl

theorem initialFoldIso_inv (hA : IsInitial A) (hB : IsInitial B) :
    (initialFoldIso α hA hB).inv =
      (hB.to ((Endofunctor.Algebra.functorOfNatTrans α.inv).obj A)).f := rfl

theorem initialFoldIso_constructor (hA : IsInitial A) (hB : IsInitial B) :
    A.str ≫ (initialFoldIso α hA hB).hom =
      α.hom.app A.a ≫ K.map (initialFoldIso α hA hB).hom ≫ B.str := by
  let f : A.a ⟶ B.a := (hA.to ((Endofunctor.Algebra.functorOfNatTrans α.hom).obj B)).f
  have hf := (hA.to ((Endofunctor.Algebra.functorOfNatTrans α.hom).obj B)).h
  change H.map f ≫ (α.hom.app B.a ≫ B.str) = A.str ≫ f at hf
  erw [← Category.assoc,α.hom.naturality,Category.assoc] at hf
  exact hf.symm

theorem initialFoldIso_inverse_constructor (hA : IsInitial A) (hB : IsInitial B) :
    B.str ≫ (initialFoldIso α hA hB).inv =
      α.inv.app B.a ≫ H.map (initialFoldIso α hA hB).inv ≫ A.str := by
  let g : B.a ⟶ A.a := (hB.to ((Endofunctor.Algebra.functorOfNatTrans α.inv).obj A)).f
  have hg := (hB.to ((Endofunctor.Algebra.functorOfNatTrans α.inv).obj A)).h
  change K.map g ≫ (α.inv.app A.a ≫ A.str) = B.str ≫ g at hg
  erw [← Category.assoc,α.inv.naturality,Category.assoc] at hg
  exact hg.symm

/-- The fields are proved together with the initial-algebra fold. -/
structure FoldComparisonData (hA : IsInitial A) (hB : IsInitial B) where
  iso : A.a ≅ B.a
  hom_constructor : A.str ≫ iso.hom = α.hom.app A.a ≫ K.map iso.hom ≫ B.str
  inv_constructor : B.str ≫ iso.inv = α.inv.app B.a ≫ H.map iso.inv ≫ A.str
  hom_fold : iso.hom = (hA.to ((Endofunctor.Algebra.functorOfNatTrans α.hom).obj B)).f
  inv_fold : iso.inv = (hB.to ((Endofunctor.Algebra.functorOfNatTrans α.inv).obj A)).f

def foldComparisonData (hA : IsInitial A) (hB : IsInitial B) :
    FoldComparisonData (A := A) (B := B) α hA hB where
  iso := initialFoldIso (A := A) (B := B) α hA hB
  hom_constructor := initialFoldIso_constructor (A := A) (B := B) α hA hB
  inv_constructor := initialFoldIso_inverse_constructor (A := A) (B := B) α hA hB
  hom_fold := initialFoldIso_hom (A := A) (B := B) α hA hB
  inv_fold := initialFoldIso_inv (A := A) (B := B) α hA hB

end Generic

def targetAlgebra : Endofunctor.Algebra R.inference :=
  (Endofunctor.Algebra.functorOfNatTrans ι.inferenceTransformation).obj
    (NumericalDerivation.codeAlgebra R')

def relabelFold : NumericalDerivation.codeAlgebra R ⟶ targetAlgebra ι :=
  (NumericalDerivation.codeInitial R).to _

/-- The checked folds and their laws are sealed together, so point-value statements do not
unfold the chosen initiality implementation. -/
opaque relabelData :
    FoldComparisonData (A := NumericalDerivation.codeAlgebra R)
      (B := NumericalDerivation.codeAlgebra R') (inferenceIso ι κ hικ hκι)
      (NumericalDerivation.codeInitial R) (NumericalDerivation.codeInitial R') :=
  foldComparisonData (A := NumericalDerivation.codeAlgebra R)
    (B := NumericalDerivation.codeAlgebra R') (inferenceIso ι κ hικ hκι)
    (NumericalDerivation.codeInitial R) (NumericalDerivation.codeInitial R')

def overIso : (NumericalDerivation.codeAlgebra R).a ≅
    (NumericalDerivation.codeAlgebra R').a := (relabelData ι κ hικ hκι).iso

def codeIso : NumericalDerivation.codeObject R ≅ NumericalDerivation.codeObject R' :=
  (Over.forget F).mapIso (overIso ι κ hικ hκι)

@[reassoc (attr := simp)] theorem conclusion :
    (codeIso ι κ hικ hκι).hom ≫ NumericalDerivation.codeConclusion R' =
      NumericalDerivation.codeConclusion R :=
  Over.w (overIso ι κ hικ hκι).hom

@[reassoc (attr := simp)] theorem inverse_conclusion :
    (codeIso ι κ hικ hκι).inv ≫ NumericalDerivation.codeConclusion R =
      NumericalDerivation.codeConclusion R' :=
  Over.w (overIso ι κ hικ hκι).inv

/-- The relabelling fold satisfies the proved constructor law. -/
abbrev constructor := (relabelData ι κ hικ hκι).hom_constructor
abbrev inverse_constructor := (relabelData ι κ hικ hκι).inv_constructor
abbrev relabel_is_fold := (relabelData ι κ hικ hκι).hom_fold
abbrev inverse_is_fold := (relabelData ι κ hικ hκι).inv_fold

def inputRelabel (i : Fin (N + 1)) :
    R.ruleObject (NumericalDerivation.codeAlgebra R).a i ⟶
      R'.ruleObject (NumericalDerivation.codeAlgebra R').a i :=
  ι.mapRule (NumericalDerivation.codeAlgebra R).a i ≫
    R'.ruleMap (overIso ι κ hικ hκι).hom i

@[reassoc (attr := simp)] theorem input_label (i : Fin (N + 1)) :
    inputRelabel ι κ hικ hκι i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ι.map i := by
  simp [inputRelabel]

@[reassoc (attr := simp)] theorem input_children (i : Fin (N + 1)) :
    inputRelabel ι κ hικ hκι i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (codeIso ι κ hικ hκι).hom i.val := by
  simp [inputRelabel,codeIso]

/-- In each branch the forward map replaces precisely the rule label
and applies itself, in order, to that node's children. -/
theorem branch_constructor (i : Fin (N + 1)) :
    inputRelabel ι κ hικ hκι i ≫
        Sigma.ι (R'.ruleObject (NumericalDerivation.codeAlgebra R').a) i ≫
          (NumericalDerivation.codeAlgebra R').str.left =
      Sigma.ι (R.ruleObject (NumericalDerivation.codeAlgebra R).a) i ≫
        (NumericalDerivation.codeAlgebra R).str.left ≫ (codeIso ι κ hικ hκι).hom := by
  have h := congrArg (fun f : R.inference.obj (NumericalDerivation.codeAlgebra R).a ⟶
      (NumericalDerivation.codeAlgebra R').a =>
    Sigma.ι (R.ruleObject (NumericalDerivation.codeAlgebra R).a) i ≫ f.left) (constructor ι κ hικ hκι)
  simpa only [inferenceIso,RulePresentation.Hom.inferenceTransformation,RulePresentation.inference,
    Over.homMk_left,Over.comp_left,Category.assoc,Sigma.ι_map_assoc,
    inputRelabel,codeIso,overIso,Functor.mapIso_hom,Over.forget_map] using h.symm

/-- The fold is computed on original unary proof words. -/
theorem forward_realizer :
    ∃ p : ℕ → Part ℕ, Partrec p ∧
      ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject R),
        p x.val = Part.some (((codeIso ι κ hικ hκι).hom.toFun x).val) := by
  exact (codeIso ι κ hικ hκι).hom.represented

theorem backward_realizer :
    ∃ p : ℕ → Part ℕ, Partrec p ∧
      ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject R'),
        p x.val = Part.some (((codeIso ι κ hικ hκι).inv.toFun x).val) := by
  exact (codeIso ι κ hικ hκι).inv.represented

end CategoricalEssentialIncompleteness.V46.NumericalRuleRelabel
