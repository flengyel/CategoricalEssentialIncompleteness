/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.V46Inference

/-! # Finite leaf lists on the original typed derivation algebra -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.DerivationFiniteSupport

variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
variable {F X : D} (R : RulePresentation F 2) (L : StableListAlgebra X)

def carrier : Over F := Over.mk (prod.fst : F ⨯ L.algebra.carrier ⟶ F)

/-- A nullary rule contributes its prescribed leaf list; a unary rule
retains its child's list; a binary rule concatenates the two lists. -/
def nodeList (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    (i : Fin 3) → R.ruleObject (carrier L) i ⟶ L.algebra.carrier :=
  Fin.cases (pullback.fst _ _ ≫ leaf)
    (Fin.cases (pullback.snd _ _ ≫ prod.snd)
      (Fin.cases (pullback.snd _ _ ≫ prod.map prod.snd prod.snd ≫ L.append)
        (fun i => i.elim0)))

def algebra (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    Endofunctor.Algebra R.inference where
  a := carrier L
  str := Over.homMk
    (Sigma.desc fun i => prod.lift (R.ruleConclusion (carrier L) i) (nodeList R L leaf i))
    (by
      apply Sigma.hom_ext
      intro i
      simp [carrier, RulePresentation.inference])

variable (P : Endofunctor.Algebra R.inference) (initial : IsInitial P)

def fold (leaf : R.instances 0 ⟶ L.algebra.carrier) : P.a ⟶ carrier L :=
  (initial.to (algebra R L leaf)).f

def collect (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    P.a.left ⟶ L.algebra.carrier := (fold R L P initial leaf).left ≫ prod.snd

@[reassoc] theorem fold_conclusion (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    (fold R L P initial leaf).left ≫ prod.fst = P.a.hom :=
  Over.w (fold R L P initial leaf)

def ruleConstructor (i : Fin 3) : R.ruleObject P.a i ⟶ P.a.left :=
  Sigma.ι (R.ruleObject P.a) i ≫ P.str.left

@[reassoc] theorem constructor_collect (leaf : R.instances 0 ⟶ L.algebra.carrier)
    (i : Fin 3) :
    ruleConstructor R P i ≫ collect R L P initial leaf =
      R.ruleMap (fold R L P initial leaf) i ≫ nodeList R L leaf i := by
  have h := congrArg Over.Hom.left (initial.to (algebra R L leaf)).h.symm
  have hi := congrArg
    (fun f => Sigma.ι (R.ruleObject P.a) i ≫ f ≫ prod.snd) h
  simpa [ruleConstructor, collect, fold, algebra, RulePresentation.inference,
    Category.assoc] using hi

@[reassoc] theorem nullary_collect (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    ruleConstructor R P 0 ≫ collect R L P initial leaf = pullback.fst _ _ ≫ leaf := by
  rw [constructor_collect]
  change R.ruleMap (fold R L P initial leaf) 0 ≫ (pullback.fst _ _ ≫ leaf) = _
  rw [← Category.assoc, RulePresentation.ruleMap_fst]

@[reassoc] theorem unary_collect (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    ruleConstructor R P 1 ≫ collect R L P initial leaf =
      pullback.snd (R.premises 1) (finitePowerMap P.a.hom 1) ≫ collect R L P initial leaf := by
  rw [constructor_collect]
  change R.ruleMap (fold R L P initial leaf) 1 ≫ (pullback.snd _ _ ≫ prod.snd) = _
  rw [← Category.assoc, RulePresentation.ruleMap_snd, Category.assoc]
  rfl

@[reassoc] theorem binary_collect (leaf : R.instances 0 ⟶ L.algebra.carrier) :
    ruleConstructor R P 2 ≫ collect R L P initial leaf =
      pullback.snd (R.premises 2) (finitePowerMap P.a.hom 2) ≫
        prod.map (collect R L P initial leaf) (collect R L P initial leaf) ≫ L.append := by
  rw [constructor_collect]
  change R.ruleMap (fold R L P initial leaf) 2 ≫
    (pullback.snd _ _ ≫ prod.map prod.snd prod.snd ≫ L.append) = _
  rw [← Category.assoc, RulePresentation.ruleMap_snd]
  simp only [finitePowerMap, Category.assoc, prod.map_map_assoc, collect]

variable [FinitaryExtensive D]

/-- The identity leaf assignment lists the original nullary rule labels. -/
def nullaryLabels (K : StableListAlgebra (R.instances 0)) :
    P.a.left ⟶ K.algebra.carrier := collect R K P initial K.singleton

end CategoricalEssentialIncompleteness.V46.DerivationFiniteSupport
