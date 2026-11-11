/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProofObjects

/-! # The actual one-node proof morphisms -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax

open EffectiveFork (V centerIdem leftIdem rightIdem)
open EnumerableCarriers (support support_re val)

def leafCode (leaf : ℕ → ProofTree) (x : ℕ) : ℕ := ProofTree.encode (leaf x)

theorem leafCode_computable {leaf : ℕ → ProofTree} (hl : Computable leaf) :
    Computable (leafCode leaf) :=
  Computable.comp (f := ProofTree.encode) (g := leaf) ProofTree.encode_computable hl

theorem proofRelabel_leaf (leaf : ℕ → ProofTree)
    (hn : ∀ f x,(leaf x).mapAtoms f=leaf (f x)) (f : ℕ → ℕ) (x : ℕ) :
    proofRelabelCode f (leafCode leaf x)=leafCode leaf (f x) := by
  unfold proofRelabelCode leafCode
  rw [ProofTree.decode_encode,hn]

theorem mem_leafCarrier {A B : Set ℕ} (hA : REPred (· ∈ A)) (hB : REPred (· ∈ B))
    (leaf : ℕ → ProofTree) (x : ℕ) (hx : ProofTree.Valid A B (leaf x)) :
    leafCode leaf x ∈ (proofCarrier A B hA hB).support := by
  apply (mem_proofCarrier A B hA hB _).mpr
  unfold leafCode
  rw [ProofTree.decode_encode]
  exact hx

def leafMap (a b d : Idem V) (leaf : ℕ → ProofTree) (hl : Computable leaf)
    (hn : ∀ f x,(leaf x).mapAtoms f=leaf (f x))
    (h0 : ∀ x ∈ support (centerIdem d),
      ProofTree.Valid (support (centerIdem a)) (support (centerIdem b)) (leaf x))
    (h1 : ∀ x ∈ support (leftIdem d),
      ProofTree.Valid (support (leftIdem a)) (support (leftIdem b)) (leaf x))
    (h2 : ∀ x ∈ support (rightIdem d),
      ProofTree.Valid (support (rightIdem a)) (support (rightIdem b)) (leaf x)) :
    EffectiveFork.domainObject d ⟶ Prf a b :=
  EffectiveFork.computedMap (X := EffectiveFork.domainObject d) (Y := Prf a b)
    (leafCode leaf) (leafCode leaf) (leafCode leaf)
    (leafCode_computable hl) (leafCode_computable hl) (leafCode_computable hl)
    (fun x hx => mem_leafCarrier (support_re (centerIdem a))
      (support_re (centerIdem b)) leaf x (h0 x hx))
    (fun x hx => mem_leafCarrier (support_re (leftIdem a))
      (support_re (leftIdem b)) leaf x (h1 x hx))
    (fun x hx => mem_leafCarrier (support_re (rightIdem a))
      (support_re (rightIdem b)) leaf x (h2 x hx))
    (by
      intro x u hu
      obtain ⟨hx,hu⟩ := (EnumerableCarriers.mem_val_restrictMap V.leftMap
        (centerIdem d) (leftIdem d) (EffectiveFork.closed_left d) x u).mp hu
      apply (mem_proofMap (support_re (centerIdem a)) (support_re (centerIdem b))
        (support_re (leftIdem a)) (support_re (leftIdem b)) _ EffectiveFork.leftCoordinate_computable
        (left_axioms a) (left_axioms b) _ _).mpr
      refine ⟨mem_leafCarrier (support_re (centerIdem a))
        (support_re (centerIdem b)) leaf x (h0 x hx),?_⟩
      rw [proofRelabel_leaf leaf hn,← (EffectiveFork.mem_V_left x u).mp hu])
    (by
      intro x u hu
      obtain ⟨hx,hu⟩ := (EnumerableCarriers.mem_val_restrictMap V.rightMap
        (centerIdem d) (rightIdem d) (EffectiveFork.closed_right d) x u).mp hu
      apply (mem_proofMap (support_re (centerIdem a)) (support_re (centerIdem b))
        (support_re (rightIdem a)) (support_re (rightIdem b)) _ EffectiveFork.rightCoordinate_computable
        (right_axioms a) (right_axioms b) _ _).mpr
      refine ⟨mem_leafCarrier (support_re (centerIdem a))
        (support_re (centerIdem b)) leaf x (h0 x hx),?_⟩
      rw [proofRelabel_leaf leaf hn,← (EffectiveFork.mem_V_right x u).mp hu])

theorem leafMap_total (a b d : Idem V) (leaf : ℕ → ProofTree) (hl : Computable leaf)
    (hn : ∀ f x,(leaf x).mapAtoms f=leaf (f x))
    (h0 : ∀ x ∈ support (centerIdem d),
      ProofTree.Valid (support (centerIdem a)) (support (centerIdem b)) (leaf x))
    (h1 : ∀ x ∈ support (leftIdem d),
      ProofTree.Valid (support (leftIdem a)) (support (leftIdem b)) (leaf x))
    (h2 : ∀ x ∈ support (rightIdem d),
      ProofTree.Valid (support (rightIdem a)) (support (rightIdem b)) (leaf x)) :
    isTotal (leafMap a b d leaf hl hn h0 h1 h2) := by
  unfold leafMap
  apply EffectiveFork.computedMap_total

def positiveLeaves (a b : Idem V) : EffectiveFork.domainObject a ⟶ Prf a b :=
  leafMap a b a ProofTree.positive ProofTree.positive_computable (fun _ _ => rfl)
    (fun _ hx => ⟨_,Concludes.positive hx⟩) (fun _ hx => ⟨_,Concludes.positive hx⟩)
    (fun _ hx => ⟨_,Concludes.positive hx⟩)

def negativeLeaves (a b : Idem V) : EffectiveFork.domainObject b ⟶ Prf a b :=
  leafMap a b b ProofTree.negative ProofTree.negative_computable (fun _ _ => rfl)
    (fun _ hx => ⟨_,Concludes.negative hx⟩) (fun _ hx => ⟨_,Concludes.negative hx⟩)
    (fun _ hx => ⟨_,Concludes.negative hx⟩)

theorem positiveLeaves_total (a b : Idem V) : isTotal (positiveLeaves a b) :=
  leafMap_total _ _ _ _ _ _ _ _ _

theorem negativeLeaves_total (a b : Idem V) : isTotal (negativeLeaves a b) :=
  leafMap_total _ _ _ _ _ _ _ _ _

theorem numerical_leaf_conclusion (a b d : Idem EffectiveFork.natCarrier)
    (leaf : ℕ → ProofTree) (hl : Computable leaf)
    (hv : ∀ x ∈ support d,ProofTree.Valid (support a) (support b) (leaf x))
    (g : ℕ → ℕ) (hg : Computable g)
    (hc : ∀ x ∈ support d,conclusionCode (leafCode leaf x)=g x) :
    EnumerableCarriers.totalFromFunction (leafCode leaf) (leafCode_computable hl)
      (fun x hx => mem_leafCarrier (support_re a) (support_re b) leaf x (hv x hx)) ≫
      conclusionArrow (support a) (support b) (support_re a) (support_re b)=
      EnumerableCarriers.into d ≫ natArrow g hg := by
  apply EnumerableCarriers.val_injective
  apply PFun.ext
  intro x y
  rw [EnumerableCarriers.mem_val_comp,EnumerableCarriers.mem_val_comp]
  constructor
  · rintro ⟨p,hp,hy⟩
    obtain ⟨hx,rfl⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ x p).mp hp
    obtain ⟨_,he⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ _ y).mp hy
    exact ⟨x,(EnumerableCarriers.mem_val_idem d x x).mpr ⟨hx,rfl⟩,
      (mem_natArrow g hg x y).mpr (he.trans (hc x hx))⟩
  · rintro ⟨z,hz,hy⟩
    obtain ⟨hx,he⟩ := (EnumerableCarriers.mem_val_idem d x z).mp hz
    subst z
    refine ⟨leafCode leaf x,(EnumerableCarriers.mem_totalFromFunction _ _ _ _ _).mpr ⟨hx,rfl⟩,
      (EnumerableCarriers.mem_totalFromFunction _ _ _ _ y).mpr ?_⟩
    exact ⟨mem_leafCarrier (support_re a) (support_re b) leaf x (hv x hx),
      ((mem_natArrow g hg x y).mp hy).trans (hc x hx).symm⟩

theorem positiveLeaves_conclusion (a b : Idem V) :
    positiveLeaves a b ≫ conclusion a b=EffectiveFork.domainInclusion a ≫ theta := by
  apply EffectiveFork.Hom.ext
  all_goals
    apply numerical_leaf_conclusion _ _ _ ProofTree.positive ProofTree.positive_computable
      (fun _ hx => ⟨_,Concludes.positive hx⟩) atomCode atomCode_computable
    intro x hx
    exact conclusionCode_of_concludes (B := ∅) (Concludes.positive hx)

theorem natArrow_comp (f g : ℕ → ℕ) (hf : Computable f) (hg : Computable g) :
    natArrow f hf ≫ natArrow g hg=natArrow (g ∘ f) (hg.comp hf) :=
  EnumerableCarriers.totalFromFunction_comp f g hf hg _ _

theorem negativeLeaves_conclusion (a b : Idem V) :
    negativeLeaves a b ≫ conclusion a b=(EffectiveFork.domainInclusion b ≫ theta) ≫ nu := by
  apply EffectiveFork.Hom.ext
  all_goals
    change _=(EnumerableCarriers.into _ ≫ natArrow atomCode atomCode_computable) ≫
      natArrow negCode negCode_computable
    rw [Category.assoc,natArrow_comp]
    apply numerical_leaf_conclusion _ _ _ ProofTree.negative ProofTree.negative_computable
      (fun _ hx => ⟨_,Concludes.negative hx⟩) (negCode ∘ atomCode)
      (negCode_computable.comp atomCode_computable)
    intro x hx
    exact conclusionCode_of_concludes (A := ∅) (Concludes.negative hx)

end CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax
