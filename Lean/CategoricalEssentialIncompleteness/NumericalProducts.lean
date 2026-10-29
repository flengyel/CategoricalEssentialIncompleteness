/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.NumericalEmbedding
import CategoricalEssentialIncompleteness.PERProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Numerical binary products and their preservation

The product carrier uses recursive tuple coding and is proved infinite and
recursive. Its total projections form a categorical product. An explicit
isomorphism identifies its image under J with the product of equality PERs,
and J preserves all binary products.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

def product (X Y : Numerical) : Numerical where
  carrier := {n | (Nat.unpair n).1 ∈ X.carrier ∧ (Nat.unpair n).2 ∈ Y.carrier}
  recursive := by
    classical
    apply Computable.computablePred
    simpa using
      Primrec.and.to_comp.comp
        (X.recursive.decide.comp (Computable.fst.comp Computable.unpair))
        (Y.recursive.decide.comp (Computable.snd.comp Computable.unpair))
  infinite := by
    obtain ⟨y, hy⟩ := Y.infinite.nonempty
    apply Set.infinite_of_injOn_mapsTo (f := fun x ↦ Nat.pair x y) _ _ X.infinite
    · intro a _ b _ hab
      exact (Nat.pair_eq_pair.mp hab).1
    · intro a ha
      simpa using And.intro ha hy

def totalFromFunction {X Y : Numerical} (f : ℕ → ℕ) (hf : Computable f)
    (h : ∀ n ∈ X.carrier, f n ∈ Y.carrier) : totalObject X ⟶ totalObject Y :=
  let t : NumericalPER.Representative (NumericalPER.discrete X.carrier)
      (NumericalPER.discrete Y.carrier) :=
    { val n := Part.some (f n)
      computable := hf
      total := fun _ _ ↦ Part.some_dom _
      respects := by
        intro n m a b hn ha hb
        obtain ⟨hn, rfl⟩ := hn
        obtain rfl := Part.mem_some_iff.mp ha
        obtain rfl := Part.mem_some_iff.mp hb
        exact ⟨h _ hn, rfl⟩ }
  ⟨ofDiscreteRepresentative t, ofDiscreteRepresentative_total t⟩

def totalProduct (X Y : Total) : Total := totalObject (product X.obj Y.obj)

def fst (X Y : Total) : totalProduct X Y ⟶ X :=
  totalFromFunction (fun n ↦ (Nat.unpair n).1)
    (Computable.fst.comp Computable.unpair) (fun _ h ↦ h.1)

def snd (X Y : Total) : totalProduct X Y ⟶ Y :=
  totalFromFunction (fun n ↦ (Nat.unpair n).2)
    (Computable.snd.comp Computable.unpair) (fun _ h ↦ h.2)

/-- The comparison is represented by the identity on coded pairs in both directions. -/
def productIso (X Y : Total) :
    toPER.obj (totalProduct X Y) ≅ NumericalPER.product (toPER.obj X) (toPER.obj Y) :=
  NumericalPER.relationIso _ _ (by
    intro n m
    change ((Nat.unpair n).1 ∈ X.obj.carrier ∧ (Nat.unpair n).2 ∈ Y.obj.carrier) ∧ n = m ↔
      ((Nat.unpair n).1 ∈ X.obj.carrier ∧ (Nat.unpair n).1 = (Nat.unpair m).1) ∧
      ((Nat.unpair n).2 ∈ Y.obj.carrier ∧ (Nat.unpair n).2 = (Nat.unpair m).2)
    constructor
    · rintro ⟨⟨hx, hy⟩, rfl⟩
      exact ⟨⟨hx, rfl⟩, ⟨hy, rfl⟩⟩
    · intro h
      refine ⟨⟨h.1.1, h.2.1⟩, ?_⟩
      have hp := congrArg (fun p : ℕ × ℕ ↦ Nat.pair p.1 p.2) (Prod.ext h.1.2 h.2.2)
      simpa only [Nat.pair_unpair] using hp)

@[simp, reassoc] theorem productIso_hom_fst (X Y : Total) :
    (productIso X Y).hom ≫ NumericalPER.fst _ _ = toPER.map (fst X Y) := by
  apply (NumericalPER.discrete_arrow_eq_iff _ _).mpr
  intro n hn
  change (Part.some n).bind (fun k ↦ Part.some (Nat.unpair k).1) =
    (supportIdentity (product X.obj Y.obj).carrier n).bind
      (fun k ↦ Part.some (Nat.unpair k).1)
  rw [supportIdentity, Part.assert_pos (show n ∈ (product X.obj Y.obj).carrier from hn.1)]

@[simp, reassoc] theorem productIso_hom_snd (X Y : Total) :
    (productIso X Y).hom ≫ NumericalPER.snd _ _ = toPER.map (snd X Y) := by
  apply (NumericalPER.discrete_arrow_eq_iff _ _).mpr
  intro n hn
  change (Part.some n).bind (fun k ↦ Part.some (Nat.unpair k).2) =
    (supportIdentity (product X.obj Y.obj).carrier n).bind
      (fun k ↦ Part.some (Nat.unpair k).2)
  rw [supportIdentity, Part.assert_pos (show n ∈ (product X.obj Y.obj).carrier from hn.1)]

/-- The image of the numerical product cone has the full PER product property. -/
def productMapIsLimit (X Y : Total) :
    IsLimit (BinaryFan.mk (toPER.map (fst X Y)) (toPER.map (snd X Y))) := by
  let e := productIso X Y
  have hf : e.inv ≫ toPER.map (fst X Y) = NumericalPER.fst _ _ := by
    rw [← productIso_hom_fst, ← Category.assoc]
    simp [e]
  have hg : e.inv ≫ toPER.map (snd X Y) = NumericalPER.snd _ _ := by
    rw [← productIso_hom_snd, ← Category.assoc]
    simp [e]
  exact (NumericalPER.productIsLimit (toPER.obj X) (toPER.obj Y)).ofIsoLimit
    (BinaryFan.ext e.symm hf.symm hg.symm)

def productIsLimit (X Y : Total) : IsLimit (BinaryFan.mk (fst X Y) (snd X Y)) :=
  isLimitOfReflectsOfMapIsLimit toPER _ _ (productMapIsLimit X Y)

instance totalProductHasLimit (X Y : Total) : HasLimit (Limits.pair X Y) :=
  ⟨⟨_, productIsLimit X Y⟩⟩

instance totalHasBinaryProducts : HasBinaryProducts Total :=
  hasBinaryProducts_of_hasLimit_pair Total

instance toPER_preservesPair (X Y : Total) : PreservesLimit (Limits.pair X Y) toPER :=
  preservesLimit_of_preserves_limit_cone (productIsLimit X Y)
    ((isLimitMapConeBinaryFanEquiv toPER _ _).symm (productMapIsLimit X Y))

instance toPER_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) toPER where
  preservesLimit := by
    intro K
    exact preservesLimit_of_iso_diagram toPER (diagramIsoPair K).symm

end Numerical
end CategoricalEssentialIncompleteness
