/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkSyntaxInitialAlgebra
public import CategoricalEssentialIncompleteness.ForkProofObjects
public import CategoricalEssentialIncompleteness.EffectiveForkExtensive
public import CategoricalEssentialIncompleteness.V46ForkDerivationInference

/-! # The actual fork formula, axiom and rule objects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation
open EffectiveFork (Total)

/-- The native product coding is compared with the chosen categorical product. -/
def codedProduct (X Y : Total) : Total := ⟨EffectiveFork.product X.obj Y.obj⟩

def codedFst (X Y : Total) : codedProduct X Y ⟶ X :=
  ⟨EffectiveFork.first _ _, (EffectiveFork.total_iff _).mpr
    ⟨EnumerableCarriers.partialFst_total _ _, EnumerableCarriers.partialFst_total _ _,
      EnumerableCarriers.partialFst_total _ _⟩⟩

def codedSnd (X Y : Total) : codedProduct X Y ⟶ Y :=
  ⟨EffectiveFork.second _ _, (EffectiveFork.total_iff _).mpr
    ⟨EnumerableCarriers.partialSnd_total _ _, EnumerableCarriers.partialSnd_total _ _,
      EnumerableCarriers.partialSnd_total _ _⟩⟩

def codedPair {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ codedProduct X Y :=
  ⟨EffectiveFork.partialPair f.hom g.hom, (EffectiveFork.total_iff _).mpr
    ⟨EnumerableCarriers.partialPair_total _ _
        ((EffectiveFork.total_iff _).mp f.property).1 ((EffectiveFork.total_iff _).mp g.property).1,
      EnumerableCarriers.partialPair_total _ _
        ((EffectiveFork.total_iff _).mp f.property).2.1 ((EffectiveFork.total_iff _).mp g.property).2.1,
      EnumerableCarriers.partialPair_total _ _
        ((EffectiveFork.total_iff _).mp f.property).2.2 ((EffectiveFork.total_iff _).mp g.property).2.2⟩⟩

@[simp] theorem codedPair_fst {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    codedPair f g ≫ codedFst X Y = f := by
  apply WideSubcategory.hom_ext
  apply EffectiveFork.Hom.ext
  all_goals
    change EnumerableCarriers.partialPair _ _ ≫ EnumerableCarriers.partialFst _ _ = _
    rw [EnumerableCarriers.partialPair_fst]
  · rw [((EffectiveFork.total_iff _).mp g.property).1, Category.id_comp]
  · rw [((EffectiveFork.total_iff _).mp g.property).2.1, Category.id_comp]
  · rw [((EffectiveFork.total_iff _).mp g.property).2.2, Category.id_comp]

@[simp] theorem codedPair_snd {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    codedPair f g ≫ codedSnd X Y = g := by
  apply WideSubcategory.hom_ext
  apply EffectiveFork.Hom.ext
  all_goals
    change EnumerableCarriers.partialPair _ _ ≫ EnumerableCarriers.partialSnd _ _ = _
    rw [EnumerableCarriers.partialPair_snd]
  · rw [((EffectiveFork.total_iff _).mp f.property).1, Category.id_comp]
  · rw [((EffectiveFork.total_iff _).mp f.property).2.1, Category.id_comp]
  · rw [((EffectiveFork.total_iff _).mp f.property).2.2, Category.id_comp]

theorem codedProduct_hom_ext {W X Y : Total} {f g : W ⟶ codedProduct X Y}
    (hf : f ≫ codedFst X Y = g ≫ codedFst X Y)
    (hg : f ≫ codedSnd X Y = g ≫ codedSnd X Y) : f = g := by
  apply WideSubcategory.hom_ext
  apply EffectiveFork.Hom.ext
  · apply EnumerableCarriers.partial_product_hom_ext
    · exact congrArg (fun k : W ⟶ X => k.hom.center) hf
    · exact congrArg (fun k : W ⟶ Y => k.hom.center) hg
  · apply EnumerableCarriers.partial_product_hom_ext
    · exact congrArg (fun k : W ⟶ X => k.hom.left) hf
    · exact congrArg (fun k : W ⟶ Y => k.hom.left) hg
  · apply EnumerableCarriers.partial_product_hom_ext
    · exact congrArg (fun k : W ⟶ X => k.hom.right) hf
    · exact congrArg (fun k : W ⟶ Y => k.hom.right) hg

@[simp] theorem codedPair_eta {W X Y : Total} (f : W ⟶ codedProduct X Y) :
    codedPair (f ≫ codedFst X Y) (f ≫ codedSnd X Y) = f := by
  apply codedProduct_hom_ext <;> simp

def codedProductIsLimit (X Y : Total) : IsLimit (BinaryFan.mk (codedFst X Y) (codedSnd X Y)) :=
  BinaryFan.isLimitMk (fun s => codedPair s.fst s.snd)
    (fun _ => codedPair_fst _ _) (fun _ => codedPair_snd _ _) (by
      intro s m hm0 hm1
      apply codedProduct_hom_ext
      · exact hm0.trans (codedPair_fst s.fst s.snd).symm
      · exact hm1.trans (codedPair_snd s.fst s.snd).symm)

def productComparison (X Y : Total) : X ⨯ Y ≅ codedProduct X Y :=
  (prodIsProd X Y).conePointUniqueUpToIso (codedProductIsLimit X Y)

@[simp, reassoc] theorem productComparison_fst (X Y : Total) :
    (productComparison X Y).hom ≫ codedFst X Y = prod.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd X Y) (codedProductIsLimit X Y) ⟨.left⟩

@[simp, reassoc] theorem productComparison_snd (X Y : Total) :
    (productComparison X Y).hom ≫ codedSnd X Y = prod.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd X Y) (codedProductIsLimit X Y) ⟨.right⟩

@[simp,reassoc] theorem productComparison_inv_fst (X Y : Total) :
    (productComparison X Y).inv ≫ prod.fst = codedFst X Y :=
  IsLimit.conePointUniqueUpToIso_inv_comp (prodIsProd X Y) (codedProductIsLimit X Y) ⟨.left⟩

@[simp,reassoc] theorem productComparison_inv_snd (X Y : Total) :
    (productComparison X Y).inv ≫ prod.snd = codedSnd X Y :=
  IsLimit.conePointUniqueUpToIso_inv_comp (prodIsProd X Y) (codedProductIsLimit X Y) ⟨.right⟩

/-- The comparison is the actual restriction-product pairing of the
chosen total projections, rather than an unspecified product isomorphism. -/
theorem productComparison_hom (X Y : Total) :
    (productComparison X Y).hom = codedPair (prod.fst : X ⨯ Y ⟶ X) prod.snd := by
  apply codedProduct_hom_ext <;> simp

theorem productComparison_inv (X Y : Total) :
    (productComparison X Y).inv = prod.lift (codedFst X Y) (codedSnd X Y) := by
  apply prod.hom_ext <;> simp

@[simp,reassoc] theorem productComparison_pair {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    prod.lift f g ≫ (productComparison X Y).hom = codedPair f g := by
  apply codedProduct_hom_ext <;> simp

def sentenceObject : Total := ⟨ForkSyntax.S⟩
def variableObject : Total := ⟨EffectiveFork.V⟩
def atom : variableObject ⟶ sentenceObject := ⟨ForkSyntax.theta, ForkSyntax.theta_total⟩
def negation : sentenceObject ⟶ sentenceObject := ⟨ForkSyntax.nu, ForkSyntax.nu_total⟩
def implication : sentenceObject ⨯ sentenceObject ⟶ sentenceObject :=
  (productComparison sentenceObject sentenceObject).hom ≫
    ⟨ForkSyntax.implication, ForkSyntax.implication_total⟩

def H1 : sentenceObject ⨯ sentenceObject ⟶ sentenceObject :=
  prod.lift prod.fst (prod.lift prod.snd prod.fst ≫ implication) ≫ implication

def H2 : (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject ⟶ sentenceObject :=
  prod.lift
    (prod.lift (prod.fst ≫ prod.fst)
      (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ implication) ≫ implication)
    (prod.lift
      (prod.lift (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd) ≫ implication)
      (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ implication) ≫ implication) ≫ implication

def H3 : sentenceObject ⨯ sentenceObject ⟶ sentenceObject :=
  prod.lift (prod.lift (prod.snd ≫ negation) (prod.fst ≫ negation) ≫ implication)
    (prod.lift prod.fst prod.snd ≫ implication) ≫ implication

def axiomDomain (a : Idem EffectiveFork.V) : Total := ⟨EffectiveFork.domainObject a⟩
def axiomInclusion (a : Idem EffectiveFork.V) : axiomDomain a ⟶ variableObject :=
  ⟨EffectiveFork.domainInclusion a, EffectiveFork.domainInclusion_total a⟩

def axiomCoefficients (a b : Idem EffectiveFork.V) : Fin 5 → Total :=
  ![sentenceObject ⨯ sentenceObject, (sentenceObject ⨯ sentenceObject) ⨯ sentenceObject,
    sentenceObject ⨯ sentenceObject, axiomDomain a, axiomDomain b]

def axiomConclusions (a b : Idem EffectiveFork.V) :
    ∀ i, axiomCoefficients a b i ⟶ sentenceObject :=
  Fin.cases H1 (Fin.cases H2 (Fin.cases H3
    (Fin.cases (axiomInclusion a ≫ atom)
      (Fin.cases (axiomInclusion b ≫ atom ≫ negation) (fun i => Fin.elim0 i)))))

def axiomObject (a b : Idem EffectiveFork.V) : Total := ∐ axiomCoefficients a b

def lambda (a b : Idem EffectiveFork.V) : axiomObject a b ⟶ sentenceObject :=
  Sigma.desc (axiomConclusions a b)

@[simp,reassoc] theorem lambda_logical1 (a b : Idem EffectiveFork.V) :
    Sigma.ι (axiomCoefficients a b) 0 ≫ lambda a b = H1 :=
  Sigma.ι_comp_desc (axiomConclusions a b) 0

@[simp,reassoc] theorem lambda_logical2 (a b : Idem EffectiveFork.V) :
    Sigma.ι (axiomCoefficients a b) 1 ≫ lambda a b = H2 :=
  Sigma.ι_comp_desc (axiomConclusions a b) 1

@[simp,reassoc] theorem lambda_logical3 (a b : Idem EffectiveFork.V) :
    Sigma.ι (axiomCoefficients a b) 2 ≫ lambda a b = H3 :=
  Sigma.ι_comp_desc (axiomConclusions a b) 2

@[simp,reassoc] theorem lambda_positive (a b : Idem EffectiveFork.V) :
    Sigma.ι (axiomCoefficients a b) 3 ≫ lambda a b = axiomInclusion a ≫ atom :=
  Sigma.ι_comp_desc (axiomConclusions a b) 3

@[simp,reassoc] theorem lambda_negative (a b : Idem EffectiveFork.V) :
    Sigma.ι (axiomCoefficients a b) 4 ≫ lambda a b = axiomInclusion b ≫ atom ≫ negation :=
  Sigma.ι_comp_desc (axiomConclusions a b) 4

def rules (a b : Idem EffectiveFork.V) : RulePresentation sentenceObject 2 :=
  ForkInference.rules (lambda a b) implication

def printedH (a b : Idem EffectiveFork.V) : Over sentenceObject ⥤ Over sentenceObject :=
  ForkInference.printedH (lambda a b) implication

def inferenceIso (a b : Idem EffectiveFork.V) : (rules a b).inference ≅ printedH a b :=
  ForkInference.inferenceIso (lambda a b) implication

def proofObject (a b : Idem EffectiveFork.V) : Total := ⟨ForkSyntax.Prf a b⟩

def conclusion (a b : Idem EffectiveFork.V) : proofObject a b ⟶ sentenceObject :=
  ⟨ForkSyntax.conclusion a b, ForkSyntax.conclusion_total a b⟩

@[simp] theorem conclusion_hom (a b : Idem EffectiveFork.V) :
    (conclusion a b).hom = ForkSyntax.conclusion a b := rfl
end CategoricalEssentialIncompleteness.V46.ForkDerivation
