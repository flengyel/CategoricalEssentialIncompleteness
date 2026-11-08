/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Inference
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
import Mathlib.Tactic.FinCases

/-! # The printed nullary-and-modus-ponens inference functor

This is the finite rule functor with no unary rules. Its comparison with
Ax + M is constructed, without an initial-algebra premise.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkInference
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {S Ax : D} (axioms : Ax ⟶ S) (implication : S ⨯ S ⟶ S)

def premise : S ⨯ S ⟶ S ⨯ S := prod.lift prod.fst implication

def rules : RulePresentation S 2 where
  instances := ![Ax, ⊥_ D, S ⨯ S]
  premises := Fin.cases (terminal.from Ax)
    (Fin.cases (initial.to S) (Fin.cases (premise implication) (fun i => Fin.elim0 i)))
  conclusion := Fin.cases axioms
    (Fin.cases (initial.to S) (Fin.cases prod.snd (fun i => Fin.elim0 i)))

@[simp] theorem rules_premises_zero :
    (rules axioms implication).premises 0 = terminal.from Ax := rfl
@[simp] theorem rules_premises_one :
    (rules axioms implication).premises 1 = initial.to S := rfl
@[simp] theorem rules_premises_two :
    (rules axioms implication).premises 2 = premise implication := rfl
@[simp] theorem rules_conclusion_zero :
    (rules axioms implication).conclusion 0 = axioms := rfl
@[simp] theorem rules_conclusion_one :
    (rules axioms implication).conclusion 1 = initial.to S := rfl
@[simp] theorem rules_conclusion_two :
    (rules axioms implication).conclusion 2 = prod.snd := rfl

def mpObject (Q : Over S) : D :=
  pullback (premise implication) (prod.map Q.hom Q.hom)

def mpConclusion (Q : Over S) : mpObject implication Q ⟶ S :=
  pullback.fst _ _ ≫ prod.snd

def mpMap {Q Q' : Over S} (h : Q ⟶ Q') : mpObject implication Q ⟶ mpObject implication Q' :=
  pullback.map _ _ _ _ (𝟙 _) (prod.map h.left h.left) (𝟙 _)
    (by simp) (by simp only [Category.comp_id, prod.map_map, Over.w h])

omit [FinitaryExtensive D] in
@[simp, reassoc (attr := simp)] theorem mpMap_fst {Q Q' : Over S} (h : Q ⟶ Q') :
    mpMap implication h ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [mpMap]

omit [FinitaryExtensive D] in
@[simp, reassoc (attr := simp)] theorem mpMap_snd {Q Q' : Over S} (h : Q ⟶ Q') :
    mpMap implication h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ prod.map h.left h.left := by
  simp [mpMap]

omit [FinitaryExtensive D] in
@[simp] theorem mpMap_id (Q : Over S) : mpMap implication (𝟙 Q) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

omit [FinitaryExtensive D] in
@[simp] theorem mpMap_comp {Q Q' Q'' : Over S} (h : Q ⟶ Q') (k : Q' ⟶ Q'') :
    mpMap implication (h ≫ k) = mpMap implication h ≫ mpMap implication k := by
  apply pullback.hom_ext <;> simp [prod.map_map, Category.assoc]

def printedH : Over S ⥤ Over S where
  obj Q := Over.mk (coprod.desc axioms (mpConclusion implication Q))
  map h := Over.homMk (coprod.map (𝟙 Ax) (mpMap implication h)) (by
    apply coprod.hom_ext <;> simp [mpConclusion])
  map_id Q := by
    apply Over.OverMorphism.ext
    change coprod.map (𝟙 Ax) (mpMap implication (𝟙 Q)) = 𝟙 _
    simp only [mpMap_id, coprod.map_id_id]
  map_comp h k := by
    apply Over.OverMorphism.ext
    change coprod.map (𝟙 Ax) (mpMap implication (h ≫ k)) =
      coprod.map (𝟙 Ax) (mpMap implication h) ≫ coprod.map (𝟙 Ax) (mpMap implication k)
    simp only [mpMap_comp, coprod.map_map, Category.id_comp]

def nullaryInputIso (Q : Over S) : (rules axioms implication).ruleObject Q 0 ≅ Ax where
  hom := pullback.fst _ _
  inv := (rules axioms implication).nullaryRule Q
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [Category.assoc,RulePresentation.nullaryRule_fst]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact terminal.hom_ext _ _
  inv_hom_id := (rules axioms implication).nullaryRule_fst Q

def unaryInputInitial (Q : Over S) : IsInitial ((rules axioms implication).ruleObject Q 1) := by
  let f : (rules axioms implication).ruleObject Q 1 ⟶ ⊥_ D := pullback.fst _ _
  exact IsInitial.ofStrict f initialIsInitial

private def toPrintedLeft (Q : Over S) :
    ((rules axioms implication).inference.obj Q).left ⟶ ((printedH axioms implication).obj Q).left :=
  Sigma.desc (Fin.cases (pullback.fst _ _ ≫ coprod.inl)
    (Fin.cases ((unaryInputInitial axioms implication Q).to _)
      (Fin.cases coprod.inr (fun i => Fin.elim0 i))))

@[simp, reassoc (attr := simp)] private theorem toPrintedLeft_ι_zero (Q : Over S) :
    Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫ toPrintedLeft axioms implication Q =
      pullback.fst ((rules axioms implication).premises 0) (finitePowerMap Q.hom 0) ≫ coprod.inl := by
  rw [toPrintedLeft,Sigma.ι_comp_desc]
  rfl

@[simp, reassoc (attr := simp)] private theorem toPrintedLeft_ι_two (Q : Over S) :
    Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫ toPrintedLeft axioms implication Q =
      coprod.inr := by
  rw [toPrintedLeft,Sigma.ι_comp_desc]
  rfl

private theorem toPrintedLeft_conclusion (Q : Over S) :
    toPrintedLeft axioms implication Q ≫ ((printedH axioms implication).obj Q).hom =
      ((rules axioms implication).inference.obj Q).hom := by
  apply Sigma.hom_ext
  intro i
  fin_cases i
  · change Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫
        toPrintedLeft axioms implication Q ≫ coprod.desc axioms (mpConclusion implication Q) =
      Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫
        Sigma.desc ((rules axioms implication).ruleConclusion Q)
    rw [← Category.assoc,toPrintedLeft_ι_zero,Category.assoc,coprod.inl_desc,Sigma.ι_comp_desc]
    rfl
  · exact (unaryInputInitial axioms implication Q).hom_ext _ _
  · change Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫
        toPrintedLeft axioms implication Q ≫ coprod.desc axioms (mpConclusion implication Q) =
      Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫
        Sigma.desc ((rules axioms implication).ruleConclusion Q)
    rw [← Category.assoc,toPrintedLeft_ι_two,coprod.inr_desc,Sigma.ι_comp_desc]
    rfl

def toPrinted (Q : Over S) :
    (rules axioms implication).inference.obj Q ⟶ (printedH axioms implication).obj Q :=
  Over.homMk (toPrintedLeft axioms implication Q) (toPrintedLeft_conclusion axioms implication Q)

private def fromPrintedLeft (Q : Over S) :
    ((printedH axioms implication).obj Q).left ⟶ ((rules axioms implication).inference.obj Q).left :=
  coprod.desc ((rules axioms implication).nullaryRule Q ≫
    Sigma.ι ((rules axioms implication).ruleObject Q) 0)
    (Sigma.ι ((rules axioms implication).ruleObject Q) 2)

private theorem fromPrintedLeft_conclusion (Q : Over S) :
    fromPrintedLeft axioms implication Q ≫ ((rules axioms implication).inference.obj Q).hom =
      ((printedH axioms implication).obj Q).hom := by
  apply coprod.hom_ext
  · change coprod.inl ≫ coprod.desc
        ((rules axioms implication).nullaryRule Q ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 0)
        (Sigma.ι ((rules axioms implication).ruleObject Q) 2) ≫
          Sigma.desc ((rules axioms implication).ruleConclusion Q) =
      coprod.inl ≫ coprod.desc axioms (mpConclusion implication Q)
    rw [coprod.inl_desc_assoc,coprod.inl_desc,Category.assoc,Sigma.ι_comp_desc]
    change (rules axioms implication).nullaryRule Q ≫
      (pullback.fst ((rules axioms implication).premises 0) (finitePowerMap Q.hom 0) ≫ axioms) = axioms
    erw [← Category.assoc,RulePresentation.nullaryRule_fst,Category.id_comp]
  · change coprod.inr ≫ coprod.desc
        ((rules axioms implication).nullaryRule Q ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 0)
        (Sigma.ι ((rules axioms implication).ruleObject Q) 2) ≫
          Sigma.desc ((rules axioms implication).ruleConclusion Q) =
      coprod.inr ≫ coprod.desc axioms (mpConclusion implication Q)
    rw [coprod.inr_desc_assoc,coprod.inr_desc,Sigma.ι_comp_desc]
    rfl

def fromPrinted (Q : Over S) :
    (printedH axioms implication).obj Q ⟶ (rules axioms implication).inference.obj Q :=
  Over.homMk (fromPrintedLeft axioms implication Q) (fromPrintedLeft_conclusion axioms implication Q)

def inputIso (Q : Over S) : (rules axioms implication).inference.obj Q ≅
    (printedH axioms implication).obj Q where
  hom := toPrinted axioms implication Q
  inv := fromPrinted axioms implication Q
  hom_inv_id := by
    apply Over.OverMorphism.ext
    change toPrintedLeft axioms implication Q ≫ fromPrintedLeft axioms implication Q = 𝟙 _
    apply Sigma.hom_ext
    intro i
    fin_cases i
    · erw [← Category.assoc,toPrintedLeft_ι_zero]
      erw [Category.assoc,fromPrintedLeft,coprod.inl_desc]
      change (nullaryInputIso axioms implication Q).hom ≫
          (nullaryInputIso axioms implication Q).inv ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 0 =
        Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫ 𝟙 _
      rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]
    · exact (unaryInputInitial axioms implication Q).hom_ext _ _
    · erw [← Category.assoc,toPrintedLeft_ι_two]
      erw [fromPrintedLeft,coprod.inr_desc,Category.comp_id]
      rfl
  inv_hom_id := by
    apply Over.OverMorphism.ext
    change fromPrintedLeft axioms implication Q ≫ toPrintedLeft axioms implication Q = 𝟙 _
    apply coprod.hom_ext
    · erw [fromPrintedLeft,coprod.inl_desc_assoc,Category.assoc,toPrintedLeft_ι_zero]
      erw [← Category.assoc,RulePresentation.nullaryRule_fst,Category.id_comp,Category.comp_id]
      rfl
    · erw [fromPrintedLeft,coprod.inr_desc_assoc,toPrintedLeft_ι_two,Category.comp_id]
      rfl

def inferenceIso : (rules axioms implication).inference ≅ printedH axioms implication :=
  NatIso.ofComponents (inputIso axioms implication) (by
    intro Q Q' h
    apply Over.OverMorphism.ext
    change Limits.Sigma.map ((rules axioms implication).ruleMap h) ≫
        toPrintedLeft axioms implication Q' =
      toPrintedLeft axioms implication Q ≫ coprod.map (𝟙 Ax) (mpMap implication h)
    apply Sigma.hom_ext
    intro i
    fin_cases i
    · erw [Sigma.ι_map_assoc,toPrintedLeft_ι_zero,toPrintedLeft_ι_zero_assoc,
        coprod.inl_map,Category.id_comp,RulePresentation.ruleMap_fst_assoc]
      rfl
    · exact (unaryInputInitial axioms implication Q).hom_ext _ _
    · erw [Sigma.ι_map_assoc,toPrintedLeft_ι_two,toPrintedLeft_ι_two_assoc,coprod.inr_map]
      rfl)

/-- The nullary comparison is the literal label projection, in both
directions; it neither inserts a premise nor selects a proof. -/
theorem nullaryInputIso_hom (Q : Over S) :
    (nullaryInputIso axioms implication Q).hom =
      pullback.fst ((rules axioms implication).premises 0) (finitePowerMap Q.hom 0) := rfl

theorem nullaryInputIso_inv (Q : Over S) :
    (nullaryInputIso axioms implication Q).inv = (rules axioms implication).nullaryRule Q := rfl

/-- The binary comparison keeps the same pullback: the two children have
their individual conclusions, matched to α and α implies β. -/
def binaryInputIso (Q : Over S) :
    (rules axioms implication).ruleObject Q 2 ≅ mpObject implication Q := Iso.refl _

@[simp,reassoc] theorem binaryInputIso_label (Q : Over S) :
    (binaryInputIso axioms implication Q).hom ≫
      pullback.fst (premise implication) (prod.map Q.hom Q.hom) =
      pullback.fst ((rules axioms implication).premises 2) (finitePowerMap Q.hom 2) := by
  simp only [binaryInputIso,Iso.refl_hom,Category.id_comp,rules_premises_two,finitePowerMap]

@[simp,reassoc] theorem binaryInputIso_children (Q : Over S) :
    (binaryInputIso axioms implication Q).hom ≫
      pullback.snd (premise implication) (prod.map Q.hom Q.hom) =
      pullback.snd ((rules axioms implication).premises 2) (finitePowerMap Q.hom 2) := by
  simp only [binaryInputIso,Iso.refl_hom,Category.id_comp,rules_premises_two,finitePowerMap]

@[simp,reassoc] theorem inputIso_nullary (Q : Over S) :
    (rules axioms implication).nullaryRule Q ≫
      Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫
        (inputIso axioms implication Q).hom.left = coprod.inl := by
  change (rules axioms implication).nullaryRule Q ≫
    Sigma.ι ((rules axioms implication).ruleObject Q) 0 ≫ toPrintedLeft axioms implication Q = coprod.inl
  rw [toPrintedLeft_ι_zero]
  erw [← Category.assoc,RulePresentation.nullaryRule_fst,Category.id_comp]

@[simp,reassoc] theorem inputIso_binary (Q : Over S) :
    Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫
      (inputIso axioms implication Q).hom.left =
        (binaryInputIso axioms implication Q).hom ≫ coprod.inr := by
  change Sigma.ι ((rules axioms implication).ruleObject Q) 2 ≫ toPrintedLeft axioms implication Q =
    (𝟙 _) ≫ coprod.inr
  rw [toPrintedLeft_ι_two]
  exact (Category.id_comp _).symm

@[simp,reassoc] theorem inputIso_inv_nullary (Q : Over S) :
    coprod.inl ≫ (inputIso axioms implication Q).inv.left =
      (rules axioms implication).nullaryRule Q ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 0 := by
  change coprod.inl ≫ fromPrintedLeft axioms implication Q = _
  exact coprod.inl_desc _ _

@[simp,reassoc] theorem inputIso_inv_binary (Q : Over S) :
    coprod.inr ≫ (inputIso axioms implication Q).inv.left =
      (binaryInputIso axioms implication Q).inv ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 2 := by
  change coprod.inr ≫ fromPrintedLeft axioms implication Q =
    (𝟙 _) ≫ Sigma.ι ((rules axioms implication).ruleObject Q) 2
  rw [fromPrintedLeft,coprod.inr_desc]
  exact (Category.id_comp _).symm

theorem inputIso_conclusion (Q : Over S) :
    (inputIso axioms implication Q).hom.left ≫
      coprod.desc axioms (pullback.fst (premise implication) (prod.map Q.hom Q.hom) ≫ prod.snd) =
      Sigma.desc ((rules axioms implication).ruleConclusion Q) :=
  Over.w (inputIso axioms implication Q).hom

theorem inputIso_inverse_conclusion (Q : Over S) :
    (inputIso axioms implication Q).inv.left ≫
      Sigma.desc ((rules axioms implication).ruleConclusion Q) =
      coprod.desc axioms (pullback.fst (premise implication) (prod.map Q.hom Q.hom) ≫ prod.snd) :=
  Over.w (inputIso axioms implication Q).inv
end CategoricalEssentialIncompleteness.V46.ForkInference
