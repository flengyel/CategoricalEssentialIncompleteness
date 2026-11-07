/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticNullaryRules
import CategoricalEssentialIncompleteness.V46NumericalRuleRelabel
import CategoricalEssentialIncompleteness.V46NumericalRuleRebaseWords

/-! # Actual arithmetic rule-label and finite-proof relabellings -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleComparison
open Coordinates NamedArithmeticSignature

/-- Formula conclusions are changed by the proved formula word chart;
all source inference labels and ordered child slots remain unchanged. -/
abbrev sourceRules (Γ : Carrier) := NumericalRuleRebase.rules (Rules.rules Γ) formulaIso
/-- The target labels are the actual PA rule-instance objects under
arithmetic interpretation, with its ordered finite-power comparison. -/
abbrev targetRules (Γ : Carrier) := NumericalDerivationInterpretation.interpretedRules (Rules.originalRules Γ)

/-- These are the actual computable rho_n, including all seven logical
schemes and the unchanged Gamma axiom branch at n=0. -/
def labelIso (Γ : Carrier) : ∀ i : Fin 3, (sourceRules Γ).instances i ≅ (targetRules Γ).instances i :=
  Fin.cases (NullaryRules.rho0 Γ) (Fin.cases (Rules.rho1 Γ)
    (Fin.cases (Rules.rho2 Γ) (fun i => Fin.elim0 i)))

/-- Labels are decoded at their actual tuple dimensions. In particular,
the zero-dimensional code image is not replaced by all natural numbers. -/
def labelForward (Γ : Carrier) (i : Fin 3) : ℕ → Part ℕ :=
  (labelIso Γ i).hom.restrictedProgram

def labelBackward (Γ : Carrier) (i : Fin 3) : ℕ → Part ℕ :=
  (labelIso Γ i).inv.restrictedProgram

theorem labelForward_partrec (Γ : Carrier) (i : Fin 3) : Partrec (labelForward Γ i) :=
  (labelIso Γ i).hom.restrictedProgram_partrec

theorem labelBackward_partrec (Γ : Carrier) (i : Fin 3) : Partrec (labelBackward Γ i) :=
  (labelIso Γ i).inv.restrictedProgram_partrec

theorem labelForward_graph (Γ : Carrier) (i : Fin 3) (n k : ℕ) :
    k ∈ labelForward Γ i n ↔ ∃ x : NumericalTuples.Point ((sourceRules Γ).instances i),
      NumericalTuples.code ((sourceRules Γ).instances i).dimension x.val = n ∧
        NumericalTuples.code ((targetRules Γ).instances i).dimension
          ((labelIso Γ i).hom.toFun x).val = k :=
  (labelIso Γ i).hom.restrictedProgram_graph n k

theorem labelBackward_graph (Γ : Carrier) (i : Fin 3) (n k : ℕ) :
    k ∈ labelBackward Γ i n ↔ ∃ x : NumericalTuples.Point ((targetRules Γ).instances i),
      NumericalTuples.code ((targetRules Γ).instances i).dimension x.val = n ∧
        NumericalTuples.code ((sourceRules Γ).instances i).dimension
          ((labelIso Γ i).inv.toFun x).val = k :=
  (labelIso Γ i).inv.restrictedProgram_graph n k

private theorem restricted_inverse {C D : NumericalTuples.Object} (e : C ≅ D)
    (x : NumericalTuples.Point C) :
    (e.hom.restrictedProgram (NumericalTuples.code C.dimension x.val)).bind e.inv.restrictedProgram =
      Part.some (NumericalTuples.code C.dimension x.val) := by
  rw [e.hom.restrictedProgram_apply,Part.bind_some,e.inv.restrictedProgram_apply]
  have hx : e.inv.toFun (e.hom.toFun x) = x :=
    (NumericalTuples.composition_apply e.hom e.inv x).symm.trans
      ((congrArg (fun f => f.toFun x) e.hom_inv_id).trans (NumericalTuples.identity_apply C x))
  exact congrArg (fun y : NumericalTuples.Point C => Part.some (NumericalTuples.code C.dimension y.val)) hx

/-- At a valid label both program composites recover its original
code. Their source dimensions are retained, including dimension zero. -/
abbrev labelForward_backward (Γ : Carrier) (i : Fin 3) := restricted_inverse (labelIso Γ i)
abbrev labelBackward_forward (Γ : Carrier) (i : Fin 3) := restricted_inverse (labelIso Γ i).symm

def forward (Γ : Carrier) : RulePresentation.Hom (sourceRules Γ) (targetRules Γ) where
  map i := (labelIso Γ i).hom
  premises i := by
    fin_cases i
    · exact NullaryRules.rho0_rule_premises Γ
    · exact Rules.rho1_rule_premises Γ
    · exact Rules.rho2_rule_premises Γ
  conclusion i := by
    fin_cases i
    · exact NullaryRules.rho0_rule_conclusion Γ
    · exact Rules.rho1_rule_conclusion Γ
    · exact Rules.rho2_rule_conclusion Γ

/-- The inverse is an inference-signature morphism, not merely a
bijection between coefficient carriers. -/
def backward (Γ : Carrier) : RulePresentation.Hom (targetRules Γ) (sourceRules Γ) where
  map i := (labelIso Γ i).inv
  premises i := by
    have h := congrArg (fun k => (labelIso Γ i).inv ≫ k) ((forward Γ).premises i)
    simpa only [forward,← CategoryTheory.Category.assoc,Iso.inv_hom_id,CategoryTheory.Category.id_comp] using h.symm
  conclusion i := by
    have h := congrArg (fun k => (labelIso Γ i).inv ≫ k) ((forward Γ).conclusion i)
    simpa only [forward,← CategoryTheory.Category.assoc,Iso.inv_hom_id,CategoryTheory.Category.id_comp] using h.symm

theorem forward_backward (Γ : Carrier) (i : Fin 3) :
    (forward Γ).map i ≫ (backward Γ).map i = 𝟙 _ := (labelIso Γ i).hom_inv_id

theorem backward_forward (Γ : Carrier) (i : Fin 3) :
    (backward Γ).map i ≫ (forward Γ).map i = 𝟙 _ := (labelIso Γ i).inv_hom_id

/-- Inverse constructor-preserving folds give the actual finite-proof
relabelings; their programs are total on their respective proof carriers. -/
def proofIso (Γ : Carrier) : NumericalDerivation.codeObject (Rules.rules Γ) ≅
    NumericalDerivation.codeObject (targetRules Γ) :=
  NumericalRuleRebase.codeIso (Rules.rules Γ) formulaIso ≪≫
    NumericalRuleRelabel.codeIso (forward Γ) (backward Γ)
      (forward_backward Γ) (backward_forward Γ)

/-- The actual constructor comparisons are supplied by the constructed
base-change and inverse relabelling folds, including their original inputs. -/
abbrev rebase_constructor (Γ : Carrier) :=
  NumericalRuleRebase.constructor (Rules.rules Γ) formulaIso

abbrev relabel_constructor (Γ : Carrier) :=
  NumericalRuleRelabel.constructor (forward Γ) (backward Γ)
    (forward_backward Γ) (backward_forward Γ)

abbrev inverse_relabel_constructor (Γ : Carrier) :=
  NumericalRuleRelabel.inverse_constructor (forward Γ) (backward Γ)
    (forward_backward Γ) (backward_forward Γ)

abbrev relabel_branch_constructor (Γ : Carrier) :=
  NumericalRuleRelabel.branch_constructor (forward Γ) (backward Γ)
    (forward_backward Γ) (backward_forward Γ)

abbrev rebase_word_coded (Γ : Carrier) := NumericalRuleRebase.code_word_coded (Rules.rules Γ) formulaIso

/-- The composed input map changes precisely the actual rule label and
each ordered child by the corresponding proof comparison. -/
def inputComparison (Γ : Carrier) (i : Fin 3) :
    (Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a i ⟶
      (targetRules Γ).ruleObject (NumericalDerivation.codeAlgebra (targetRules Γ)).a i :=
  NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
    NumericalRuleRelabel.inputRelabel (forward Γ) (backward Γ)
      (forward_backward Γ) (backward_forward Γ) i

@[reassoc] theorem input_label (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (labelIso Γ i).hom := by
  change (NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
    NumericalRuleRelabel.inputRelabel (forward Γ) (backward Γ)
      (forward_backward Γ) (backward_forward Γ) i) ≫ pullback.fst _ _ = _
  rw [CategoryTheory.Category.assoc,NumericalRuleRelabel.input_label,← CategoryTheory.Category.assoc,
    NumericalRuleRebase.input_label]
  rfl

@[reassoc] theorem input_children (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (proofIso Γ).hom i.val := by
  change (NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
    NumericalRuleRelabel.inputRelabel (forward Γ) (backward Γ)
      (forward_backward Γ) (backward_forward Γ) i) ≫ pullback.snd _ _ = _
  rw [CategoryTheory.Category.assoc,NumericalRuleRelabel.input_children,← CategoryTheory.Category.assoc,
    NumericalRuleRebase.input_children,CategoryTheory.Category.assoc]
  simp only [proofIso,Iso.trans_hom,finitePowerMap_comp]

private theorem rebase_branch {F G : NumericalTuples.Object} {N : ℕ}
    (R : RulePresentation F N) (e : F ≅ G) (i : Fin (N+1)) :
    NumericalRuleRebase.inputRebase R e i ≫
        Sigma.ι ((NumericalRuleRebase.rules R e).ruleObject
          (NumericalDerivation.codeAlgebra (NumericalRuleRebase.rules R e)).a) i ≫
        (NumericalDerivation.codeAlgebra (NumericalRuleRebase.rules R e)).str.left =
      Sigma.ι (R.ruleObject (NumericalDerivation.codeAlgebra R).a) i ≫
        (NumericalDerivation.codeAlgebra R).str.left ≫ (NumericalRuleRebase.codeIso R e).hom := by
  have h := congrArg Over.Hom.left (NumericalRuleRebase.constructor R e)
  change (NumericalDerivation.codeAlgebra R).str.left ≫ (NumericalRuleRebase.codeIso R e).hom =
    (Limits.Sigma.mapIso (NumericalRuleRebase.inputIso R e (NumericalDerivation.codeAlgebra R).a)).hom ≫
      Limits.Sigma.map ((NumericalRuleRebase.rules R e).ruleMap (NumericalRuleRebase.overIso R e).hom) ≫
      (NumericalDerivation.codeAlgebra (NumericalRuleRebase.rules R e)).str.left at h
  have hi := congrArg (fun f => Sigma.ι (R.ruleObject (NumericalDerivation.codeAlgebra R).a) i ≫ f) h
  simpa only [NumericalRuleRebase.inputRebase,CategoryTheory.Category.assoc,
    Sigma.ι_mapIso_hom_assoc,Sigma.ι_map_assoc] using hi.symm

/-- The actual composite map obeys the node-label recursion: the input
map carries rho on the label and this same map on every ordered child. -/
theorem branch_constructor (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ Sigma.ι ((targetRules Γ).ruleObject
        (NumericalDerivation.codeAlgebra (targetRules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (targetRules Γ)).str.left =
      Sigma.ι ((Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (Rules.rules Γ)).str.left ≫ (proofIso Γ).hom := by
  calc
    _ = NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
        (NumericalRuleRelabel.inputRelabel (forward Γ) (backward Γ)
          (forward_backward Γ) (backward_forward Γ) i ≫
        Sigma.ι ((targetRules Γ).ruleObject (NumericalDerivation.codeAlgebra (targetRules Γ)).a) i ≫
          (NumericalDerivation.codeAlgebra (targetRules Γ)).str.left) := by
      simp only [inputComparison,CategoryTheory.Category.assoc]
    _ = NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
        (Sigma.ι ((sourceRules Γ).ruleObject (NumericalDerivation.codeAlgebra (sourceRules Γ)).a) i ≫
          (NumericalDerivation.codeAlgebra (sourceRules Γ)).str.left ≫
          (NumericalRuleRelabel.codeIso (forward Γ) (backward Γ)
            (forward_backward Γ) (backward_forward Γ)).hom) :=
      congrArg (fun f => NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫ f)
        (NumericalRuleRelabel.branch_constructor (forward Γ) (backward Γ)
          (forward_backward Γ) (backward_forward Γ) i)
    _ = (NumericalRuleRebase.inputRebase (Rules.rules Γ) formulaIso i ≫
        Sigma.ι ((sourceRules Γ).ruleObject (NumericalDerivation.codeAlgebra (sourceRules Γ)).a) i ≫
          (NumericalDerivation.codeAlgebra (sourceRules Γ)).str.left) ≫
        (NumericalRuleRelabel.codeIso (forward Γ) (backward Γ)
          (forward_backward Γ) (backward_forward Γ)).hom := by simp only [CategoryTheory.Category.assoc]
    _ = (Sigma.ι ((Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (Rules.rules Γ)).str.left ≫
          (NumericalRuleRebase.codeIso (Rules.rules Γ) formulaIso).hom) ≫
        (NumericalRuleRelabel.codeIso (forward Γ) (backward Γ)
          (forward_backward Γ) (backward_forward Γ)).hom :=
      congrArg (fun f => f ≫ (NumericalRuleRelabel.codeIso (forward Γ) (backward Γ)
        (forward_backward Γ) (backward_forward Γ)).hom) (rebase_branch (Rules.rules Γ) formulaIso i)
    _ = _ := by simp only [proofIso,Iso.trans_hom,CategoryTheory.Category.assoc]

@[reassoc] theorem proof_conclusion (Γ : Carrier) :
    (proofIso Γ).hom ≫ NumericalDerivation.codeConclusion (targetRules Γ) =
      NumericalDerivation.codeConclusion (Rules.rules Γ) ≫ formulaIso.hom := by
  simp only [proofIso,Iso.trans_hom,CategoryTheory.Category.assoc,NumericalRuleRelabel.conclusion,
    NumericalRuleRebase.conclusion]

@[reassoc] theorem inverse_proof_conclusion (Γ : Carrier) :
    (proofIso Γ).inv ≫ NumericalDerivation.codeConclusion (Rules.rules Γ) ≫ formulaIso.hom =
      NumericalDerivation.codeConclusion (targetRules Γ) := by
  have h := congrArg (fun k => (proofIso Γ).inv ≫ k) (proof_conclusion Γ)
  simpa only [← CategoryTheory.Category.assoc,Iso.inv_hom_id,CategoryTheory.Category.id_comp] using h.symm

private def inverseInputMap {F G L L' X Y : NumericalTuples.Object} (n : ℕ)
    (e : F ≅ G) (rho : L ≅ L') (gamma : X ≅ Y)
    (p : L ⟶ finitePower F n) (q : X ⟶ F)
    (p' : L' ⟶ finitePower G n) (q' : Y ⟶ G)
    (hrho : rho.inv ≫ p ≫ finitePowerMap e.hom n = p')
    (hgamma : gamma.inv ≫ q ≫ e.hom = q') :
    pullback p' (finitePowerMap q' n) ⟶ pullback p (finitePowerMap q n) :=
  pullback.lift (pullback.fst _ _ ≫ rho.inv)
    (pullback.snd _ _ ≫ finitePowerMap gamma.inv n) (by
      apply (cancel_mono (NumericalRuleRebase.powerIso e n).hom).mp
      change ((pullback.fst _ _ ≫ rho.inv) ≫ p) ≫ finitePowerMap e.hom n =
        ((pullback.snd _ _ ≫ finitePowerMap gamma.inv n) ≫ finitePowerMap q n) ≫
          finitePowerMap e.hom n
      have hg : finitePowerMap gamma.inv n ≫ finitePowerMap q n ≫ finitePowerMap e.hom n =
          finitePowerMap q' n := by
        simpa only [finitePowerMap_comp] using congrArg (fun f => finitePowerMap f n) hgamma
      calc
        _ = pullback.fst p' (finitePowerMap q' n) ≫ (rho.inv ≫ p ≫ finitePowerMap e.hom n) := by
          simp only [CategoryTheory.Category.assoc]
        _ = pullback.fst p' (finitePowerMap q' n) ≫ p' :=
          congrArg (fun f => pullback.fst p' (finitePowerMap q' n) ≫ f) hrho
        _ = pullback.snd p' (finitePowerMap q' n) ≫ finitePowerMap q' n := pullback.condition
        _ = pullback.snd p' (finitePowerMap q' n) ≫
            (finitePowerMap gamma.inv n ≫ finitePowerMap q n ≫ finitePowerMap e.hom n) :=
          congrArg (fun f => pullback.snd p' (finitePowerMap q' n) ≫ f) hg.symm
        _ = _ := by simp only [CategoryTheory.Category.assoc])

/-- The inverse input map uses rho inverse on its label and the SAME
inverse proof map on each child; matching follows from the proved squares. -/
def inputComparisonInverse (Γ : Carrier) (i : Fin 3) :
    (targetRules Γ).ruleObject (NumericalDerivation.codeAlgebra (targetRules Γ)).a i ⟶
      (Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a i :=
  inverseInputMap i.val formulaIso (labelIso Γ i) (proofIso Γ)
    ((Rules.rules Γ).premises i) (NumericalDerivation.codeConclusion (Rules.rules Γ))
    ((targetRules Γ).premises i) (NumericalDerivation.codeConclusion (targetRules Γ))
    (by simpa only [sourceRules,NumericalRuleRebase.rules,backward,CategoryTheory.Category.assoc]
      using (backward Γ).premises i)
    (inverse_proof_conclusion Γ)

@[reassoc] theorem inverse_input_label (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (labelIso Γ i).inv := by
  change inputComparisonInverse Γ i ≫
      pullback.fst ((Rules.rules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (Rules.rules Γ)) i.val) =
    pullback.fst ((targetRules Γ).premises i)
      (finitePowerMap (NumericalDerivation.codeConclusion (targetRules Γ)) i.val) ≫ (labelIso Γ i).inv
  simp only [inputComparisonInverse,inverseInputMap,pullback.lift_fst]

@[reassoc] theorem inverse_input_children (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (proofIso Γ).inv i.val := by
  change inputComparisonInverse Γ i ≫
      pullback.snd ((Rules.rules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (Rules.rules Γ)) i.val) =
    pullback.snd ((targetRules Γ).premises i)
      (finitePowerMap (NumericalDerivation.codeConclusion (targetRules Γ)) i.val) ≫
        finitePowerMap (proofIso Γ).inv i.val
  simp only [inputComparisonInverse,inverseInputMap,pullback.lift_snd]

@[reassoc] theorem input_forward_inverse (Γ : Carrier) (i : Fin 3) :
    inputComparison Γ i ≫ inputComparisonInverse Γ i = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [CategoryTheory.Category.assoc,inverse_input_label,input_label_assoc,
      CategoryTheory.Category.id_comp]
    rw [(labelIso Γ i).hom_inv_id,CategoryTheory.Category.comp_id]
  · simp only [CategoryTheory.Category.assoc,inverse_input_children,input_children_assoc,
      CategoryTheory.Category.id_comp]
    change pullback.snd ((Rules.rules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (Rules.rules Γ)) i.val) ≫
      (finitePowerMap (proofIso Γ).hom i.val ≫ finitePowerMap (proofIso Γ).inv i.val) = _
    exact (congrArg (fun f => pullback.snd ((Rules.rules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (Rules.rules Γ)) i.val) ≫ f)
      (NumericalRuleRebase.powerIso (proofIso Γ) i.val).hom_inv_id).trans
        (CategoryTheory.Category.comp_id _)

@[reassoc] theorem input_inverse_forward (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫ inputComparison Γ i = 𝟙 _ := by
  apply pullback.hom_ext
  · simp only [CategoryTheory.Category.assoc,input_label,inverse_input_label_assoc,
      CategoryTheory.Category.id_comp]
    rw [(labelIso Γ i).inv_hom_id,CategoryTheory.Category.comp_id]
  · simp only [CategoryTheory.Category.assoc,input_children,inverse_input_children_assoc,
      CategoryTheory.Category.id_comp]
    change pullback.snd ((targetRules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (targetRules Γ)) i.val) ≫
      (finitePowerMap (proofIso Γ).inv i.val ≫ finitePowerMap (proofIso Γ).hom i.val) = _
    exact (congrArg (fun f => pullback.snd ((targetRules Γ).premises i)
        (finitePowerMap (NumericalDerivation.codeConclusion (targetRules Γ)) i.val) ≫ f)
      (NumericalRuleRebase.powerIso (proofIso Γ) i.val).inv_hom_id).trans
        (CategoryTheory.Category.comp_id _)

/-- The inverse tree map obeys the inverse node-label recursion, on
exactly the valid target inputs with their prescribed premise conclusions. -/
theorem inverse_branch_constructor (Γ : Carrier) (i : Fin 3) :
    inputComparisonInverse Γ i ≫
        Sigma.ι ((Rules.rules Γ).ruleObject (NumericalDerivation.codeAlgebra (Rules.rules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (Rules.rules Γ)).str.left =
      Sigma.ι ((targetRules Γ).ruleObject (NumericalDerivation.codeAlgebra (targetRules Γ)).a) i ≫
        (NumericalDerivation.codeAlgebra (targetRules Γ)).str.left ≫ (proofIso Γ).inv := by
  have h := congrArg (fun f => inputComparisonInverse Γ i ≫ f ≫ (proofIso Γ).inv)
    (branch_constructor Γ i)
  simpa only [CategoryTheory.Category.assoc,input_inverse_forward_assoc,
    Iso.hom_inv_id,CategoryTheory.Category.comp_id] using h.symm

theorem forward_program (Γ : Carrier) :
    ∃ p : NumericalTuples.Tuple (NumericalDerivation.codeObject (Rules.rules Γ)).dimension →
        Part (NumericalTuples.Tuple (NumericalDerivation.codeObject (targetRules Γ)).dimension),
      Partrec p ∧ ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject (Rules.rules Γ)),
        p x.val = Part.some ((proofIso Γ).hom.toFun x).val := (proofIso Γ).hom.represented

theorem backward_program (Γ : Carrier) :
    ∃ p : NumericalTuples.Tuple (NumericalDerivation.codeObject (targetRules Γ)).dimension →
        Part (NumericalTuples.Tuple (NumericalDerivation.codeObject (Rules.rules Γ)).dimension),
      Partrec p ∧ ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject (targetRules Γ)),
        p x.val = Part.some ((proofIso Γ).inv.toFun x).val := (proofIso Γ).inv.represented

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.RuleComparison
