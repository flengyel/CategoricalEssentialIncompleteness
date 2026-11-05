/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46DerivationStandardInductionInputs

/-! # The original typed rule constructors and their tree-word charts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
open SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F₀ : PredicateCategory T} {bound : ℕ}
  (R : RulePresentation F₀ bound)

/-- The coefficient equality changes only the chosen object spelling
of the original rule instance, with its actual inverse transport. -/
def coefficientInput (X : PredicateCategory T) (i : Fin (bound + 1)) :
    R.instances i ⨯ finitePower X i.val ⟶
      PolynomialComparison.coefficients (D := PredicateCategory T) R i.val ⨯ finitePower X i.val :=
  prod.map (eqToHom (PolynomialComparison.coefficients_fin R i).symm) (𝟙 _)

theorem coefficientInput_injection (X : PredicateCategory T) (i : Fin (bound + 1)) :
    coefficientInput T R X i ≫
      PolynomialComparison.injection (PolynomialComparison.coefficients (D := PredicateCategory T) R) X bound i ≫
      (PolynomialComparison.comparison R).hom.app X =
      Sigma.ι (fun j : Fin (bound + 1) => R.instances j ⨯ finitePower X j.val) i := by
  rw [PolynomialComparison.injection_comparison]
  unfold coefficientInput
  rw [← Category.assoc, prod.map_map]
  simp

/-- Each typed constructor first forgets its matching witnesses, retaining
its own rule label and the same ordered child tuple. -/
theorem typed_constructor_tree (i : Fin (bound + 1)) :
    derivationConstructor T R i ≫ treeInclusion T R =
      CheckedRoot.matchingMap R (derivationAlgebra T R).a i ≫
        prod.map (𝟙 (R.instances i)) (finitePowerMap (treeInclusion T R) i.val) ≫
        Sigma.ι (fun j : Fin (bound + 1) =>
          R.instances j ⨯ finitePower (ordinaryTree T R).a j.val) i ≫ (ordinaryTree T R).str := by
  have he := congrArg (fun k => Sigma.ι (R.ruleObject (derivationAlgebra T R).a) i ≫ k)
    (derivationConstructor_tree T R)
  simpa only [derivationConstructor, InputGeometry.forget, PolynomialComparison.ordinary,
    Category.assoc, Sigma.ι_comp_desc_assoc, Sigma.ι_map_assoc] using he

def ruleChildren (i : Fin (bound + 1)) :
    R.ruleObject (derivationAlgebra T R).a i ⟶ finitePower (derivationAlgebra T R).a.left i.val :=
  pullback.snd (R.premises i) (finitePowerMap (derivationAlgebra T R).a.hom i.val)

def typedChild (i : Fin (bound + 1)) (k : Fin i.val) :
    R.ruleObject (derivationAlgebra T R).a i ⟶ (derivationAlgebra T R).a.left :=
  ruleChildren T R i ≫ finiteChild T (derivationAlgebra T R).a.left i.val k

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- The successful validator carrier contains the original tree number;
its inclusion into the ordinary tree object keeps that number literally. -/
theorem treeInclusion_value (d : Obj T M (derivationAlgebra T R).a.left) :
    ((F T M).map (treeInclusion T R) d).val = d.val := by
  let v := (validatorFold T R).f
  let out := (F T M).map (treeInclusion T R) d
  have hg := (PredicateInterpretation.map_class_eq_iff T M (SuccessCarrier.inclusion v) d out).mp rfl
  exact ((SuccessCarrier.inclusionGraph_eval v M d.val out.val).mp hg).2.symm

variable [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Each original child of a typed inference node has smaller literal
node count than the parent. Its premise conclusion remains its own
prescribed component of R.premises, rather than the parent conclusion. -/
theorem typed_children_smaller (i : Fin (bound + 1))
    (r : Obj T M (R.ruleObject (derivationAlgebra T R).a i)) (k : Fin i.val) :
    len ((F T M).map (typedChild T R i k) r).val <
      len ((F T M).map (derivationConstructor T R i) r).val := by
  let Q : Over F₀ := (derivationAlgebra T R).a
  let X : PredicateCategory T := (ordinaryTree T R).a
  let labels : ℕ → PredicateCategory T := PolynomialComparison.coefficients (D := PredicateCategory T) R
  let j : Q.left ⟶ X := treeInclusion T R
  let p : Obj T M (R.instances i ⨯ finitePower Q.left i.val) :=
    (F T M).map (CheckedRoot.matchingMap R Q i) r
  let p' : Obj T M (R.instances i ⨯ finitePower X i.val) :=
    (F T M).map (prod.map (𝟙 (R.instances i)) (finitePowerMap j i.val)) p
  let pc : Obj T M (labels i.val ⨯ finitePower X i.val) :=
    (F T M).map (coefficientInput T R X i) p'
  let w : Obj T M ((PolynomialComparison.ordinary (D := PredicateCategory T) R).obj X) :=
    (F T M).map (Sigma.ι (fun h : Fin (bound + 1) => R.instances h ⨯ finitePower X h.val) i) p'
  let parent := (F T M).map (derivationConstructor T R i) r
  have htree : (F T M).map j parent = (F T M).map (ordinaryTree T R).str w := by
    have he := congrArg (fun f => (F T M).map f r) (typed_constructor_tree T R i)
    simp only [Functor.map_comp_apply] at he
    dsimp only [p,p',w,parent,j,Q,X]
    exact he
  have hparent : parent.val = ((F T M).map (ordinaryTree T R).str w).val :=
    (treeInclusion_value T R M parent).symm.trans (congrArg Subtype.val htree)
  obtain ⟨u,source,hsource,himage,hword,hsize⟩ := ordinary_input_chart T M R w
  let z₀ := (F T M).map (projectedInput T labels bound) source
  have hz₀ := projectedInput_chart T labels bound M u source hsource
  have hc₁ : (F T M).map ((PolynomialComparison.comparison R).hom.app X) z₀ = w := by
    unfold ordinaryInput at himage
    rw [Functor.map_comp_apply] at himage
    exact himage
  have hc₂ : (F T M).map ((PolynomialComparison.comparison R).hom.app X)
      ((F T M).map (PolynomialComparison.injection labels X bound i) pc) = w := by
    have he := congrArg (fun f => (F T M).map f p') (coefficientInput_injection T R X i)
    simp only [Functor.map_comp_apply] at he
    exact he
  have hp : z₀ = (F T M).map (PolynomialComparison.injection labels X bound i) pc :=
    (((F T M).mapIso ((PolynomialComparison.comparison R).app X)).toEquiv.injective
      (hc₁.trans hc₂.symm))
  let childPower := (F T M).map (prod.snd : labels i.val ⨯ finitePower X i.val ⟶ _) pc
  let literalPower := (F T M).map (PolynomialComparison.powerIso X i.val).hom childPower
  obtain ⟨tuple,htuple⟩ := baseRepresentation_cover T M X (⊤_ (PredicateCategory T))
    (SyntaxPolynomial.power .term i.val) literalPower
  let label := (F T M).map (prod.fst : labels i.val ⨯ finitePower X i.val ⟶ _) pc
  let input := ruleTag M bound i (Arithmetic.pair label.val tuple)
  have hinput : (baseRepresentation T X (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.constructors labels bound)).val.Evalb ![input,z₀.val] := by
    have he := injection_representation T M labels X bound i pc tuple htuple
    have hv := congrArg Subtype.val hp
    rw [hv]
    exact he
  have hu : u = input := baseRepresentation_code_unique T M X (⊤_ (PredicateCategory T))
    (SyntaxPolynomial.constructors labels bound) u input z₀.val hz₀ hinput
  have hsinput : Coding.ChildSize (SyntaxPolynomial.constructors labels bound)
      (len ((F T M).map (ordinaryTree T R).str w).val) input := by
    rw [← hu]
    exact hsize
  have htupleSize := ruleTag_childSize T M labels bound i
    (len ((F T M).map (ordinaryTree T R).str w).val) label.val tuple hsinput
  have hsmall := power_children_smaller T M X (⊤_ (PredicateCategory T)) i.val
    (len ((F T M).map (ordinaryTree T R).str w).val) tuple literalPower htuple htupleSize k
  have hchildren : childPower = (F T M).map (finitePowerMap j i.val)
      ((F T M).map (ruleChildren T R i) r) := by
    calc
      _ = (F T M).map (prod.snd : R.instances i ⨯ finitePower X i.val ⟶ _) p' := by
        change (F T M).map prod.snd
          ((F T M).map (prod.map (eqToHom (PolynomialComparison.coefficients_fin R i).symm)
            (𝟙 (finitePower X i.val))) p') = _
        rw [ConcreteNamedComparison.model_map_snd, (F T M).map_id]
        rfl
      _ = (F T M).map (finitePowerMap j i.val) ((F T M).map prod.snd p) :=
        ConcreteNamedComparison.model_map_snd T M (𝟙 (R.instances i)) (finitePowerMap j i.val) p
      _ = _ := by
        congr 1
        change (F T M).map prod.snd ((F T M).map (CheckedRoot.matchingMap R Q i) r) = _
        rw [← Functor.map_comp_apply]
        have he : CheckedRoot.matchingMap R Q i ≫ prod.snd = ruleChildren T R i := by
          simp [CheckedRoot.matchingMap,ruleChildren,Q]
        rw [he]
  have hchild : (F T M).map j ((F T M).map (typedChild T R i k) r) =
      (F T M).map (powerProjection T X (⊤_ (PredicateCategory T)) i.val k) literalPower := by
    calc
      _ = (F T M).map (finiteChild T X i.val k)
          ((F T M).map (finitePowerMap j i.val) ((F T M).map (ruleChildren T R i) r)) := by
        have he := congrArg (fun f => (F T M).map f ((F T M).map (ruleChildren T R i) r))
          (finiteChild_natural T j i.val k)
        simpa only [Functor.map_comp_apply,typedChild] using he.symm
      _ = (F T M).map (finiteChild T X i.val k) childPower := by rw [hchildren]
      _ = _ := by rw [finiteChild,Functor.map_comp_apply]
  have hval : ((F T M).map (typedChild T R i k) r).val =
      ((F T M).map (powerProjection T X (⊤_ (PredicateCategory T)) i.val k) literalPower).val :=
    (treeInclusion_value T R M ((F T M).map (typedChild T R i k) r)).symm.trans
      (congrArg Subtype.val hchild)
  exact (congrArg len hval).trans_lt (hsmall.trans_eq (congrArg len hparent).symm)

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
