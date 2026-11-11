/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalRuleRelabel


/-! # Statement checks in `V46NumericalRuleRelabelChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
variable {F : NumericalTuples.Object} {N : ℕ} {R R' : RulePresentation F N}
variable (ι : RulePresentation.Hom R R') (κ : RulePresentation.Hom R' R)
  (hικ : ∀ i, ι.map i ≫ κ.map i = 𝟙 _) (hκι : ∀ i, κ.map i ≫ ι.map i = 𝟙 _)

example (Q : Over F) (i : Fin (N + 1)) :
    ι.mapRule Q i ≫ pullback.snd (R'.premises i) (finitePowerMap Q.hom i.val) =
      pullback.snd (R.premises i) (finitePowerMap Q.hom i.val) :=
  ι.mapRule_snd Q i

example : NumericalDerivation.codeObject R ≅ NumericalDerivation.codeObject R' :=
  NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

example : (NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom ≫
    NumericalDerivation.codeConclusion R' = NumericalDerivation.codeConclusion R :=
  NumericalRuleRelabel.conclusion (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

example : (NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).inv ≫
    NumericalDerivation.codeConclusion R = NumericalDerivation.codeConclusion R' :=
  NumericalRuleRelabel.inverse_conclusion (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

/-- A morphism in the algebra category carries the full constructor
commutation equation in its `h` field. Its underlying map is the actual iso. -/
example : ∃ f : NumericalDerivation.codeAlgebra R ⟶
      NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R) (R' := R') ι,
    f.f = (NumericalRuleRelabel.overIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom ∧
      ∀ g : NumericalDerivation.codeAlgebra R ⟶
          NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R) (R' := R') ι,
        g = f := by
  refine ⟨NumericalRuleRelabel.relabelFold (F := F) (N := N) (R := R) (R' := R') ι, ?_, ?_⟩
  · exact (NumericalRuleRelabel.relabel_is_fold (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).symm
  · intro g
    exact (NumericalDerivation.codeInitial R).hom_ext _ _

example : ∃ f : NumericalDerivation.codeAlgebra R' ⟶
      NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R') (R' := R) κ,
    f.f = (NumericalRuleRelabel.overIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).inv ∧
      ∀ g : NumericalDerivation.codeAlgebra R' ⟶
          NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R') (R' := R) κ,
        g = f := by
  refine ⟨NumericalRuleRelabel.relabelFold (F := F) (N := N) (R := R') (R' := R) κ, ?_, ?_⟩
  · exact (NumericalRuleRelabel.inverse_is_fold (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).symm
  · intro g
    exact (NumericalDerivation.codeInitial R').hom_ext _ _

example : (NumericalRuleRelabel.overIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom =
    ((NumericalDerivation.codeInitial R).to (NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R) (R' := R') ι)).f :=
  NumericalRuleRelabel.relabel_is_fold (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

example : (NumericalRuleRelabel.overIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).inv =
    ((NumericalDerivation.codeInitial R').to (NumericalRuleRelabel.targetAlgebra (F := F) (N := N) (R := R') (R' := R) κ)).f :=
  NumericalRuleRelabel.inverse_is_fold (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

example (i : Fin (N + 1)) :
    NumericalRuleRelabel.inputRelabel (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ ι.map i :=
  NumericalRuleRelabel.input_label (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i

example (i : Fin (N + 1)) :
    NumericalRuleRelabel.inputRelabel (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ finitePowerMap (NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom i.val :=
  NumericalRuleRelabel.input_children (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i

example (i : Fin (N + 1)) :
    NumericalRuleRelabel.inputRelabel (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i ≫
        Sigma.ι (R'.ruleObject (NumericalDerivation.codeAlgebra R').a) i ≫
          (NumericalDerivation.codeAlgebra R').str.left =
      Sigma.ι (R.ruleObject (NumericalDerivation.codeAlgebra R).a) i ≫
        (NumericalDerivation.codeAlgebra R).str.left ≫ (NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom :=
  NumericalRuleRelabel.branch_constructor (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι i

example : ∃ p : ℕ → Part ℕ, Partrec p ∧
    ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject R),
      p x.val = Part.some (((NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).hom.toFun x).val) :=
  NumericalRuleRelabel.forward_realizer (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι

example : ∃ p : ℕ → Part ℕ, Partrec p ∧
    ∀ x : NumericalTuples.Point (NumericalDerivation.codeObject R'),
      p x.val = Part.some (((NumericalRuleRelabel.codeIso (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι).inv.toFun x).val) :=
  NumericalRuleRelabel.backward_realizer (F := F) (N := N) (R := R) (R' := R') ι κ hικ hκι
