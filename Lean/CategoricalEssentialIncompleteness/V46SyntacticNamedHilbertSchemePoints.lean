/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertOperations
public import CategoricalEssentialIncompleteness.V46SyntacticFiniteNamedDerivations
public import CategoricalEssentialIncompleteness.V46NamedBooleanReflection
public import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables
public import CategoricalEssentialIncompleteness.V46NamedStandardLists
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonMembership

/-! # Literal named formulas at genuine logical-scheme parameters -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "X" => (Postfix.plainCarrier false (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "Tm" => NamedFiniteSyntax.Term (Symbols σ) d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "G" => F 𝗣𝗔 ℕ

/-- The complete model-value identity is proved before substituting
any concrete syntax object, whose chosen data need not be reduced. -/
private theorem identity_value (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    (A : PredicateCategory T) (a : Obj T M A) :
    ((F T M).map (𝟙 A) a).val = a.val := by
  exact congrArg Subtype.val ((F T M).map_id_apply A a)

theorem hilbertOne_point (φ ψ : Fm) :
    (G).map (S).hilbertOne
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp φ (.imp ψ φ)) := by
  dsimp only [CategoricalSyntax.hilbertOne]
  apply implication_at σ π d
  · exact pairPoint_fst 𝗣𝗔 ℕ _ _
  · apply implication_at σ π d
    · exact pairPoint_snd 𝗣𝗔 ℕ _ _
    · exact pairPoint_fst 𝗣𝗔 ℕ _ _

theorem hilbertTwo_point (φ ψ χ : Fm) :
    (G).map (S).hilbertTwo
      (pairPoint 𝗣𝗔 ℕ
        (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
        (formulaPoint σ π d χ)) =
        formulaPoint σ π d (.imp (.imp φ (.imp ψ χ))
          (.imp (.imp φ ψ) (.imp φ χ))) := by
  dsimp only [CategoricalSyntax.hilbertTwo]
  apply implication_at σ π d
  · apply implication_at σ π d
    · erw [Functor.map_comp_apply,pairPoint_fst,pairPoint_fst]
    · apply implication_at σ π d
      · erw [Functor.map_comp_apply,pairPoint_fst,pairPoint_snd]
      · exact pairPoint_snd 𝗣𝗔 ℕ _ _
  · apply implication_at σ π d
    · exact ((G).map_comp_apply _ _ _).trans
        ((congrArg ((G).map (S).implicationConstructor)
          (pairPoint_fst 𝗣𝗔 ℕ _ _)).trans (implication_point σ π d φ ψ))
    · apply implication_at σ π d
      · erw [Functor.map_comp_apply,pairPoint_fst,pairPoint_fst]
      · exact pairPoint_snd 𝗣𝗔 ℕ _ _

theorem hilbertThree_point (φ ψ : Fm) :
    (G).map (S).hilbertThree
      (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) =
        formulaPoint σ π d (.imp (.imp (.neg ψ) (.neg φ)) (.imp φ ψ)) := by
  dsimp only [CategoricalSyntax.hilbertThree]
  apply implication_at σ π d
  · apply implication_at σ π d
    · apply negation_at σ π d
      exact pairPoint_snd 𝗣𝗔 ℕ _ _
    · apply negation_at σ π d
      exact pairPoint_fst 𝗣𝗔 ℕ _ _
  · exact implication_point σ π d φ ψ

theorem hilbertReflexivity_point (t : Tm) :
    (G).map (S).hilbertReflexivity (termPoint σ π d t) =
      formulaPoint σ π d (.equal t t) := by
  dsimp only [CategoricalSyntax.hilbertReflexivity]
  apply equality_at σ π d
  · apply Subtype.ext
    exact identity_value 𝗣𝗔 ℕ ((S).algebra.a.1) (termPoint σ π d t)
  · apply Subtype.ext
    exact identity_value 𝗣𝗔 ℕ ((S).algebra.a.1) (termPoint σ π d t)

/-- The original instantiation coordinates map to the public substitution
input through its actual permutation morphism. -/
theorem instantiationInput_point (x : ℕ) (φ : Fm) (t : Tm) :
    (G).map (S).instantiationInput
      (pairPoint 𝗣𝗔 ℕ (namePoint x)
        (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (termPoint σ π d t))) =
      substitutionPoint σ π d x φ t := by
  dsimp only [CategoricalSyntax.instantiationInput,substitutionPoint]
  erw [lift_point,lift_point]
  erw [Functor.map_comp_apply,pairPoint_snd,pairPoint_fst,
    pairPoint_fst,Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]

theorem hilbertInstantiation_point (x : ℕ) (φ : Fm) (t : Tm) (ψ : Fm)
    (hff : φ.FreeFor x t) (hs : φ.substitute x t = some ψ) :
    ∃ z : Obj 𝗣𝗔 ℕ (S).instantiationParameters,
      (G).map (S).hilbertInstantiation z = formulaPoint σ π d (.imp (.all x φ) ψ) := by
  obtain ⟨a,ha,hr⟩ := substitution_instance σ π d x φ t ψ hff hs
  let base := pairPoint 𝗣𝗔 ℕ (namePoint x)
    (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (termPoint σ π d t))
  have hb : (G).map (S).instantiationInput base = (G).map (S).admissibleInclusion a :=
    (instantiationInput_point σ π d x φ t).trans ha.symm
  obtain ⟨z,hz,ha'⟩ := pullback_point_exists 𝗣𝗔 ℕ
    (S).instantiationInput (S).admissibleInclusion base a hb
  have hz' : (G).map (S).instantiationInclusion z = base := hz
  have ha'' : (G).map (S).instantiationAdmissible z = a := ha'
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertInstantiation]
  apply implication_at σ π d
  · apply quantifier_at σ π d
    · exact ((G).map_comp_apply _ _ z).trans
        ((congrArg ((G).map prod.fst) hz').trans (pairPoint_fst 𝗣𝗔 ℕ _ _))
    · erw [Functor.map_comp_apply,hz',Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
  · exact ((G).map_comp_apply _ _ z).trans
      ((congrArg ((G).map (S).formulaSubstitution) ha'').trans hr)

/-- The absence condition is checked by the independently computed
ordered FV list and then lifted through the genuine false fiber. -/
theorem distributionPoint_exists (x : ℕ) (φ ψ : Fm) (h : x ∉ φ.freeVariables) :
    ∃ z : Obj 𝗣𝗔 ℕ (S).distributionParameters,
      (G).map (S).distributionInclusion z =
        pairPoint 𝗣𝗔 ℕ (namePoint x)
          (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ)) := by
  let base := pairPoint 𝗣𝗔 ℕ (namePoint x)
    (pairPoint 𝗣𝗔 ℕ (formulaPoint σ π d φ) (formulaPoint σ π d ψ))
  let coordinateArrow : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      ((variableCarrier : PredicateCategory 𝗣𝗔) ⨯ (Y ⨯ Y))
        ((variableCarrier : PredicateCategory 𝗣𝗔) ⨯ listObject 𝗣𝗔 variableCarrier) :=
    prod.lift prod.fst (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences)
  let coords := (G).map coordinateArrow base
  have hm : (G).map (membershipArrow 𝗣𝗔 variableCarrier) coords =
      (G).map (Two.constant (C := PredicateCategory 𝗣𝗔) ((variableCarrier : PredicateCategory 𝗣𝗔) ⨯ listObject 𝗣𝗔 variableCarrier) false) coords := by
    apply (membershipArrow_point_iff 𝗣𝗔 ℕ variableCarrier coords false).mpr
    dsimp only [coords,coordinateArrow]
    erw [model_lift_fst,model_lift_snd,Functor.map_comp_apply,Functor.map_comp_apply,
      pairPoint_snd,pairPoint_fst,plain_formulaOccurrences_value,
      pairPoint_fst,formulaPoint_value]
    exact (congrArg (ConcreteNamedSubstitution.member x)
      (@NamedPostfixEncoding.freeVariables_formulaCode σ π d φ)).trans
        ((NamedPostfixEncoding.member_pack_eq_zero x φ.freeVariables).mpr h)
  have hb : (G).map (S).distributionAbsence base =
      (G).map (Two.constant (C := PredicateCategory 𝗣𝗔) ((variableCarrier : PredicateCategory 𝗣𝗔) ⨯ (Y ⨯ Y)) false) base := by
    change (G).map (coordinateArrow ≫
      (SyntacticLists.stableListAlgebra 𝗣𝗔 variableCarrier).membership
        (SyntacticDecidableVariables.decidableVariables 𝗣𝗔 variableCarrier)) base = _
    erw [← membershipArrow_eq 𝗣𝗔 variableCarrier,Functor.map_comp_apply]
    exact hm.trans (((G).map_comp_apply coordinateArrow (Two.constant (C := PredicateCategory 𝗣𝗔) _ false) base).symm.trans
      (congrArg (fun f => (G).map f base) (Two.comp_constant (C := PredicateCategory 𝗣𝗔) coordinateArrow false)))
  exact booleanFiber_point_exists 𝗣𝗔 ℕ (S).distributionAbsence false base hb

theorem hilbertDistribution_point (x : ℕ) (φ ψ : Fm) (h : x ∉ φ.freeVariables) :
    ∃ z : Obj 𝗣𝗔 ℕ (S).distributionParameters,
      (G).map (S).hilbertDistribution z =
        formulaPoint σ π d (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) := by
  obtain ⟨z,hz⟩ := distributionPoint_exists σ π d x φ ψ h
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertDistribution]
  rw [Functor.map_comp_apply,hz]
  apply implication_at σ π d
  · apply quantifier_at σ π d
    · exact pairPoint_fst 𝗣𝗔 ℕ _ _
    · exact ((G).map_comp_apply _ _ _).trans
        ((congrArg ((G).map (S).implicationConstructor)
          (pairPoint_snd 𝗣𝗔 ℕ _ _)).trans (implication_point σ π d φ ψ))
  · apply implication_at σ π d
    · erw [Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
    · apply quantifier_at σ π d
      · exact pairPoint_fst 𝗣𝗔 ℕ _ _
      · erw [Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]

/-- Both equality instances retain one original body and shared name;
the two success fibers are intersected over those exact coordinates. -/
theorem hilbertEquality_point (x : ℕ) (φ : Fm) (u t : Tm) (ψ χ : Fm)
    (hfu : φ.FreeFor x u) (hft : φ.FreeFor x t)
    (hsu : φ.substitute x u = some ψ) (hst : φ.substitute x t = some χ) :
    ∃ z : Obj 𝗣𝗔 ℕ (S).equalitySchemeParameters,
      (G).map (S).hilbertEquality z =
        formulaPoint σ π d (.imp (.equal u t) (.imp ψ χ)) := by
  obtain ⟨au,hau,hru⟩ := substitution_instance σ π d x φ u ψ hfu hsu
  obtain ⟨admissibleT,hat,hrt⟩ := substitution_instance σ π d x φ t χ hft hst
  let base := pairPoint 𝗣𝗔 ℕ
    (pairPoint 𝗣𝗔 ℕ (namePoint x) (formulaPoint σ π d φ))
    (pairPoint 𝗣𝗔 ℕ (termPoint σ π d u) (termPoint σ π d t))
  have hinputu : (G).map (S).equalityFirstInput base = substitutionPoint σ π d x φ u := by
    dsimp only [CategoricalSyntax.equalityFirstInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
  have hinputt : (G).map (S).equalitySecondInput base = substitutionPoint σ π d x φ t := by
    dsimp only [CategoricalSyntax.equalitySecondInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]
  obtain ⟨zu,hzu,hzu'⟩ := pullback_point_exists 𝗣𝗔 ℕ
    (S).equalityFirstInput (S).admissibleInclusion base au (hinputu.trans hau.symm)
  obtain ⟨zt,hzt,hzt'⟩ := pullback_point_exists 𝗣𝗔 ℕ
    (S).equalitySecondInput (S).admissibleInclusion base admissibleT (hinputt.trans hat.symm)
  obtain ⟨z,hz,hz'⟩ := pullback_point_exists 𝗣𝗔 ℕ
    (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)
    (pullback.fst (S).equalitySecondInput (S).admissibleInclusion)
    zu zt (hzu.trans hzt.symm)
  have hb : (G).map (S).equalitySchemeInclusion z = base := by
    exact ((G).map_comp_apply _ _ z).trans
      ((congrArg ((G).map (pullback.fst (S).equalityFirstInput (S).admissibleInclusion)) hz).trans hzu)
  have hu : (G).map (S).equalityFirstAdmissible z = au := by
    exact ((G).map_comp_apply _ _ z).trans
      ((congrArg ((G).map (pullback.snd (S).equalityFirstInput (S).admissibleInclusion)) hz).trans hzu')
  have ht : (G).map (S).equalitySecondAdmissible z = admissibleT := by
    exact ((G).map_comp_apply _ _ z).trans
      ((congrArg ((G).map (pullback.snd (S).equalitySecondInput (S).admissibleInclusion)) hz').trans hzt')
  refine ⟨z,?_⟩
  dsimp only [CategoricalSyntax.hilbertEquality]
  apply implication_at σ π d
  · calc
      _ = (G).map (S).equalityConstructor
          ((G).map prod.snd ((G).map (S).equalitySchemeInclusion z)) := by
            rw [Functor.map_comp_apply,Functor.map_comp_apply]
            rfl
      _ = (G).map (S).equalityConstructor
          (pairPoint 𝗣𝗔 ℕ (termPoint σ π d u) (termPoint σ π d t)) :=
            congrArg ((G).map (S).equalityConstructor)
              ((congrArg ((G).map prod.snd) hb).trans (pairPoint_snd 𝗣𝗔 ℕ _ _))
      _ = _ := equality_point σ π d u t
  · apply implication_at σ π d
    · exact ((G).map_comp_apply _ _ z).trans
        ((congrArg ((G).map (S).formulaSubstitution) hu).trans hru)
    · exact ((G).map_comp_apply _ _ z).trans
        ((congrArg ((G).map (S).formulaSubstitution) ht).trans hrt)

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
