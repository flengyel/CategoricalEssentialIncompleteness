/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSemantics
public import CategoricalEssentialIncompleteness.V46ModelQuantifierSoundness
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonMembership
public import CategoricalEssentialIncompleteness.V46NamedBooleanReflection
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainOccurrences
public import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables

/-! # The actual absent-variable parameter fiber and distribution soundness -/

@[expose] public section

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Y" => (Postfix.plainCarrier true (termPolynomial σ d) (formulaPolynomial π d) : PredicateCategory 𝗣𝗔)
local notation "G" => F 𝗣𝗔 ℕ

/-- The actual false-membership equalizer enforces absence in the
decoded named formula, with its ordered numerical occurrence list. -/
theorem distribution_absent (r : Obj 𝗣𝗔 ℕ (S).distributionParameters) :
    let q := (G).map (S).distributionInclusion r
    ((G).map (prod.fst (C := PredicateCategory 𝗣𝗔)
      (X := variableCarrier) («Y» := Y ⨯ Y)) q).val ∉
      (decodeFormula σ π d ((G).map
        (prod.fst (C := PredicateCategory 𝗣𝗔) (X := Y) («Y» := Y))
        ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔)
          (X := variableCarrier) («Y» := Y ⨯ Y)) q))).freeVariables := by
  let q := (G).map (S).distributionInclusion r
  let VV : PredicateCategory 𝗣𝗔 := variableCarrier
  let FF : PredicateCategory 𝗣𝗔 := Y
  let names : VV ⨯ (FF ⨯ FF) ⟶ VV ⨯ listObject 𝗣𝗔 VV :=
    prod.lift prod.fst (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences)
  let z := (G).map names q
  let x := (G).map (prod.fst (C := PredicateCategory 𝗣𝗔)
    (X := variableCarrier) («Y» := Y ⨯ Y)) q
  let φ := (G).map (prod.fst (C := PredicateCategory 𝗣𝗔) (X := Y) («Y» := Y))
    ((G).map (prod.snd (C := PredicateCategory 𝗣𝗔)
      (X := variableCarrier) («Y» := Y ⨯ Y)) q)
  have hb : (G).map (membershipArrow 𝗣𝗔 variableCarrier) z =
      (G).map (Two.constant (VV ⨯ listObject 𝗣𝗔 VV) false) z := by
    have h := congrArg (fun f => (G).map f r) (S).distribution_absence
    rw [Functor.map_comp_apply] at h
    change (G).map (names ≫ (S).lists.membership (S).decidableVariables) q = _ at h
    rw [Functor.map_comp_apply] at h
    have hc := model_constant_comp 𝗣𝗔 ℕ ((S).distributionInclusion ≫ names) r false
    rw [Functor.map_comp_apply] at hc
    rw [membershipArrow_eq]
    exact h.trans hc.symm
  have hm := (membershipArrow_point_iff 𝗣𝗔 ℕ variableCarrier z false).mp hb
  have hx : ((G).map (prod.fst : VV ⨯ listObject 𝗣𝗔 VV ⟶ _) z).val = x.val := by
    exact congrArg Subtype.val (model_lift_fst 𝗣𝗔 ℕ _ _ q)
  have hv : ((G).map (prod.snd : VV ⨯ listObject 𝗣𝗔 VV ⟶ _) z).val =
      SyntacticSyntax.NatVectors.pack (decodeFormula σ π d φ).freeVariables := by
    have h := congrArg Subtype.val (model_lift_snd 𝗣𝗔 ℕ
      (prod.fst : VV ⨯ (FF ⨯ FF) ⟶ _)
      (prod.snd ≫ prod.fst ≫ (S).formulaOccurrences) q)
    change ((G).map (prod.snd : VV ⨯ listObject 𝗣𝗔 VV ⟶ _) z).val = _ at h
    rw [Functor.map_comp_apply,Functor.map_comp_apply] at h
    have hf := plain_formulaOccurrences_value 𝗣𝗔 variableCarrier σ π d ℕ φ
    have hn := freeVariables_formulaCode (decodeFormula σ π d φ)
    rw [decodeFormula_code] at hn
    exact h.trans (hf.trans hn)
  change x.val ∉ (decodeFormula σ π d φ).freeVariables
  rw [hx,hv] at hm
  exact (member_pack_eq_zero _ _).mp hm

variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

theorem valid_hilbertDistribution (r : Obj 𝗣𝗔 ℕ (S).distributionParameters) :
    Valid σ π d functions relations ((G).map (S).hilbertDistribution r) := by
  let q := (G).map (S).distributionInclusion r
  have hx := distribution_absent σ π d r
  intro ρ
  rw [CategoricalSyntax.hilbertDistribution,Functor.map_comp_apply]
  exact ModelQuantifierSoundness.valid_distribution (G) (fun x => x.val)
    (S).implicationConstructor (S).quantifierConstructor
    (fun φ τ => Holds σ π d functions relations φ τ)
    (fun z τ => holds_implication σ π d functions relations z τ)
    (fun z τ => holds_quantifier σ π d functions relations z τ)
    q (fun τ a => NamedFiniteSyntax.Formula.holds_update_absent functions relations _ _ τ a hx) ρ

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
