/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SignedDerivationCarrier
public import CategoricalEssentialIncompleteness.V46DerivationFiniteSupport
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedFiniteSupport
public import CategoricalEssentialIncompleteness.V46SyntacticListsStable

/-! # Positive leaf assignment on the canonical signed proof algebra -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution

namespace CategoricalEssentialIncompleteness.V46.SignedDerivation

section Lookup
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Both recursive numerical lookup operations have the same value in
every PA model, including at nonstandard vector lengths. -/
theorem member_eq_lookup (n labels : M) :
    member n labels = ArithmeticFiniteLookup.lookup n labels := by
  rcases member_boolean n labels with hz | ho
  · have hm : ¬ MemVec n labels := by
      intro h
      have hone : member n labels = 1 :=
        (member_eq_one_iff _ _).mpr (by simpa only [MemVec, eq_comm] using h)
      exact zero_ne_one (hz.symm.trans hone)
    exact hz.trans ((ArithmeticFiniteLookup.lookup_zero_iff _ _).mpr hm).symm
  · have hm : MemVec n labels := by
      simpa only [MemVec, eq_comm] using (member_eq_one_iff _ _).mp ho
    exact ho.trans ((ArithmeticFiniteLookup.lookup_one_iff _ _).mpr hm).symm

theorem membership_graph_comparison (out n labels : M) :
    memberGraph.val.Evalb ![out, labels, n] ↔
      ArithmeticFiniteLookup.graph.val.Evalb ![out, n, labels] := by
  rw [memberGraph_eval, ArithmeticFiniteLookup.graph_iff_recursiveGraph,
    ArithmeticFiniteLookup.recursiveGraph_eval, member_eq_lookup]

end Lookup

def membershipComparisonSentence : ArithmeticSentence :=
  “∀ out n labels, !memberGraph.val out labels n ↔ !ArithmeticFiniteLookup.graph.val out n labels”

theorem membership_comparison_PA : 𝗣𝗔 ⊢ membershipComparisonSentence := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff]
  simpa [membershipComparisonSentence] using (membership_graph_comparison (M := M))

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def positiveLeafAssignment (L A B : PredicateCategory T) :
    @Quiver.Hom (PredicateCategory T) inferInstance
      (Limits.coprod (C := PredicateCategory T) L (Limits.coprod (C := PredicateCategory T) A B))
      (SyntacticLists.stableListAlgebra T A).algebra.carrier :=
  let K := SyntacticLists.stableListAlgebra T A
  coprod.desc (terminal.from L ≫ K.algebra.nil)
    (coprod.desc K.singleton (terminal.from B ≫ K.algebra.nil))

variable {L A B V S F : PredicateCategory T}
variable (logical : L ⟶ F) (sentence : S ⟶ F) (axioms : A ⨿ B ⟶ S)
variable (all : V ⨯ F ⟶ F) (imp : F ⨯ F ⟶ F)
local notation "R" => firstOrderRules logical sentence axioms all imp
local notation "K" => SyntacticLists.stableListAlgebra T A
local notation "P" => SyntacticDerivation.derivationAlgebra T R

def positiveSupport : (P).a.left ⟶ (K).algebra.carrier :=
  DerivationFiniteSupport.collect R K P (SyntacticDerivation.derivationInitial T R)
    (positiveLeafAssignment T L A B)

@[reassoc] theorem canonical_nullary_collect :
    SyntacticDerivation.nullaryDerivation T R ≫
      positiveSupport T logical sentence axioms all imp = positiveLeafAssignment T L A B := by
  change ((R).nullaryRule (P).a ≫ DerivationFiniteSupport.ruleConstructor R P 0) ≫
    DerivationFiniteSupport.collect R K P (SyntacticDerivation.derivationInitial T R)
      (positiveLeafAssignment T L A B) = _
  rw [Category.assoc, DerivationFiniteSupport.nullary_collect, ← Category.assoc,
    RulePresentation.nullaryRule_fst, Category.id_comp]

@[reassoc] theorem canonical_logical_collect :
    (coprod.inl ≫ SyntacticDerivation.nullaryDerivation T R) ≫
      positiveSupport T logical sentence axioms all imp = terminal.from L ≫ (K).algebra.nil := by
  simp [Category.assoc, canonical_nullary_collect, positiveLeafAssignment]

@[reassoc] theorem canonical_positive_collect :
    (coprod.inl ≫ coprod.inr ≫ SyntacticDerivation.nullaryDerivation T R) ≫
      positiveSupport T logical sentence axioms all imp = (K).singleton := by
  simp [Category.assoc, canonical_nullary_collect, positiveLeafAssignment]

@[reassoc] theorem canonical_negative_collect :
    (coprod.inr ≫ coprod.inr ≫ SyntacticDerivation.nullaryDerivation T R) ≫
      positiveSupport T logical sentence axioms all imp = terminal.from B ≫ (K).algebra.nil := by
  simp [Category.assoc, canonical_nullary_collect, positiveLeafAssignment]

@[reassoc] theorem canonical_unary_collect :
    SyntacticDerivation.derivationConstructor T R 1 ≫
      positiveSupport T logical sentence axioms all imp =
        pullback.snd ((R).premises 1) (finitePowerMap (P).a.hom 1) ≫
          positiveSupport T logical sentence axioms all imp :=
  DerivationFiniteSupport.unary_collect R K P (SyntacticDerivation.derivationInitial T R)
    (positiveLeafAssignment T L A B)

@[reassoc] theorem canonical_binary_collect :
    SyntacticDerivation.derivationConstructor T R 2 ≫
      positiveSupport T logical sentence axioms all imp =
        pullback.snd ((R).premises 2) (finitePowerMap (P).a.hom 2) ≫
          prod.map (positiveSupport T logical sentence axioms all imp)
            (positiveSupport T logical sentence axioms all imp) ≫ (K).append :=
  DerivationFiniteSupport.binary_collect R K P (SyntacticDerivation.derivationInitial T R)
    (positiveLeafAssignment T L A B)

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem canonical_support
    (p : SyntacticLists.Obj T M (P).a.left) :
    (FiniteSigmaOne.allEntriesCondition A).Evalb
      ![((PredicateInterpretation.functor T M).map
        (positiveSupport T logical sentence axioms all imp) p).val] := by
  have h := ((PredicateInterpretation.functor T M).map
    (positiveSupport T logical sentence axioms all imp) p).property
  exact (FiniteSigmaOne.finite_membership_model A _).mpr h

/-- The finite positive supports are constructed from the original
canonical proof algebra; their entry conditions are consequences of typing. -/
theorem canonical_negative_lookup
    (hd : ∀ n : M, A.val.Evalb ![n] → ¬ B.val.Evalb ![n])
    (p q : SyntacticLists.Obj T M (P).a.left) (n : M) (hn : B.val.Evalb ![n]) :
    ArithmeticFiniteLookup.graph.val.Evalb ![0, n, Words.append
      ((PredicateInterpretation.functor T M).map
        (positiveSupport T logical sentence axioms all imp) p).val
      ((PredicateInterpretation.functor T M).map
        (positiveSupport T logical sentence axioms all imp) q).val] := by
  exact ArithmeticFiniteLookup.negative_label_value A B hd _
    ((ArithmeticSignedFiniteSupport.all_entries_append A _ _).mpr
      ⟨canonical_support T logical sentence axioms all imp p,
        canonical_support T logical sentence axioms all imp q⟩) n hn

end Models

end CategoricalEssentialIncompleteness.V46.SignedDerivation
