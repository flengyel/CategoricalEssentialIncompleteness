/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonAdmissibleValues
public import CategoricalEssentialIncompleteness.V46SyntaxOptionClassifier

/-! # The substitution-domain classifier realizes independent free-for -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

section ModelGeometry
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Interpret a true-fiber pullback. The morphism and classifier remain opaque; neither a
point-image property nor a free-for fact is assumed as a construction field. -/
theorem model_classifier_image_iff {A D : PredicateCategory T}
    (ι : A ⟶ D) (χ : D ⟶ Two (PredicateCategory T))
    (h : IsPullback ι (terminal.from A) χ
      (Two.point (C := PredicateCategory T) true)) (q : Obj T M D) :
    (∃ a : Obj T M A, (F T M).map ι a = q) ↔
      (F T M).map χ q = (F T M).map (Two.constant D true) q := by
  change (∃ a : Obj T M A, (F T M).map ι a = q) ↔
    (F T M).map χ q = (F T M).map
      (terminal.from D ≫ Two.point (C := PredicateCategory T) true) q
  rw [Functor.map_comp_apply]
  constructor
  · rintro ⟨a,ha⟩
    have hterm := congrArg (fun f => (F T M).map f a)
      (terminalIsTerminal.hom_ext (terminal.from A) (ι ≫ terminal.from D))
    have ht : (F T M).map (terminal.from A) a = (F T M).map (terminal.from D) q :=
      hterm.trans (((F T M).map_comp_apply ι (terminal.from D) a).trans
        (congrArg ((F T M).map (terminal.from D)) ha))
    have hc := parameterPoint_diagram T M ι χ (terminal.from A)
      (Two.point (C := PredicateCategory T) true) h.w a
    exact (congrArg ((F T M).map χ) ha).symm.trans
      (hc.trans (congrArg ((F T M).map (Two.point (C := PredicateCategory T) true)) ht))
  · intro hq
    obtain ⟨a,ha,_⟩ := Types.exists_of_isPullback (h.map (F T M)) q
      ((F T M).map (terminal.from D) q) hq
    exact ⟨a,ha⟩

end ModelGeometry

variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "X" => (syntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)

/-- The categorical success classifier. Its agreement with the
independently defined numerical free-for recursion is proved below. -/
def canonicalFreeForClassifier : @Quiver.Hom (PredicateCategory T) inferInstance
    (Y ⨯ P) (Two (PredicateCategory T)) :=
  (S).formulaSubstitutionOption ≫ SyntaxOptionTransport.optionTag (C := PredicateCategory T) Y

/-- This is a pullback of the true point by the classifier; it precedes comparison with
any numerical flag. -/
theorem canonicalFreeForClassifier_isPullback :
    IsPullback (S).admissibleInclusion (terminal.from (S).admissibleSubstitution)
      (canonicalFreeForClassifier T V σ π d)
      (Two.point (C := PredicateCategory T) true) :=
  SyntaxOptionTransport.optionTag_success_isPullback (C := PredicateCategory T)
    («X» := (Y ⨯ P)) («Y» := Y) (S).formulaSubstitutionOption

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- The numerical free-for flag is the separate primitive recursive loop field, not a
definition in terms of this categorical success classifier. -/
theorem canonicalFreeForClassifier_model_iff (q : Obj T M (Y ⨯ P)) :
    (F T M).map (canonicalFreeForClassifier T V σ π d) q =
      (F T M).map (Two.constant (C := PredicateCategory T) (Y ⨯ P) true) q ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 :=
  (model_classifier_image_iff T M (S).admissibleInclusion
    (canonicalFreeForClassifier T V σ π d)
    (canonicalFreeForClassifier_isPullback T V σ π d) q).symm.trans
      (canonical_admissible_model_iff T V σ π d M q)

end Models
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
