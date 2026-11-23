/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConnectedNumeralDomains
public import CategoricalEssentialIncompleteness.V46ConnectedDomainStageTests
public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityDiagonal
public import CategoricalEssentialIncompleteness.SyntacticObservations
public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding

/-! # Failure of local connectedness in the syntactic recursion category

For a consistent computably enumerable extension of PA, each nonzero connected restriction
idempotent on the number object lies below a standard numeral. Two programs can agree provably
at each numeral while defining distinct morphisms. Those morphisms witness the claim of
Di Paola and Montagna, Corollary 4.4, cited in Appendix D.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Limits (zero_comp)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.UniformIndexQuotient
open FailureOfComposition.ConcreteIndices
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

attribute [local irreducible] stageParity

/-- The bounded diagonal test at the numeral for `n`. -/
def stageAt (j n : ℕ) : Carrier := .mkSigma “s. !(stageParity j).val !!n s”

private theorem stageAt_eval {M : Type} [ORingStructure M] (j n : ℕ) (x : M) :
    (stageAt j n).val.Evalb ![x] ↔ (stageParity j).val.Evalb ![ORingStructure.numeral n, x] := by
  simp [stageAt]

/-- An input satisfies this formula when every stage in `C` has the specified parity. -/
def decisionFormula (C : Carrier) (j : ℕ) : ArithmeticSemisentence 1 :=
  “n. ∀ x, !C.val x → !(stageParity j).val n x”

private theorem decision_eval {M : Type} [ORingStructure M] (C : Carrier) (j : ℕ) (n : M) :
    (decisionFormula C j).Evalb ![n] ↔ ∀ x : M, C.val.Evalb ![x] →
      (stageParity j).val.Evalb ![n, x] := by simp [decisionFormula]

private def decisions (C : Carrier) (j : ℕ) : Set ℕ :=
  {n | T ⊢ ((decisionFormula C j)/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)}

private theorem decision_iff (C : Carrier) (j n : ℕ) : n ∈ decisions T C j ↔
    Implies T C (stageAt j n) := by
  constructor
  · intro h M _ _ x hx
    have hp := consequence_iff.mp (Theory.Proof.sound h) M inferInstance
    rw [ClassicalPrograms.numeralInstance_eval, decision_eval] at hp
    exact (stageAt_eval j n x).mpr (hp x hx)
  · intro h
    apply Arithmetic.complete.{0} T
    intro M _ _
    rw [ClassicalPrograms.numeralInstance_eval, decision_eval]
    exact fun x hx => (stageAt_eval j n x).mp (h M x hx)

private theorem decisions_complement (C : Carrier) (hc : Connected (predicateIdem T C))
    (hne : predicateIdem T C ≠ ⊥) (n : ℕ) : n ∈ decisions T C 0 ↔ n ∉ decisions T C 1 := by
  have hPN (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : M) :
      (stageAt 0 n).val.Evalb ![x] ↔ ¬(stageAt 1 n).val.Evalb ![x] := by
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [stageAt_eval, stageAt_eval, stageParity_complement]
  rw [decision_iff, decision_iff]
  constructor
  · intro h0 h1
    exact hne (predicate_bot T C fun M _ _ x hx => (hPN M x).mp (h0 M x hx) (h1 M x hx))
  · exact (connected_decides T C _ _ hc hPN).resolve_left

/-- Every nonzero connected restriction idempotent is supported on one standard numeral. -/
theorem connected_le_numeral [T.RE] (a : Idem (omegaObject T)) (hc : Connected a) (hne : a ≠ ⊥) :
    ∃ n, a ≤ predicateIdem T (numeralPredicate n) := by
  obtain ⟨C, rfl⟩ := omegaIdem_is_predicate T a
  simp_rw [predicate_le]
  by_contra hn
  have hre (j : ℕ) : REPred (· ∈ decisions T C j) :=
    SyntacticModel.numeral_provability_enumerable T (decisionFormula C j)
  have hrec : ComputablePred (· ∈ decisions T C 1) :=
    ComputablePred.computable_iff_re_compl_re'.mpr
      ⟨hre 1, (hre 0).of_eq (decisions_complement T C hc hne)⟩
  apply ArithmeticSentenceInseparability.diagonal_no_recursive_separator
  refine ⟨decisions T C 1, hrec, ?_, Set.disjoint_left.mpr ?_⟩
  · intro n ha
    obtain ⟨t, ht⟩ := (alpha_iff_stage (M := ℕ) n).mp ha
    apply (decision_iff T C 1 n).mpr
    intro M _ _ x hx
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    exact (stageAt_eval 1 n x).mpr (stageParity_mono _ _ _
      (bounds_of_no_numeral T C hc hn t M x hx) (standard_stage n t ht))
  · intro n hp hb
    have hneg := ArithmeticDiagonalCodes.beta_numeral_refutes_alpha n hb
    have h1 := (decision_iff T C 1 n).mp hp
    apply hne (predicate_bot T C ?_)
    intro M _ _ x hx
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    have hh := consequence_iff.mp (Theory.Proof.sound hneg) M inferInstance
    rw [Semantics.Not.models_not, ClassicalPrograms.numeralInstance_eval] at hh
    exact hh ((alpha_iff_stage _).mpr ⟨x, (stageAt_eval 1 n x).mp (h1 M x hx)⟩)

private theorem pointwise_of_class_eq {e f : ℕ} (h : classOf T e = classOf T f) :
    PointwiseIndex T e f := by
  apply (pointwiseIndex_iff T e f).mpr
  intro n
  apply Arithmetic.complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, eqAt_eval]
  exact fun y => SyntacticModel.uniform_model T M ((classOf_eq_classOf_iff T e f).mp h) _ y

/-- Numeralwise provable graph equality gives equality on the corresponding partial identity. -/
theorem numeral_restriction_eq {e f : ℕ} (h : PointwiseIndex T e f) (n : ℕ) :
    (predicateIdem T (numeralPredicate n)).hom ≫ omegaArrow T (classOf T e) =
      (predicateIdem T (numeralPredicate n)).hom ≫ omegaArrow T (classOf T f) := by
  apply CodedHom.ext
  apply programClass_ext T
  intro M _ _ x y
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  have hp := consequence_iff.mp (Theory.Proof.sound ((pointwiseIndex_iff T e f).mp h n))
    M inferInstance
  rw [models_iff, eqAt_eval] at hp
  change SyntacticModel.programRelation T M
    (classOf T e * predicateClass T (numeralPredicate n)) x y ↔
    SyntacticModel.programRelation T M (classOf T f * predicateClass T (numeralPredicate n)) x y
  simp only [restricted_program_model, numeralPredicate_eval, SyntacticModel.programRelation_class]
  exact and_congr_right fun hx => by simpa only [hx, numeral_eq_natCast] using hp y

/-- Distinct morphisms on the number object agree after every connected restriction. -/
theorem indistinguishable_on_connected [Consistent T] (hT : REPred (AxiomCodes T)) :
    ∃ f g : omegaObject T ⟶ omegaObject T, f ≠ g ∧
      ∀ a : Idem (omegaObject T), Connected a → a.hom ≫ f = a.hom ≫ g := by
  let : T.RE := ⟨(hT.comp Computable.encode).of_eq (fun σ => by
    simp only [AxiomCodes, Sentence.quote_eq_encode_nat, Encodable.encode_inj]
    simp)⟩
  obtain ⟨e, f, g, hef, hcomp⟩ := index_noncongruence_via_godel_of_re_axioms T hT
  refine ⟨omegaArrow T (classOf T e), omegaArrow T (classOf T f), ?_, ?_⟩
  · intro he
    have h := congrArg (fun k : omegaObject T ⟶ omegaObject T => k.val * classOf T g) he
    exact hcomp (pointwise_of_class_eq T h)
  · intro a ha
    by_cases hz : a = ⊥
    · subst a
      simp
    · obtain ⟨n, hn⟩ := connected_le_numeral T a ha hz
      exact comp_eq_of_supported _ _ (Idem.le_def.mp hn) _ _ (numeral_restriction_eq T hef n)

theorem not_locallyConnected [Consistent T] (hT : REPred (AxiomCodes T)) :
    ¬LocallyConnected (CodedProgramCategory T) := by
  intro h
  obtain ⟨f, g, hne, he⟩ := indistinguishable_on_connected T hT
  exact hne (h.hom_ext f g he)

open PrintedObjectCoding (NormalizedCategory)
open CategoryTheory.Limits (HasZeroMorphisms comp_zero)

instance : HasZeroMorphisms (NormalizedCategory T) where
  zero _ _ := ⟨InducedCategory.homMk 0⟩
  comp_zero := by intro X Y f Z; exact InducedCategory.hom_ext comp_zero
  zero_comp := by intro X Y Z f; exact InducedCategory.hom_ext zero_comp

instance : RestrictionZero (NormalizedCategory T) where
  restrict_zero _ _ := InducedCategory.hom_ext (RestrictionZero.restrict_zero _ _)

/-- In the presentation by formal terms, the restriction idempotents at each term have
the order of the numerical restriction idempotents. -/
def numeralIdemOrderIso (X : NormalizedCategory T) : Idem X ≃o Idem (omegaObject T) where
  toFun a := ⟨a.hom.hom, congrArg (fun f : X ⟶ X => f.hom) a.restriction⟩
  invFun a := ⟨InducedCategory.homMk a.hom, InducedCategory.hom_ext a.restriction⟩
  left_inv _ := Idem.ext rfl
  right_inv _ := Idem.ext rfl
  map_rel_iff' {a b} := by
    change a.hom.hom ≫ b.hom.hom = a.hom.hom ↔ a.hom ≫ b.hom = a.hom
    exact ⟨fun h => InducedCategory.hom_ext h, congrArg (fun f : X ⟶ X => f.hom)⟩

instance : BinaryJoins (NormalizedCategory T) where
  join {X} a b := (numeralIdemOrderIso T X).symm (numeralIdemOrderIso T X a ⊔
    numeralIdemOrderIso T X b)
  le_left {X} _ _ := (numeralIdemOrderIso T X).le_symm_apply.mpr le_sup_left
  le_right {X} _ _ := (numeralIdemOrderIso T X).le_symm_apply.mpr le_sup_right
  least {X} _ _ _ ha hb := (numeralIdemOrderIso T X).symm_apply_le.mpr
    (sup_le ((numeralIdemOrderIso T X).monotone ha) ((numeralIdemOrderIso T X).monotone hb))

theorem connected_numeralIdem {X : NormalizedCategory T} (a : Idem X) (ha : Connected a) :
    Connected (numeralIdemOrderIso T X a) := by
  let E := numeralIdemOrderIso T X
  intro b c he hd
  have he' : a = E.symm b ⊔ E.symm c := by
    apply E.injective
    simpa only [E.map_sup, E.apply_symm_apply] using he
  have hd' : E.symm b ⊓ E.symm c = ⊥ := by
    apply E.injective
    simpa only [E.map_inf, E.map_bot, E.apply_symm_apply] using hd
  rcases ha _ _ he' hd' with h | h
  · left
    simpa only [E.apply_symm_apply, E.map_bot] using congrArg E h
  · right
    simpa only [E.apply_symm_apply, E.map_bot] using congrArg E h

/-- The unprimed category on formal object terms fails local connectedness for every
consistent computably enumerable extension of PA in the fixed arithmetic language. -/
theorem normalized_not_locallyConnected [Consistent T] (hT : REPred (AxiomCodes T)) :
    ¬LocallyConnected (NormalizedCategory T) := by
  intro h
  obtain ⟨f, g, hne, he⟩ := indistinguishable_on_connected T hT
  let X : NormalizedCategory T := .omega
  let F : X ⟶ X := ⟨f⟩
  let G : X ⟶ X := ⟨g⟩
  have eq := h.hom_ext F G (by
    intro a ha
    apply InducedCategory.hom_ext
    exact he _ (connected_numeralIdem T a ha))
  exact hne (congrArg (fun k : X ⟶ X => k.hom) eq)

omit [𝗣𝗔 ⪯ T] in
theorem axiomCodes_enumerable [T.RE] : REPred (AxiomCodes T) := by
  have he : REPred (fun p : ℕ × ArithmeticSentence => Encodable.encode p.2 = p.1) :=
    (Primrec.eq.comp (Primrec.encode.comp Primrec.snd) Primrec.fst).computablePred.to_re
  apply (he.and ((Theory.RE.re (T := T)).comp Computable.snd)).projection.of_eq
  intro n
  simp only [AxiomCodes, Sentence.quote_eq_encode_nat]

theorem unprimed_not_locallyConnected [Consistent T] [T.RE] :
    ¬LocallyConnected (NormalizedCategory T) :=
  normalized_not_locallyConnected T (axiomCodes_enumerable T)

end CategoricalEssentialIncompleteness.V46.ConnectedNumeralDomains
