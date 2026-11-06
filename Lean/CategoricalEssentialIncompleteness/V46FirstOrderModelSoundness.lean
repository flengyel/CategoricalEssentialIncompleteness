/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46FirstOrderLogicalInduction
import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheory

/-! # Model predicates and soundness of the constructed logical derivations

All proof carriers and conclusion maps here are the constructed arbitrary-rule
initial algebras and their actual sentence pullbacks. The predicate wrappers
are definitions of the displayed graph conditions, used before specializing
the syntax algebra to a concrete code presentation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.FirstOrderModelSoundness
open SyntacticDerivation.StandardInduction
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable {V : PredicateCategory T} {σ π : ℕ → PredicateCategory T} {d : ℕ}
variable (S : CategoricalSyntax V σ π d)
variable {A : PredicateCategory T} (axioms : A ⟶ S.sentenceObject)

def proofAlgebra := SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)
def conclusion : (proofAlgebra T S axioms).a.left ⟶ S.algebra.a.2 :=
  (proofAlgebra T S axioms).a.hom
def sentenceProofObject : PredicateCategory T := pullback (conclusion T S axioms) S.sentenceInclusion
def sentenceConclusion : sentenceProofObject T S axioms ⟶ S.sentenceObject := pullback.snd _ _

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

def sentenceFormulaPoint (s : Obj T M S.sentenceObject) : Obj T M S.algebra.a.2 :=
  (F T M).map S.sentenceInclusion s
def negationPoint (s : Obj T M S.sentenceObject) : Obj T M S.sentenceObject :=
  (F T M).map S.sentenceNegation s
def axiomFormulaPoint (a : Obj T M A) : Obj T M S.algebra.a.2 :=
  (F T M).map (axioms ≫ S.sentenceInclusion) a
def conclusionPoint (p : Obj T M (proofAlgebra T S axioms).a.left) : Obj T M S.algebra.a.2 :=
  (F T M).map (conclusion T S axioms) p
def sentencePoint (p : Obj T M (sentenceProofObject T S axioms)) : Obj T M S.sentenceObject :=
  (F T M).map (sentenceConclusion T S axioms) p

variable (Q : Obj T M S.algebra.a.2 → Prop)
def AxiomsProperty : Prop := ∀ a : Obj T M A, Q (axiomFormulaPoint T S axioms M a)
def ConclusionProperty : Prop :=
  ∀ p : Obj T M (proofAlgebra T S axioms).a.left, Q (conclusionPoint T S axioms M p)
def SentenceProperty : Prop :=
  ∀ p : Obj T M (sentenceProofObject T S axioms),
    Q (sentenceFormulaPoint T S M (sentencePoint T S axioms M p))
def sentenceSubset : Set (Obj T M S.sentenceObject) :=
  {s | Q (sentenceFormulaPoint T S M s)}

theorem axiomsProperty_iff : AxiomsProperty T S axioms M Q ↔
    ∀ a : Obj T M A, Q ((F T M).map (axioms ≫ S.sentenceInclusion) a) := Iff.rfl
theorem conclusionProperty_iff : ConclusionProperty T S axioms M Q ↔
    ∀ p : Obj T M (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.left,
      Q ((F T M).map (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom p) :=
  Iff.rfl

theorem sentenceProperty_iff : SentenceProperty T S axioms M Q ↔
    ∀ p : Obj T M (pullback
        (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom S.sentenceInclusion),
      Q ((F T M).map S.sentenceInclusion ((F T M).map
        (pullback.snd (SyntacticDerivation.derivationAlgebra T (S.logicalRules axioms)).a.hom
          S.sentenceInclusion) p)) := Iff.rfl

theorem sentenceProperty_of_conclusion (h : ConclusionProperty T S axioms M Q) :
    SentenceProperty T S axioms M Q := by
  intro p
  have hp := h ((F T M).map (pullback.fst (conclusion T S axioms) S.sentenceInclusion) p)
  have he := congrArg (fun f => (F T M).map f p)
    (pullback.condition (f := conclusion T S axioms) (g := S.sentenceInclusion))
  rw [Functor.map_comp_apply,Functor.map_comp_apply] at he
  change Q ((F T M).map (conclusion T S axioms)
    ((F T M).map (pullback.fst _ _) p)) at hp
  exact (congrArg Q he).mp hp

def validityInclusion : (sentenceSubset T S M Q : Type) ⟶ Obj T M S.sentenceObject := ↾Subtype.val
instance validityInclusion_mono : Mono (validityInclusion T S M Q) :=
  (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective

def factor (h : SentenceProperty T S axioms M Q) :
    Obj T M (sentenceProofObject T S axioms) ⟶ (sentenceSubset T S M Q : Type) :=
  ↾fun p => ⟨sentencePoint T S axioms M p,h p⟩

theorem factor_inclusion (h : SentenceProperty T S axioms M Q) :
    factor T S axioms M Q h ≫ validityInclusion T S M Q =
      (F T M).map (sentenceConclusion T S axioms) := rfl

theorem factor_unique (h : SentenceProperty T S axioms M Q)
    (e : Obj T M (sentenceProofObject T S axioms) ⟶ (sentenceSubset T S M Q : Type))
    (he : e ≫ validityInclusion T S M Q = (F T M).map (sentenceConclusion T S axioms)) :
    e = factor T S axioms M Q h := by
  apply (cancel_mono (validityInclusion T S M Q)).mp
  exact he.trans (factor_inclusion T S axioms M Q h).symm

theorem exists_unique_factor (h : SentenceProperty T S axioms M Q) :
    ∃! e : Obj T M (sentenceProofObject T S axioms) ⟶ (sentenceSubset T S M Q : Type),
      e ≫ validityInclusion T S M Q = (F T M).map (sentenceConclusion T S axioms) :=
  ⟨factor T S axioms M Q h,factor_inclusion T S axioms M Q h,
    fun e he => factor_unique T S axioms M Q h e he⟩

theorem conclusion_range_consistent (h : SentenceProperty T S axioms M Q)
    (hd : Disjoint (sentenceSubset T S M Q)
      (((F T M).map S.sentenceNegation) ⁻¹' sentenceSubset T S M Q)) :
    Disjoint (Set.range ((F T M).map (sentenceConclusion T S axioms)))
      (((F T M).map S.sentenceNegation) ⁻¹'
        Set.range ((F T M).map (sentenceConclusion T S axioms))) := by
  have hs : Set.range ((F T M).map (sentenceConclusion T S axioms)) ⊆ sentenceSubset T S M Q := by
    rintro s ⟨p,rfl⟩
    exact h p
  exact hd.mono hs (Set.preimage_mono hs)

end Models

section Standard
variable [ℕ↓[ℒₒᵣ] ⊧* T] (Q : Obj T ℕ S.algebra.a.2 → Prop)

/-- Standard rule induction applies to the actual constructed proof carrier.
The only axiom hypothesis is the stated predicate on its actual axiom points. -/
theorem conclusion_property
    (hlogical : ∀ l : Obj T ℕ S.logicalParameters, Q ((F T ℕ).map S.logicalAxioms l))
    (haxioms : AxiomsProperty T S axioms ℕ Q)
    (hgeneralization : ∀ z : Obj T ℕ (V ⨯ S.algebra.a.2),
      Q ((F T ℕ).map (prod.snd : V ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z) →
        Q ((F T ℕ).map S.quantifierConstructor z))
    (hmodusPonens : ∀ z : Obj T ℕ (S.algebra.a.2 ⨯ S.algebra.a.2),
      Q ((F T ℕ).map (prod.fst : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z) →
      Q ((F T ℕ).map S.implicationConstructor z) →
      Q ((F T ℕ).map (prod.snd : S.algebra.a.2 ⨯ S.algebra.a.2 ⟶ S.algebra.a.2) z)) :
    ConclusionProperty T S axioms ℕ Q :=
  firstOrder_conclusion_induction T S.logicalAxioms S.sentenceInclusion axioms
    S.quantifierConstructor S.implicationConstructor Q hlogical haxioms
    hgeneralization hmodusPonens

end Standard

/-- This is the existing generated-theory algebra, literally, when the
constructed plain syntax is supplied. Its carrier and constructors agree. -/
theorem proofAlgebra_plain (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T)
    (d : ℕ) {A : PredicateCategory T}
    (axioms : A ⟶ (SyntacticSyntax.plainCategoricalSyntax T V σ π d).sentenceObject) :
    proofAlgebra T (SyntacticSyntax.plainCategoricalSyntax T V σ π d) axioms =
      SyntacticGeneratedTheory.proofAlgebra T V σ π d axioms := rfl

theorem sentenceProofObject_plain (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T)
    (d : ℕ) {A : PredicateCategory T}
    (axioms : A ⟶ (SyntacticSyntax.plainCategoricalSyntax T V σ π d).sentenceObject) :
    sentenceProofObject T (SyntacticSyntax.plainCategoricalSyntax T V σ π d) axioms =
      SyntacticGeneratedTheory.sentenceProofObject T V σ π d axioms := rfl

theorem conclusion_plain (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T)
    (d : ℕ) {A : PredicateCategory T}
    (axioms : A ⟶ (SyntacticSyntax.plainCategoricalSyntax T V σ π d).sentenceObject) :
    conclusion T (SyntacticSyntax.plainCategoricalSyntax T V σ π d) axioms =
      SyntacticGeneratedTheory.conclusion T V σ π d axioms := rfl

theorem sentenceConclusion_plain (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T)
    (d : ℕ) {A : PredicateCategory T}
    (axioms : A ⟶ (SyntacticSyntax.plainCategoricalSyntax T V σ π d).sentenceObject) :
    sentenceConclusion T (SyntacticSyntax.plainCategoricalSyntax T V σ π d) axioms =
      SyntacticGeneratedTheory.sentenceConclusion T V σ π d axioms := rfl

end CategoricalEssentialIncompleteness.V46.FirstOrderModelSoundness
