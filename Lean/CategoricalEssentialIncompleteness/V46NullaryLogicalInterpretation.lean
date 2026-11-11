/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalEquality
public import CategoricalEssentialIncompleteness.V46LogicalTranslations

/-! # Logical translations from the language of nullary predicates -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def logicalParameterMap : S.logicalParameters ⟶ Q.logicalParameters :=
  coprod.map
    (coprod.map
      (coprod.map
        (coprod.map
          (coprod.map
            (coprod.map
              (prod.map (interpretation S Q f).2 (interpretation S Q f).2)
              (prod.map (prod.map (interpretation S Q f).2 (interpretation S Q f).2)
                (interpretation S Q f).2))
            (prod.map (interpretation S Q f).2 (interpretation S Q f).2))
          (instantiationInterpretation S Q f))
        (distributionInterpretation S Q f))
      (interpretation S Q f).1)
    (equalitySchemeInterpretation S Q f)

theorem logical_axioms_comparison :
    logicalParameterMap S Q f ≫ Q.logicalAxioms = S.logicalAxioms ≫ (interpretation S Q f).2 := by
  unfold logicalParameterMap CategoricalSyntax.logicalAxioms
  repeat' apply coprod.hom_ext
  all_goals simp only [coprod.inl_map_assoc, coprod.inr_map_assoc,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc]
  · exact (hilbert_one_comparison S Q f).symm
  · exact (hilbert_two_comparison S Q f).symm
  · exact (hilbert_three_comparison S Q f).symm
  · exact (hilbert_instantiation_comparison S Q f).symm
  · exact (hilbert_distribution_comparison S Q f).symm
  · exact (hilbert_reflexivity_comparison S Q f).symm
  · exact (hilbert_equality_comparison S Q f).symm

variable (proofs : (A : Subobject S.sentenceObject) →
  Endofunctor.Algebra (S.logicalRules A.arrow).inference)
variable (initial : ∀ A, IsInitial (proofs A))

def presentation : FirstOrderPresentation V where
  functions := fun _ => ⊥_ D
  relations := fun _ => X
  bound := 0
  syntaxData := S
  proofs := proofs
  initial := initial

def translation (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    FirstOrderPresentation.Translation (presentation S proofs initial) R where
  term := (interpretation S R.syntaxData a).1
  formula := (interpretation S R.syntaxData a).2
  sentence := sentenceInterpretation S R.syntaxData a
  variable_law := variable_law S R.syntaxData a
  equality := equality S R.syntaxData a
  negation := negation S R.syntaxData a
  implication := implication S R.syntaxData a
  quantifier := quantifier S R.syntaxData a
  term_substitution := term_substitution S R.syntaxData a
  substitution := ⟨admissibleInterpretation S R.syntaxData a,
    admissibleInterpretation_inclusion S R.syntaxData a,
    admissibleInterpretation_result S R.syntaxData a⟩
  sentences := (sentenceInterpretation_inclusion S R.syntaxData a).symm
  logical_axioms := ⟨logicalParameterMap S R.syntaxData a,
    logical_axioms_comparison S R.syntaxData a⟩

theorem translation_atom (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    atomSentence S ≫ (translation S proofs initial R a).sentence = a :=
  sentenceInterpretation_atom S R.syntaxData a

theorem translation_unique (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject)
    (τ : FirstOrderPresentation.Translation (presentation S proofs initial) R)
    (ha : atomSentence S ≫ τ.sentence = a) : τ = translation S proofs initial R a := by
  have hatom : atomFormula S ≫ τ.formula = a ≫ R.syntaxData.sentenceInclusion := by
    calc
      atomFormula S ≫ τ.formula = (atomSentence S ≫ S.sentenceInclusion) ≫ τ.formula :=
        congrArg (fun k => k ≫ τ.formula) (atomSentence_inclusion S).symm
      _ = (atomSentence S ≫ τ.sentence) ≫ R.syntaxData.sentenceInclusion :=
        (Category.assoc _ _ _).trans
          ((congrArg (fun k => atomSentence S ≫ k) τ.sentences).trans
            (Category.assoc _ _ _).symm)
      _ = a ≫ R.syntaxData.sentenceInclusion :=
        congrArg (fun k => k ≫ R.syntaxData.sentenceInclusion) ha
  have h := unique S R.syntaxData a (τ.term, τ.formula) τ.variable_law τ.equality
    hatom τ.negation τ.implication τ.quantifier
  apply FirstOrderPresentation.Translation.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  apply (cancel_mono R.syntaxData.sentenceInclusion).mp
  calc
    τ.sentence ≫ R.syntaxData.sentenceInclusion = S.sentenceInclusion ≫ τ.formula :=
      τ.sentences.symm
    _ = S.sentenceInclusion ≫ (interpretation S R.syntaxData a).2 :=
      congrArg (fun k => S.sentenceInclusion ≫ k) (congrArg Prod.snd h)
    _ = (translation S proofs initial R a).sentence ≫ R.syntaxData.sentenceInclusion :=
      (sentenceInterpretation_inclusion S R.syntaxData a).symm

theorem translation_comp (R T : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject)
    (τ : FirstOrderPresentation.Translation R T) :
    FirstOrderPresentation.Translation.comp (translation S proofs initial R a) τ =
      translation S proofs initial T (a ≫ τ.sentence) := by
  apply translation_unique
  change atomSentence S ≫ ((translation S proofs initial R a).sentence ≫ τ.sentence) = _
  rw [← Category.assoc, translation_atom]

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
