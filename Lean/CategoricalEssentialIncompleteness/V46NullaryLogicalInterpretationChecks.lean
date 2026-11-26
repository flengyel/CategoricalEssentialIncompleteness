/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalInterpretation

/-! # Statement checks for logical translations interpreting propositional atoms -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)
open NullaryInterpretation

variable (proofs : (A : Subobject S.sentenceObject) →
  Endofunctor.Algebra (S.logicalRules A.arrow).inference)
variable (initial : ∀ A, IsInitial (proofs A))

example (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    FirstOrderPresentation.Translation (presentation S proofs initial) R :=
  translation S proofs initial R a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.translation

example :
    logicalParameterMap S Q f ≫ Q.logicalAxioms = S.logicalAxioms ≫ (interpretation S Q f).2 :=
  NullaryInterpretation.logical_axioms_comparison S Q f

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.logical_axioms_comparison

example (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject) :
    atomSentence S ≫ (translation S proofs initial R a).sentence = a :=
  NullaryInterpretation.translation_atom S proofs initial R a

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.translation_atom

example (R : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject)
    (τ : FirstOrderPresentation.Translation (presentation S proofs initial) R)
    (ha : atomSentence S ≫ τ.sentence = a) : τ = translation S proofs initial R a :=
  NullaryInterpretation.translation_unique S proofs initial R a τ ha

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.translation_unique

example (R T : FirstOrderPresentation V) (a : X ⟶ R.syntaxData.sentenceObject)
    (τ : FirstOrderPresentation.Translation R T) :
    FirstOrderPresentation.Translation.comp (translation S proofs initial R a) τ =
      translation S proofs initial T (a ≫ τ.sentence) :=
  NullaryInterpretation.translation_comp S proofs initial R T a τ

#print axioms
  CategoricalEssentialIncompleteness.V46.NullaryInterpretation.translation_comp
