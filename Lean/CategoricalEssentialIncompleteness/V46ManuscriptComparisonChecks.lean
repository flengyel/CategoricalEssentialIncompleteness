/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalTranslations
public import CategoricalEssentialIncompleteness.V46OracleSeparatorLift
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxDecomposition

/-! # Presentation, parser and oracle statements in §§4–6 and Appendix C -/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.V46

section Presentations

variable {D : Type*} [Category D] [Regular D] [FinitaryExtensive D] {V : D}
variable {P Q : FirstOrderPresentation V}

example (A : Subobject Q.syntaxData.sentenceObject) : IsInitial (Q.proofs A) :=
  Q.initial A

example (σ : FirstOrderPresentation.Translation P Q) :
    P.syntaxData.sentenceInclusion ≫ σ.formula = σ.sentence ≫ Q.syntaxData.sentenceInclusion :=
  σ.sentences

end Presentations

section Naturality

variable {C D : Type*} [Category C] [Category D]
variable (B : C ⥤ D) (E : D ⥤ C) (e : B ⋙ E ≅ 𝟭 C)

example {S F : C} (sentence : S ⟶ F) :
    sentence ≫ e.inv.app F = e.inv.app S ≫ E.map (B.map sentence) :=
  e.inv.naturality sentence

end Naturality

section Postfix

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.Postfix

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (formula : Bool) (a b : RawPolynomial) (word : M) :
    (carrier formula a b).val.Evalb ![word] ↔
      ∃! u : M, (rawCarrier (carrier false a b) (carrier true a b)
        (if formula then b else a)).val.Evalb ![u] ∧
        word = constructor formula (if formula then b else a) u := by
  constructor
  · intro hw
    obtain ⟨u, hu, he⟩ := carrier_decomposition formula a b word hw
    refine ⟨u, ⟨hu, he⟩, ?_⟩
    rintro v ⟨hv, he'⟩
    exact constructor_injective formula a b _ v u hv hu (he'.symm.trans he)
  · rintro ⟨u, ⟨hu, rfl⟩, _⟩
    cases formula
    · exact term_constructor_carrier a b u hu
    · exact formula_constructor_carrier a b u hu

end Postfix

section Oracle

open CategoricalEssentialIncompleteness.LocalConnectedness
open OracleComputation OracleComputation.Restricted

attribute [local instance 2000] nativeRestriction

example (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ))
    (h₀ : Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separatorComplement)
    (h₁ : Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) =
      (rangeFunctor K).mapIdem separator) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K),
      (inclusion K).map ℓ = s ≫ ((rangeFunctor K).comparison (N K) (N K)).hom :=
  no_lift_of_summand_inverse_images s h₀ h₁

example (s : ℕ →. (ℕ ⊕ ℕ))
    (h₀ : ∀ n, (∃ y : ℕ, Sum.inl y ∈ s n) ↔ n ∉ A)
    (h₁ : ∀ n, (∃ y : ℕ, Sum.inr y ∈ s n) ↔ n ∈ A) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K), (inclusion K).map ℓ = s :=
  no_lift_of_output_summands s h₀ h₁

end Oracle
