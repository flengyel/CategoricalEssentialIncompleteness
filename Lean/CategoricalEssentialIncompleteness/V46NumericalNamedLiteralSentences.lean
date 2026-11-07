/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralOperations

/-! # The actual sentence pullback under the numerical constructor comparison -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport
section GenericPullback
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (i : E.functor.obj S₀.algebra.a.2 ≅ S₁.algebra.a.2)
variable (j : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hFV : E.functor.map S₀.formulaOccurrences ≫ j.hom = i.hom ≫ S₁.formulaOccurrences)
variable (hNil : E.functor.map S₀.lists.algebra.nil ≫ j.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)

include hFV hNil in
theorem mapped_sentence_pullback :
    IsPullback (E.functor.map S₀.sentenceInclusion ≫ i.hom)
      (E.functor.map (pullback.snd S₀.formulaOccurrences S₀.lists.algebra.nil) ≫
        (DecidableVariables.Transport.terminalIso E).hom)
      S₁.formulaOccurrences S₁.lists.algebra.nil := by
  apply (E.functor.map_isPullback
    (IsPullback.of_hasPullback S₀.formulaOccurrences S₀.lists.algebra.nil)).of_iso
    (Iso.refl (E.functor.obj S₀.sentenceObject)) i
    (DecidableVariables.Transport.terminalIso E) j
  · simp [CategoricalSyntax.sentenceInclusion, CategoricalSyntax.sentenceObject]
  · simp [CategoricalSyntax.sentenceObject]
  · exact hFV
  · exact hNil
end GenericPullback

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d

theorem literalSentence_isPullback :
    IsPullback ((E).functor.map (S₀).sentenceInclusion ≫ (literalFormulaIso V σ π d).hom)
      ((E).functor.map (pullback.snd (S₀).formulaOccurrences (S₀).lists.algebra.nil) ≫
        (DecidableVariables.Transport.terminalIso E).hom)
      (S₁).formulaOccurrences (S₁).lists.algebra.nil :=
  mapped_sentence_pullback (E) V σ π d (S₀) (S₁)
    (literalFormulaIso V σ π d) (literalListIso V σ π d)
    ((formulaOccurrenceComparison_iff (E) V σ π d (S₀) (S₁)
      (literalListsEquality V σ π d) (literalAlgebraIso V σ π d)).mp
        (literal_formulaOccurrences_comparison V σ π d))
    (syntaxList_nil_comparison (E) V σ π d (S₀) (S₁) (literalListsEquality V σ π d))

def literalSentenceIso : (E).functor.obj (S₀).sentenceObject ≅ (S₁).sentenceObject :=
  (literalSentence_isPullback V σ π d).isoPullback

@[reassoc] theorem literalSentenceIso_inclusion :
    (literalSentenceIso V σ π d).hom ≫ (S₁).sentenceInclusion =
      (E).functor.map (S₀).sentenceInclusion ≫ (literalFormulaIso V σ π d).hom :=
  (literalSentence_isPullback V σ π d).isoPullback_hom_fst

end CategoricalEssentialIncompleteness.V46.NumericalNamed
