/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46LogicalSchemes
public import CategoricalEssentialIncompleteness.V46FirstOrderReflection
public import CategoricalEssentialIncompleteness.V46InferenceTranslation

/-! # First-order presentations and logical translations

Translations fix the variable object and preserve logical constructors and
successful substitution. Preservation of logical axiom instances is an
existence condition; a choice of rule witnesses is used only in proofs.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

structure FirstOrderPresentation (V : D) where
  functions : ℕ → D
  relations : ℕ → D
  bound : ℕ
  syntaxData : CategoricalSyntax V functions relations bound
  proofs : (A : Subobject syntaxData.sentenceObject) →
    Endofunctor.Algebra (syntaxData.logicalRules A.arrow).inference
  initial : ∀ A, IsInitial (proofs A)

namespace FirstOrderPresentation

variable {V : D}

abbrev Theories (P : FirstOrderPresentation V) := FirstOrderReflection.Theory P.proofs

/-- The logical rule instances before a nonlogical axiom family is added. -/
def logicalRuleData (P : FirstOrderPresentation V) :
    RulePresentation P.syntaxData.algebra.a.2 2 where
  instances := ![P.syntaxData.logicalParameters, V ⨯ P.syntaxData.algebra.a.2,
    P.syntaxData.algebra.a.2 ⨯ P.syntaxData.algebra.a.2]
  premises := Fin.cases (terminal.from _) (Fin.cases prod.snd
    (Fin.cases (prod.lift prod.fst P.syntaxData.implicationConstructor) (fun i => Fin.elim0 i)))
  conclusion := Fin.cases P.syntaxData.logicalAxioms
    (Fin.cases P.syntaxData.quantifierConstructor
      (Fin.cases prod.snd (fun i => Fin.elim0 i)))

structure Translation (P Q : FirstOrderPresentation V) where
  term : P.syntaxData.algebra.a.1 ⟶ Q.syntaxData.algebra.a.1
  formula : P.syntaxData.algebra.a.2 ⟶ Q.syntaxData.algebra.a.2
  sentence : P.syntaxData.sentenceObject ⟶ Q.syntaxData.sentenceObject
  variable_law : P.syntaxData.variableConstructor ≫ term = Q.syntaxData.variableConstructor
  equality : P.syntaxData.equalityConstructor ≫ formula =
    prod.map term term ≫ Q.syntaxData.equalityConstructor
  negation : P.syntaxData.negationConstructor ≫ formula =
    formula ≫ Q.syntaxData.negationConstructor
  implication : P.syntaxData.implicationConstructor ≫ formula =
    prod.map formula formula ≫ Q.syntaxData.implicationConstructor
  quantifier : P.syntaxData.quantifierConstructor ≫ formula =
    prod.map (𝟙 V) formula ≫ Q.syntaxData.quantifierConstructor
  term_substitution : P.syntaxData.termSubstitution ≫ term =
    prod.map term (prod.map (𝟙 V) term) ≫ Q.syntaxData.termSubstitution
  substitution : ∃ s : P.syntaxData.admissibleSubstitution ⟶ Q.syntaxData.admissibleSubstitution,
    s ≫ Q.syntaxData.admissibleInclusion = P.syntaxData.admissibleInclusion ≫
      prod.map formula (prod.map (𝟙 V) term) ∧
    s ≫ Q.syntaxData.formulaSubstitution = P.syntaxData.formulaSubstitution ≫ formula
  sentences : P.syntaxData.sentenceInclusion ≫ formula =
    sentence ≫ Q.syntaxData.sentenceInclusion
  logical_axioms : ∃ l : P.syntaxData.logicalParameters ⟶ Q.syntaxData.logicalParameters,
    l ≫ Q.syntaxData.logicalAxioms = P.syntaxData.logicalAxioms ≫ formula

namespace Translation

variable {P Q R : FirstOrderPresentation V}

@[ext] theorem ext {σ τ : Translation P Q} (ht : σ.term = τ.term)
    (hf : σ.formula = τ.formula) (hs : σ.sentence = τ.sentence) : σ = τ := by
  cases σ
  cases τ
  cases ht
  cases hf
  cases hs
  rfl

def id (P : FirstOrderPresentation V) : Translation P P where
  term := 𝟙 _
  formula := 𝟙 _
  sentence := 𝟙 _
  variable_law := by simp
  equality := by simp
  negation := by simp
  implication := by simp
  quantifier := by simp
  term_substitution := by simp
  substitution := ⟨𝟙 _, by simp [CategoricalSyntax.substitutionParameters], by simp⟩
  sentences := by simp
  logical_axioms := ⟨𝟙 _, by simp⟩

def comp (σ : Translation P Q) (τ : Translation Q R) : Translation P R where
  term := σ.term ≫ τ.term
  formula := σ.formula ≫ τ.formula
  sentence := σ.sentence ≫ τ.sentence
  variable_law := by rw [← Category.assoc, σ.variable_law, τ.variable_law]
  equality := by
    rw [← Category.assoc, σ.equality, Category.assoc, τ.equality, ← Category.assoc,
      prod.map_map]
  negation := by rw [← Category.assoc, σ.negation, Category.assoc, τ.negation, ← Category.assoc]
  implication := by
    rw [← Category.assoc, σ.implication, Category.assoc, τ.implication,
      ← Category.assoc, prod.map_map]
  quantifier := by
    rw [← Category.assoc, σ.quantifier, Category.assoc, τ.quantifier,
      ← Category.assoc, prod.map_map, Category.id_comp]
  term_substitution := by
    rw [← Category.assoc, σ.term_substitution, Category.assoc, τ.term_substitution,
      ← Category.assoc, prod.map_map, prod.map_map, Category.id_comp]
  substitution := by
    obtain ⟨f, hfi, hfr⟩ := σ.substitution
    obtain ⟨g, hgi, hgr⟩ := τ.substitution
    refine ⟨f ≫ g, ?_, ?_⟩
    · rw [Category.assoc, hgi, ← Category.assoc, hfi, Category.assoc,
        prod.map_map, prod.map_map, Category.id_comp]
    · rw [Category.assoc, hgr, ← Category.assoc, hfr, Category.assoc]
  sentences := by
    rw [← Category.assoc, σ.sentences, Category.assoc, τ.sentences, ← Category.assoc]
  logical_axioms := by
    obtain ⟨l, hl⟩ := σ.logical_axioms
    obtain ⟨m, hm⟩ := τ.logical_axioms
    exact ⟨l ≫ m, by rw [Category.assoc, hm, ← Category.assoc, hl, Category.assoc]⟩

theorem sentence_negation (σ : Translation P Q) :
    P.syntaxData.sentenceNegation ≫ σ.sentence = σ.sentence ≫ Q.syntaxData.sentenceNegation := by
  apply (cancel_mono Q.syntaxData.sentenceInclusion).mp
  simp only [Category.assoc]
  rw [← σ.sentences, ← Category.assoc, P.syntaxData.sentenceNegation_inclusion,
    Category.assoc, σ.negation, ← Category.assoc, σ.sentences, Category.assoc,
    ← Q.syntaxData.sentenceNegation_inclusion]

def logicalAxiomMap (σ : Translation P Q) :
    P.syntaxData.logicalParameters ⟶ Q.syntaxData.logicalParameters :=
  Classical.choose σ.logical_axioms

@[reassoc] theorem logicalAxiomMap_law (σ : Translation P Q) :
    σ.logicalAxiomMap ≫ Q.syntaxData.logicalAxioms = P.syntaxData.logicalAxioms ≫ σ.formula :=
  Classical.choose_spec σ.logical_axioms

def logicalRuleMorphism (σ : Translation P Q) :
    RulePresentation.Translation P.logicalRuleData Q.logicalRuleData where
  formula := σ.formula
  map := Fin.cases σ.logicalAxiomMap (Fin.cases (prod.map (𝟙 V) σ.formula)
    (Fin.cases (prod.map σ.formula σ.formula) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change prod.map (𝟙 V) σ.formula ≫ prod.snd = prod.snd ≫ σ.formula
      simp
    · change prod.map σ.formula σ.formula ≫
          prod.lift prod.fst Q.syntaxData.implicationConstructor =
        prod.lift prod.fst P.syntaxData.implicationConstructor ≫ prod.map σ.formula σ.formula
      apply prod.hom_ext
      · simp
      · simpa [Category.assoc] using σ.implication.symm
  conclusion i := by
    fin_cases i
    · exact σ.logicalAxiomMap_law
    · exact σ.quantifier.symm
    · change prod.map σ.formula σ.formula ≫ prod.snd = prod.snd ≫ σ.formula
      simp

theorem preserves_logical_rules (σ : Translation P Q) :
    ∃ ρ : RulePresentation.Translation P.logicalRuleData Q.logicalRuleData,
      ρ.formula = σ.formula := ⟨σ.logicalRuleMorphism, rfl⟩

/-- A map of nonlogical axiom subobjects extends the logical rule maps.
The source and target keep their own axiom labels. -/
def rulesMap (σ : Translation P Q)
    (A : Subobject P.syntaxData.sentenceObject) (B : Subobject Q.syntaxData.sentenceObject)
    (k : (A : D) ⟶ (B : D)) (hk : k ≫ B.arrow = A.arrow ≫ σ.sentence) :
    RulePresentation.Translation (P.syntaxData.logicalRules A.arrow)
      (Q.syntaxData.logicalRules B.arrow) where
  formula := σ.formula
  map := Fin.cases (coprod.map σ.logicalAxiomMap k)
    (Fin.cases (prod.map (𝟙 V) σ.formula)
      (Fin.cases (prod.map σ.formula σ.formula) (fun i => Fin.elim0 i)))
  premises i := by
    fin_cases i
    · exact terminal.hom_ext _ _
    · change prod.map (𝟙 V) σ.formula ≫ prod.snd = prod.snd ≫ σ.formula
      simp
    · change prod.map σ.formula σ.formula ≫
          prod.lift prod.fst Q.syntaxData.implicationConstructor =
        prod.lift prod.fst P.syntaxData.implicationConstructor ≫
          prod.map σ.formula σ.formula
      apply prod.hom_ext
      · simp
      · simpa [Category.assoc] using σ.implication.symm
  conclusion i := by
    fin_cases i
    · change coprod.map σ.logicalAxiomMap k ≫
          coprod.desc Q.syntaxData.logicalAxioms (B.arrow ≫ Q.syntaxData.sentenceInclusion) =
        coprod.desc P.syntaxData.logicalAxioms (A.arrow ≫ P.syntaxData.sentenceInclusion) ≫
          σ.formula
      apply coprod.hom_ext
      · simp [σ.logicalAxiomMap_law, Category.assoc]
      · simp [← Category.assoc k, hk, σ.sentences, Category.assoc]
    · exact σ.quantifier.symm
    · change prod.map σ.formula σ.formula ≫ prod.snd = prod.snd ≫ σ.formula
      simp

end Translation

instance : Category.{v} (FirstOrderPresentation (D := D) V) where
  Hom := Translation
  id := Translation.id
  comp := Translation.comp
  id_comp σ := by apply Translation.ext <;> simp [Translation.comp, Translation.id]
  comp_id σ := by apply Translation.ext <;> simp [Translation.comp, Translation.id]
  assoc σ τ ρ := by apply Translation.ext <;> simp [Translation.comp, Category.assoc]

end FirstOrderPresentation
end CategoricalEssentialIncompleteness.V46
