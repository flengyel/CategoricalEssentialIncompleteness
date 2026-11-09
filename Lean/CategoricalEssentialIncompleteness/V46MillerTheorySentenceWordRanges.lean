import CategoricalEssentialIncompleteness.V46MillerTheorySentenceWords

/-! # Actual Gamma theorem and refutation ranges in literal sentence coordinates

The comparison uses the constructed native finite-proof equivalence and
the original sentence-word mono. It is valid for every uniformly enumerable
external Gamma, independently of truth or consistency of Gamma.
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWordRanges
open OrderedFieldSyntax TheorySentenceWords
variable (P : Uniform.Family)
local notation "σ" => functionSymbols
local notation "π" => relationSymbols
local notation "d" => bound
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "U" => (Total.underlying (P := P))
variable (Γ : Set ℕ) (hΓ : Uniform.Enumerable P (·∈Γ))

/-- The actual sentence conclusion followed by the proved literal chart. -/
def literalConclusion : NamedProofImage.sentenceProofObject P σ π d Γ hΓ ⟶ literalObject P :=
  NamedProofImage.sentenceConclusion P σ π d Γ hΓ ≫ (sentenceIso P).hom

theorem literalConclusion_graph (p word : ℕ) :
    word∈Total.val (literalConclusion P Γ hΓ).hom p ↔
      word∈Total.val (NamedProofImage.sentenceConclusion P σ π d Γ hΓ ≫
        NamedProofImage.sentenceWord P σ π d).hom p := by
  change word∈Total.val ((NamedProofImage.sentenceConclusion P σ π d Γ hΓ).hom ≫
      (sentenceIso P).hom.hom) p ↔
    word∈Total.val ((NamedProofImage.sentenceConclusion P σ π d Γ hΓ).hom ≫
      (NamedProofImage.sentenceWord P σ π d).hom) p
  rw [Total.mem_val_comp (NamedProofImage.sentenceConclusion P σ π d Γ hΓ).hom (sentenceIso P).hom.hom,
    Total.mem_val_comp (NamedProofImage.sentenceConclusion P σ π d Γ hΓ).hom
      (NamedProofImage.sentenceWord P σ π d).hom]
  exact exists_congr (fun s => and_congr_right (fun _ => toLiteral_graph P s word))

theorem literalConclusion_image : Total.Subobjects.imageCodes (literalConclusion P Γ hΓ)=
    Total.Subobjects.imageCodes (NamedProofImage.sentenceConclusion P σ π d Γ hΓ ≫
      NamedProofImage.sentenceWord P σ π d) := by
  ext word
  exact exists_congr (fun p => literalConclusion_graph P Γ hΓ p word)

/-- Exact regular-image membership at each original named sentence word. -/
theorem theorem_word_iff (φ : Formula) :
    formulaCode φ∈Total.Subobjects.imageCodes (literalConclusion P Γ hΓ) ↔
      FiniteAxiomProof σ π d Γ φ ∧ φ.freeVariables=[] := by
  rw [literalConclusion_image]
  exact NamedProofImage.sentence_word_range_iff P σ π d Γ hΓ φ

/-- The chosen categorical regular image has the same literal outputs. -/
theorem regularImage_word_iff (φ : Formula) :
    formulaCode φ∈Total.Subobjects.imageCodes (image.ι (literalConclusion P Γ hΓ)) ↔
      FiniteAxiomProof σ π d Γ φ ∧ φ.freeVariables=[] := by
  rw [Total.Subobjects.imageCodes_image_ι]
  exact theorem_word_iff P Γ hΓ φ

/-- This covers every scalar input, not merely already decoded formulas. -/
theorem theorem_words : Total.Subobjects.imageCodes (literalConclusion P Γ hΓ)=
    {word | ∃ φ : Formula,formulaCode φ=word ∧ φ.freeVariables=[] ∧
      FiniteAxiomProof σ π d Γ φ} := by
  ext word
  constructor
  · intro hw
    have hs : word∈literalSet := (literal_support P word).mp (by
      obtain ⟨p,hp⟩ := hw
      exact Total.val_target (literalConclusion P Γ hΓ).hom p word hp)
    obtain ⟨φ,hc,rfl⟩ := (literal_iff_native word).mp hs
    exact ⟨φ,rfl,hc,((theorem_word_iff P Γ hΓ φ).mp hw).1⟩
  · rintro ⟨φ,rfl,hc,hφ⟩
    exact (theorem_word_iff P Γ hΓ φ).mpr ⟨hφ,hc⟩

/-- The interpreted theorem idempotent on the proper literal sentence carrier. -/
def theoremIdem : Idem (literalObject P).obj := Ranges.range (literalConclusion P Γ hΓ).hom

def refutationIdem : Idem (literalObject P).obj :=
  Idem.pull (literalNegation P).hom (theoremIdem P Γ hΓ)

theorem theoremIdem_support : Total.support (theoremIdem P Γ hΓ)=
    Total.Subobjects.imageCodes (literalConclusion P Γ hΓ) := Total.support_range _

theorem refutationIdem_support : Total.support (refutationIdem P Γ hΓ)=
    {word | word∈literalSet ∧ negationWord word∈Total.Subobjects.imageCodes (literalConclusion P Γ hΓ)} := by
  rw [refutationIdem,Total.support_pull (literalNegation P).hom (theoremIdem P Γ hΓ),
    theoremIdem_support]
  ext word
  constructor
  · rintro ⟨out,hout,hΓout⟩
    obtain ⟨hs,rfl⟩ := (literalNegation_graph P word out).mp hout
    exact ⟨hs,hΓout⟩
  · rintro ⟨hs,hΓword⟩
    exact ⟨negationWord word,(literalNegation_graph P word _).mpr ⟨hs,rfl⟩,hΓword⟩

/-- Refutation is the actual negation inverse image of the theorem range. -/
theorem refutation_word_iff (φ : Formula) :
    formulaCode φ∈Total.support (refutationIdem P Γ hΓ) ↔
      FiniteAxiomProof σ π d Γ (.neg φ) ∧ φ.freeVariables=[] := by
  rw [refutationIdem_support]
  change (formulaCode φ∈literalSet ∧ negationWord (formulaCode φ)∈
    Total.Subobjects.imageCodes (literalConclusion P Γ hΓ)) ↔ _
  rw [← formulaCode_negation,theorem_word_iff]
  change (sentencePredicate.val.Evalb ![formulaCode φ] ∧
    FiniteAxiomProof σ π d Γ (.neg φ) ∧ φ.freeVariables=[]) ↔ _
  rw [sentence_formulaCode]
  exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h⟩⟩

/-- The top support is the sentence set, not all natural numbers. -/
theorem literal_top_support : Total.support (⊤ : Idem (literalObject P).obj)=literalSet := by
  rw [Total.support_top]
  ext word
  exact literal_support P word

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceWordRanges
