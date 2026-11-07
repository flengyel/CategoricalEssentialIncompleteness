/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalArithmeticRuleComparison
import CategoricalEssentialIncompleteness.V46NumericalArithmeticSentenceProofCodes
import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofImage
import CategoricalEssentialIncompleteness.V46NumericalArithmeticCanonical
import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretation

/-! # Actual arithmetic proof codes, canonical source proofs and fixed Prov_Gamma

The inference signatures are compared before any proof object is compared.
Their two initial code algebras give the full-proof isomorphism, and the
actual sentence pullbacks give the sentence-proof isomorphism. The fixed
Gamma theorem predicate is then the regular image of this actual conclusion.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofComparison
open Coordinates RuleParameters
local notation "K" => numericalInterpretation
local notation "U" => NumericalUnderlying.functor

/-- This targets the exact PA derivation object used by the earlier
arithmetic source construction, with its actual seven-scheme signature. -/
def fullIso (Γ : Carrier) : SentenceProofCodes.allProofs Γ ≅ (K).obj (ProofWords.allProofs Γ) :=
  RuleComparison.proofIso Γ ≪≫
    NumericalDerivationInterpretation.interpretationCodeIso (Rules.originalRules Γ)

@[reassoc] theorem full_conclusion (Γ : Carrier) :
    (fullIso Γ).hom ≫ (K).map (ProofWords.formulaConclusion Γ) =
      SentenceProofCodes.allConclusion Γ ≫ formulaIso.hom := by
  have hn :
      (NumericalDerivationInterpretation.interpretationCodeIso (Rules.originalRules Γ)).hom ≫
          (K).map (ProofWords.formulaConclusion Γ) =
        NumericalDerivation.codeConclusion (RuleComparison.targetRules Γ) :=
    NumericalDerivationInterpretation.interpretationCodeIso_conclusion (Rules.originalRules Γ)
  change ((RuleComparison.proofIso Γ).hom ≫
    (NumericalDerivationInterpretation.interpretationCodeIso (Rules.originalRules Γ)).hom) ≫
      (K).map (ProofWords.formulaConclusion Γ) = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (RuleComparison.proofIso Γ).hom ≫ f) hn).trans
      (RuleComparison.proof_conclusion Γ))

/-- Each proof's own conclusion is matched to the sentence inclusion.
No child or root conclusion is replaced by a shared external parameter. -/
def sentencePullbackIso (Γ : Carrier) : SentenceProofCodes.chosenPullback Γ ≅
    (K).obj (ArithmeticLiteralModel.proofObject Γ) :=
  pullbackComparison (ProofWords.formulaConclusion Γ) originalSyntax.sentenceInclusion
    (SentenceProofCodes.allConclusion Γ) numericalSyntax.sentenceInclusion
    (fullIso Γ) sentenceIso formulaIso (full_conclusion Γ).symm sentence_inclusion.symm

@[reassoc] theorem sentencePullback_conclusion (Γ : Carrier) :
    (sentencePullbackIso Γ).hom ≫ (K).map
        (pullback.snd (ProofWords.formulaConclusion Γ) originalSyntax.sentenceInclusion) =
      pullback.snd (SentenceProofCodes.allConclusion Γ) numericalSyntax.sentenceInclusion ≫ sentenceIso.hom :=
  pullbackComparison_snd _ _ _ _ _ _ _ _ _

/-- The actual original-word numerical carrier is compared to the exact
source sentence-derivation object, including its chosen pullback chart. -/
def rho (Γ : Carrier) : SentenceProofCodes.object Γ ≅ (K).obj (ArithmeticLiteralModel.proofObject Γ) :=
  (SentenceProofCodes.pullbackIso Γ).symm ≪≫ sentencePullbackIso Γ

private theorem cancel_mapped_iso {A B : PredicateCategory 𝗣𝗔} {X : NumericalTuples.Object}
    (f : X ⟶ (K).obj A) (e : A ≅ B) :
    (f ≫ (K).map e.hom) ≫ (K).map e.inv = f := by
  rw [Category.assoc,← (K).map_comp,e.hom_inv_id,(K).map_id,Category.comp_id]

private theorem sentence_chart_cancel :
    sentenceIso.hom ≫ (K).map ArithmeticLiteralModel.sentenceChart.inv = literalSentence :=
  cancel_mapped_iso literalSentence ArithmeticLiteralModel.sentenceChart

private theorem map_chain
    {A B C : PredicateCategory 𝗣𝗔} {W X Z : NumericalTuples.Object}
    (i : W ⟶ X) {j : X ⟶ (K).obj A} {p : X ⟶ Z} {k : Z ⟶ (K).obj B}
    {l : Z ⟶ (K).obj C} {f : A ⟶ B} {g : B ⟶ C}
    (h : j ≫ (K).map f = p ≫ k) (c : k ≫ (K).map g = l) :
    (i ≫ j) ≫ (K).map (f ≫ g) = (i ≫ p) ≫ l := by
  rw [(K).map_comp,Category.assoc,← Category.assoc j,h,Category.assoc,c,← Category.assoc]

/-- This is the printed conclusion diagram on the actual literal
sentence object, rather than equality of ambient numerical predicates. -/
@[reassoc] theorem rho_conclusion (Γ : Carrier) :
    (rho Γ).hom ≫ (K).map (ArithmeticLiteralModel.conclusion Γ) =
      SentenceProofCodes.conclusion Γ ≫ literalSentence := by
  exact map_chain (SentenceProofCodes.pullbackIso Γ).inv
    (sentencePullback_conclusion Γ) sentence_chart_cancel

private theorem original_word_conclusion (Γ : Carrier) :
    (ProofWords.iso Γ).inv ≫ representedArrow 𝗣𝗔 (ProofWords.conclusion Γ) =
      ArithmeticLiteralModel.conclusion Γ := by
  have h := congrArg (fun f => (ProofWords.iso Γ).inv ≫ f) (ProofWords.iso_conclusion Γ)
  simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using h.symm

/-- Both carriers store original proof words. Their relation to chosen
pullback coordinates is proved by the two constructor-preserving comparisons. -/
def wordIso (Γ : Carrier) : SentenceProofCodes.object Γ ≅ ProofImage.proofObject Γ :=
  rho Γ ≪≫ (K).mapIso (ProofWords.iso Γ).symm

def conclusion (Γ : Carrier) : SentenceProofCodes.object Γ ⟶ ProofImage.sentenceObject :=
  SentenceProofCodes.conclusion Γ ≫ literalSentence

@[reassoc] theorem wordIso_conclusion (Γ : Carrier) :
    (wordIso Γ).hom ≫ ProofImage.conclusion Γ = conclusion Γ := by
  change ((rho Γ).hom ≫ (K).map (ProofWords.iso Γ).inv) ≫
    (K).map (representedArrow 𝗣𝗔 (ProofWords.conclusion Γ)) = _
  rw [Category.assoc,← (K).map_comp,original_word_conclusion,rho_conclusion]
  rfl

/-- The quotient has the fixed literal Prov_Gamma predicate as target.
Its domain is the actual numerical finite-derivation word carrier. -/
def quotient (Γ : Carrier) : SentenceProofCodes.object Γ ⟶ ProofImage.theoryObject Γ :=
  (wordIso Γ).hom ≫ ProofImage.quotient Γ

instance quotient_splitEpi (Γ : Carrier) : IsSplitEpi (quotient Γ) := by
  dsimp only [quotient]
  infer_instance

theorem factor (Γ : Carrier) : quotient Γ ≫ ProofImage.inclusion Γ = conclusion Γ := by
  rw [quotient,Category.assoc,ProofImage.factor,wordIso_conclusion]

private theorem iso_comp_strongEpi {A B C : NumericalTuples.Object}
    (e : A ≅ B) (q : B ⟶ C) [IsSplitEpi q] : StrongEpi (e.hom ≫ q) := by
  infer_instance

/-- The actual fixed theorem predicate is a categorical regular image,
with its literal inclusion, and not only an extensionally equal set. -/
def imageFactorisation (Γ : Carrier) : StrongEpiMonoFactorisation (conclusion Γ) where
  I := ProofImage.theoryObject Γ
  e := quotient Γ
  m := ProofImage.inclusion Γ
  fac := factor Γ
  e_strong_epi := iso_comp_strongEpi (wordIso Γ) (ProofImage.quotient Γ)

def isImage (Γ : Carrier) : IsImage (imageFactorisation Γ).toMonoFactorisation :=
  (imageFactorisation Γ).toMonoIsImage

/-- Both implications concern the actual fixed source program selected
from the constructed Gamma conclusion, with no comparison hypothesis. -/
theorem fixed_provability (Γ : Carrier) (s : NumericalTuples.Point ProofImage.sentenceObject) :
    (∃ p : NumericalTuples.Point (SentenceProofCodes.object Γ), (conclusion Γ).toFun p = s) ↔
      (ArithmeticLiteralModel.theoremPredicate Γ).val.Evalb (M := ℕ) ![s.val] := by
  rw [← ProofImage.image_membership Γ s]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨(wordIso Γ).hom.toFun p,
      ((congrArg (fun f => f.toFun p) (wordIso_conclusion Γ)).trans hp)⟩
  · rintro ⟨p,hp⟩
    refine ⟨(wordIso Γ).inv.toFun p,?_⟩
    have h := congrArg (fun f => f.toFun ((wordIso Γ).inv.toFun p)) (wordIso_conclusion Γ)
    have hi := congrArg (fun f => f.toFun p) (wordIso Γ).inv_hom_id
    exact h.symm.trans ((congrArg (ProofImage.conclusion Γ).toFun hi).trans hp)

/-- The underlying isomorphism reaches the canonical interpretation of
the earlier arithmetic source proof object in the total restriction splitting. -/
def canonicalRho (Γ : Carrier) : (U).obj (SentenceProofCodes.object Γ) ≅
    PredicateInterpretation.CanonicalDomain 𝗣𝗔 ℕ
      ((realization 𝗣𝗔).obj (ArithmeticLiteralModel.proofObject Γ)) :=
  (U).mapIso (rho Γ) ≪≫ canonicalComparison.app (ArithmeticLiteralModel.proofObject Γ)

/-- Computability is supplied in both directions on the actual proof
carriers. The programs may remain partial away from those carriers. -/
theorem canonical_forward_program (Γ : Carrier) :
    ∃ r : ℕ → Part ℕ, Partrec r ∧
      ∀ p : NumericalTuples.Point (SentenceProofCodes.object Γ),
        r p.val = Part.some ((canonicalRho Γ).hom p).val.val := by
  refine ⟨(rho Γ).hom.program,(rho Γ).hom.program_partrec,?_⟩
  intro p
  exact ((rho Γ).hom.program_apply p).trans
    (congrArg Part.some (canonicalComparison_value (ArithmeticLiteralModel.proofObject Γ)
      ((rho Γ).hom.toFun p)).symm)

theorem canonical_backward_program (Γ : Carrier) :
    ∃ r : ℕ → Part ℕ, Partrec r ∧
      ∀ p : PredicateInterpretation.CanonicalDomain 𝗣𝗔 ℕ
        ((realization 𝗣𝗔).obj (ArithmeticLiteralModel.proofObject Γ)),
        r p.val.val = Part.some ((canonicalRho Γ).inv p).val := by
  refine ⟨(rho Γ).inv.program,(rho Γ).inv.program_partrec,?_⟩
  intro p
  exact (congrArg (rho Γ).inv.program
    (canonicalComparison_inverse_value (ArithmeticLiteralModel.proofObject Γ) p).symm).trans
      ((rho Γ).inv.program_apply (canonicalComparison.inv.app _ p))

/-- The canonical source conclusion and the actual numerical conclusion
commute under the constructed proof-code isomorphism. -/
theorem canonical_conclusion (Γ : Carrier)
    (p : NumericalTuples.Point (SentenceProofCodes.object Γ)) :
    canonicalComparison.hom.app ArithmeticLiteralModel.sentencePredicate ((conclusion Γ).toFun p) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ))
        ((canonicalRho Γ).hom p) := by
  have hc := congrArg (fun f => f.toFun p) (rho_conclusion Γ)
  exact (congrArg (canonicalComparison.hom.app ArithmeticLiteralModel.sentencePredicate) hc).symm.trans
    (canonicalComparison_natural (ArithmeticLiteralModel.conclusion Γ) ((rho Γ).hom.toFun p))

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofComparison
