module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent
public import CategoricalEssentialIncompleteness.V46JaniczakSignedTheory
public import CategoricalEssentialIncompleteness.V46MillerFixedPoint
public import CategoricalEssentialIncompleteness.V46PrecompleteClasses
public import CategoricalEssentialIncompleteness.V46RelationalSignatureAdjunction
public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory
public import CategoricalEssentialIncompleteness.V46TrivialDominicalCategory

/-! Independent applications after the source verdict. Each example selects the native
objects, morphisms and quantifiers used in the reconstructed proposition. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.PCategoryStruct CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace IndependentReaderTwo

/-- The P-category operation gives every chosen binary restriction-product operation
and satisfies all of its equations at the induced restriction. -/
def productsOfPCategory (C : Type u) [Category.{v} C] [PCategoryStruct C] [PCategory C] :
    RestrictionProducts.ProductData C where
  prod := nearProd
  fst := p0
  snd := p1
  pair := partialPairing
  fst_total := PCategory.p0_isTotal
  snd_total := PCategory.p1_isTotal
  pair_fst := PCategory.p0_partialPairing
  pair_snd := PCategory.p1_partialPairing
  pair_restriction := PCategory.rst_partialPairing
  pair_proj := PCategory.partialPairing_proj

/-- Every pair of disjoint nonempty saturated numerical sets in a precomplete
relation is recursively inseparable, even without enumerations of those sets. -/
theorem numericalClasses {R : ℕ → ℕ → Prop} (ht : Precomplete R) {A B : Set ℕ}
    (ha : A.Nonempty) (hb : B.Nonempty) (hab : Disjoint A B)
    (sa : ∀ m n, R m n → n ∈ A → m ∈ A) (sb : ∀ m n, R m n → n ∈ B → m ∈ B) :
    Numerical.RecursivelyInseparable A B := ht.inseparable_unions ha hb hab sa sb

open Miller in
theorem simultaneousMillerPoint : ∃ a : ℕ → Set.Icc (0 : ℝ) 1,
    ∀ d : ℕ, ∀ r : Set.Icc (0 : ℝ) 1,
      (∀ p : ℕ → Fin 2, rho p = a → ∀ k : ℕ, ∃ j : ℕ,
        j ∈ OracleProgram.numberedEval d p k ∧ |(Rationals.q j : ℝ) - r| < ((2 : ℝ)^k)⁻¹) →
        a d = r := Miller.exists_isMiller

open CategoryTheory.CoprodStruct TrivialDominicalCategory in
theorem separatedInTheTrivialCategory : DiPaolaHeller.IsTuringMorphism evaluator ∧
    𝟙 One.obj = (0 : One.obj ⟶ One.obj) ∧
    ¬ Inseparable (Idem.pull (diag One.obj ≫ evaluator) (summand0 One.obj One.obj))
      (Idem.pull (diag One.obj ≫ evaluator) (summand1 One.obj One.obj)) :=
  ⟨evaluator_turing, identity_eq_zero, diagonal_pair_separated⟩

def signatureAdjunction : Voutsadakis.freeSignature.{u} ⊣ Voutsadakis.formulas.{u} :=
  Voutsadakis.signatureAdjunction

open FFL FFL.FirstOrder in
theorem numericalEquivalenceRelation (A B : Set ℕ) (hd : Disjoint A B)
    (ha : REPred (· ∈ A)) (hb : REPred (· ∈ B)) :
    Entailment.Consistent (Janiczak.FOL.theory (Janiczak.Signed A B)) ∧
    (Janiczak.FOL.EssentiallyUndecidable (Janiczak.FOL.theory (Janiczak.Signed A B)) ↔
      Numerical.RecursivelyInseparable A B) := by
  obtain ⟨hc, _, _, iff⟩ := Janiczak.FOL.signed_janiczak hd ha hb
  exact ⟨hc, iff⟩

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature

theorem oneMorphismForAllPresentations :
    ∃ q : ArithmeticIndexedAxioms.parameter ⟶ ArithmeticIndexedAxioms.sentence,
      ∀ e : ℕ, Entailment.Consistent (ArithmeticNamedProofConnectives.system
        (ArithmeticUniformIndependent.gamma e)) →
      ∃ φ : Formula, φ.freeVariables = [] ∧ formulaCode φ =
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
        ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
          (ArithmeticUniformIndependent.gamma e) φ ∧
        ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
          (ArithmeticUniformIndependent.gamma e) (.neg φ) := by
  obtain ⟨q, h⟩ := ArithmeticUniformIndependent.uniform_independent_sentences
  exact ⟨q, h⟩

#print axioms productsOfPCategory
#print axioms numericalClasses
#print axioms simultaneousMillerPoint
#print axioms separatedInTheTrivialCategory
#print axioms signatureAdjunction
#print axioms numericalEquivalenceRelation
#print axioms oneMorphismForAllPresentations

end IndependentReaderTwo
