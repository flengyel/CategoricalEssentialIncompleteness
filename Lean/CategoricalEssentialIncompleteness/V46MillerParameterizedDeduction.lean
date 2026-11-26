/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerSliceDerivations
public import CategoricalEssentialIncompleteness.V46NullaryPresentationAdjunction
public import CategoricalEssentialIncompleteness.V46FirstOrderRuleTransport
public import CategoricalEssentialIncompleteness.V46SliceBaseChangeGeometry

/-! # Lemma 9.6: arbitrary Miller coefficients and parameterized deduction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.ParameterizedDeduction
variable (z : Point)

/-- The full numerical variable carrier, in the total splitting. -/
def numbers : Total.CanonicalTotal z :=
  (Total.pointPresentation z).functor.obj (Derivation.numbers (P := Uniform.Family.ofPoint z))

theorem numbers_source_full :
    (Derivation.numbers (P := Uniform.Family.ofPoint z)).obj.support = Set.univ := by
  ext n
  exact (Syntax.Raw.mapped_coefficient_support Syntax.Raw.topCarrier n).trans
    (by simp [Syntax.Raw.topCarrier])

/-- The numerical variable object has the full identity domain, rather
than a proper semidecidable subset of the natural numbers. -/
theorem numbers_domain : (numbers z).obj.domain.hom =
    𝟙 (Uniform.N (Uniform.Family.ofPoint z)) := by
  change (Uniform.setIdem (Uniform.N (Uniform.Family.ofPoint z))
    (Derivation.numbers (P := Uniform.Family.ofPoint z)).obj.support
    (Derivation.numbers (P := Uniform.Family.ofPoint z)).obj.enumerable).hom = _
  apply Uniform.hom_ext_mem
  intro x y
  change y ∈ (Uniform.identityOn (Uniform.N (Uniform.Family.ofPoint z))
    (Derivation.numbers (P := Uniform.Family.ofPoint z)).obj.support
    (Derivation.numbers (P := Uniform.Family.ofPoint z)).obj.enumerable).val x ↔
    y ∈ Part.some x
  rw [Uniform.mem_identityOn, numbers_source_full]
  simp only [Set.mem_univ, true_and, Part.mem_some_iff]

/-- Every coefficient object is allowed, including nonrecursive and empty
uniformly semidecidable carriers. Initiality is indexed only by axiom subobjects. -/
def nullaryPresentations : NullaryPresentations (numbers z) where
  syntaxData X := Syntax.canonicalCategoricalSyntax z (numbers z)
    (fun _ => ⊥_ (Total.CanonicalTotal z)) (fun _ => X) 0
  proofs X A := Derivation.Canonical.derivationAlgebra z
    ((Syntax.canonicalCategoricalSyntax z (numbers z)
      (fun _ => ⊥_ (Total.CanonicalTotal z)) (fun _ => X) 0).logicalRules A.arrow)
  initial X A := Derivation.Canonical.derivationInitial z
    ((Syntax.canonicalCategoricalSyntax z (numbers z)
      (fun _ => ⊥_ (Total.CanonicalTotal z)) (fun _ => X) 0).logicalRules A.arrow)

abbrev nullarySyntax (X : Total.CanonicalTotal z) := (nullaryPresentations z).syntaxData X

section Signature
variable {V : Total.CanonicalTotal z} {σ π : ℕ → Total.CanonicalTotal z} {d : ℕ}
variable (S : CategoricalSyntax V σ π d) (P : Total.CanonicalTotal z)
local instance : Regular (Over P) := RegularSlices.regular P
local instance : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

/-- These are the logical, generalization and ordered modus-ponens rules in the parameter
slice, with arbitrary parameter-dependent axioms. -/
def rules {A : Over P} (axioms : A ⟶ (constantFamilyFunctor P).obj S.sentenceObject) :=
  firstOrderRules ((constantFamilyFunctor P).map S.logicalAxioms)
    ((constantFamilyFunctor P).map S.sentenceInclusion) axioms
    (FirstOrderRuleTransport.mappedAll (constantFamilyFunctor P) S.quantifierConstructor)
    (FirstOrderRuleTransport.mappedImp (constantFamilyFunctor P) S.implicationConstructor)

def proofs (A : Subobject ((constantFamilyFunctor P).obj S.sentenceObject)) :
    Endofunctor.Algebra (rules z S P A.arrow).inference :=
  Derivation.Parameterized.algebra z (rules z S P A.arrow)

def initial (A : Subobject ((constantFamilyFunctor P).obj S.sentenceObject)) :
    IsInitial (proofs z S P A) := Derivation.Parameterized.initial z (rules z S P A.arrow)

/-- Every axiom subobject of P × S acquires its canonical projection to P;
no constancy or recursive presentation of that subobject is required. -/
def axiomArrow (A : Subobject (P ⨯ S.sentenceObject)) :
    Over.mk (A.arrow ≫ (prod.fst : P ⨯ S.sentenceObject ⟶ P)) ⟶
      (constantFamilyFunctor P).obj S.sentenceObject := Over.homMk A.arrow rfl

instance axiomArrow_mono (A : Subobject (P ⨯ S.sentenceObject)) : Mono (axiomArrow z S P A) :=
  by
    dsimp only [axiomArrow]
    infer_instance

/-- The inference functor acts on the literal category D_a/(P × Fm).
Its ordered-premise comparisons enforce agreement of every parameter. -/
def printedRules (A : Subobject (P ⨯ S.sentenceObject)) :
    RulePresentation (P ⨯ S.algebra.a.2) 2 :=
  SliceRuleObjects.rules (rules z S P (axiomArrow z S P A))

def printedAlgebra (A : Subobject (P ⨯ S.sentenceObject)) :
    Endofunctor.Algebra (printedRules z S P A).inference :=
  Derivation.Canonical.derivationAlgebra z (printedRules z S P A)

def printedInitial (A : Subobject (P ⨯ S.sentenceObject)) :
    IsInitial (printedAlgebra z S P A) :=
  Derivation.Canonical.derivationInitial z (printedRules z S P A)

def printedFold (A : Subobject (P ⨯ S.sentenceObject))
    (B : Endofunctor.Algebra (printedRules z S P A).inference) : printedAlgebra z S P A ⟶ B :=
  (printedInitial z S P A).to B

theorem printedFold_conclusion (A : Subobject (P ⨯ S.sentenceObject))
    (B : Endofunctor.Algebra (printedRules z S P A).inference) :
    (printedFold z S P A B).f.left ≫ B.a.hom = (printedAlgebra z S P A).a.hom := Over.w _

theorem printedFold_constructor (A : Subobject (P ⨯ S.sentenceObject))
    (B : Endofunctor.Algebra (printedRules z S P A).inference) :
    (printedAlgebra z S P A).str ≫ (printedFold z S P A B).f =
      (printedRules z S P A).inference.map (printedFold z S P A B).f ≫ B.str :=
  (printedFold z S P A B).h.symm

theorem printedFold_unique (A : Subobject (P ⨯ S.sentenceObject))
    (B : Endofunctor.Algebra (printedRules z S P A).inference)
    (f : printedAlgebra z S P A ⟶ B) : f = printedFold z S P A B :=
  (printedInitial z S P A).hom_ext _ _

end Signature

/-- Every coefficient object may specify propositional atoms. The construction
gives their first-order syntax and supplies parameterized deduction for all
bounded finite signatures, including signatures with nonrecursive coefficients. -/
structure Conclusions where
  nullary : NullaryPresentations (numbers z)
  parameterized : ∀ (X P : Total.CanonicalTotal z)
    (A : Subobject (P ⨯ (nullarySyntax z X).sentenceObject)),
    Σ B : Endofunctor.Algebra (printedRules z (nullarySyntax z X) P A).inference, IsInitial B
  signatures : ∀ (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ)
    (P : Total.CanonicalTotal z)
    (A : Subobject (P ⨯ (Syntax.canonicalCategoricalSyntax z V σ π d).sentenceObject)),
    Σ B : Endofunctor.Algebra
      (printedRules z (Syntax.canonicalCategoricalSyntax z V σ π d) P A).inference, IsInitial B

/-- Lemma 9.6 has no supplied evaluator, initiality or coherence hypothesis. -/
def printedStatement : Conclusions z where
  nullary := nullaryPresentations z
  parameterized X P A :=
    ⟨printedAlgebra z (nullarySyntax z X) P A, printedInitial z (nullarySyntax z X) P A⟩
  signatures V σ π d P A :=
    ⟨printedAlgebra z (Syntax.canonicalCategoricalSyntax z V σ π d) P A,
      printedInitial z (Syntax.canonicalCategoricalSyntax z V σ π d) P A⟩

end CategoricalEssentialIncompleteness.V46.Miller.ParameterizedDeduction
