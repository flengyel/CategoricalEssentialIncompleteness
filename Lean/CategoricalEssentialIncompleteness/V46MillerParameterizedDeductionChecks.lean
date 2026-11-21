/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46MillerParameterizedDeduction

/-! # Independent checks of the complete Lemma 9.6 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46 Miller ParameterizedDeduction

example (z : Point) : (numbers z).obj.base = Uniform.N (Uniform.Family.ofPoint z) := rfl

example (z : Point) : (numbers z).obj.domain.hom =
    𝟙 (Uniform.N (Uniform.Family.ofPoint z)) := numbers_domain z

/-- Arbitrary nullary labels, the numerical variable object, and all bounded signatures
occur before every parameter and axiom subobject. -/
example (z : Point) :
    (∀ X : Total.CanonicalTotal z,
      Nonempty (CategoricalSyntax (numbers z) (fun _ => ⊥_ (Total.CanonicalTotal z))
        (fun _ => X) 0)) ∧
    (∀ (X P : Total.CanonicalTotal z)
      (A : Subobject (P ⨯ (nullarySyntax z X).sentenceObject)),
      ∃ B : Endofunctor.Algebra (printedRules z (nullarySyntax z X) P A).inference,
        Nonempty (IsInitial B)) ∧
    (∀ (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ)
      (P : Total.CanonicalTotal z)
      (A : Subobject (P ⨯ (Syntax.canonicalCategoricalSyntax z V σ π d).sentenceObject)),
      ∃ B : Endofunctor.Algebra
        (printedRules z (Syntax.canonicalCategoricalSyntax z V σ π d) P A).inference,
        Nonempty (IsInitial B)) :=
  ⟨fun X => ⟨nullarySyntax z X⟩,
    fun X P A => ⟨printedAlgebra z (nullarySyntax z X) P A,
      ⟨printedInitial z (nullarySyntax z X) P A⟩⟩,
    fun V σ π d P A =>
      ⟨printedAlgebra z (Syntax.canonicalCategoricalSyntax z V σ π d) P A,
        ⟨printedInitial z (Syntax.canonicalCategoricalSyntax z V σ π d) P A⟩⟩⟩

example (z : Point) : Conclusions z := printedStatement z

section Nullary
variable (z : Point) (X P : Total.CanonicalTotal z)
local notation "S" => nullarySyntax z X

example : IsInitial (S).algebra := (S).initial

example : IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression (numbers z) (fun _ => ⊥_ (Total.CanonicalTotal z)) 0)
    (SyntaxPolynomial.formulaExpression (numbers z) (fun _ => X) 0) (S).algebra P) :=
  (S).stable P

example : StableListAlgebra (numbers z) := (S).lists

example : IsInitial (((S).lists.algebra.withParameters P).asAlgebra) := (S).lists.stable P

example (A : Subobject (S).sentenceObject) : IsInitial ((nullaryPresentations z).proofs X A) :=
  (nullaryPresentations z).initial X A
end Nullary

section Signatures
variable (z : Point) (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ)
variable (P : Total.CanonicalTotal z)
local notation "S" => Syntax.canonicalCategoricalSyntax z V σ π d
local instance : Regular (Over P) := RegularSlices.regular P
local instance : FinitaryExtensive (Over P) := RegularSlices.finitaryExtensive P
local instance : PreservesFiniteLimits (constantFamilyFunctor P) :=
  SliceBaseChangeGeometry.constant_preservesFiniteLimits P

example : IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
    (S).algebra P) := (S).stable P

example (A : Subobject ((constantFamilyFunctor P).obj (S).sentenceObject)) :
    IsInitial (proofs z (S) P A) := initial z (S) P A

/-- These axiom subobjects are arbitrary subobjects of the literal product. -/
example (A : Subobject (P ⨯ (S).sentenceObject)) :
    (axiomArrow z (S) P A).left = A.arrow := rfl

example (A : Subobject (P ⨯ (S).sentenceObject)) : Mono (axiomArrow z (S) P A) :=
  inferInstance

example (A : Subobject (P ⨯ (S).sentenceObject)) :
    RulePresentation (P ⨯ (S).algebra.a.2) 2 := printedRules z (S) P A

example (A : Subobject (P ⨯ (S).sentenceObject)) :
    Over (P ⨯ (S).algebra.a.2) := (printedAlgebra z (S) P A).a

example (A : Subobject (P ⨯ (S).sentenceObject)) :
    IsInitial (printedAlgebra z (S) P A) := printedInitial z (S) P A

/-- Every rule conclusion has exactly the parameter of its rule instance. -/
example (A : Subobject (P ⨯ (S).sentenceObject)) (i : Fin 3) :
    (printedRules z (S) P A).conclusion i ≫ (prod.fst : P ⨯ (S).algebra.a.2 ⟶ P) =
      ((rules z (S) P (axiomArrow z (S) P A)).instances i).hom :=
  Over.w ((rules z (S) P (axiomArrow z (S) P A)).conclusion i)

example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules z (S) P A).inference) :
    ∃! _f : printedAlgebra z (S) P A ⟶ B, True :=
  ⟨printedFold z (S) P A B, trivial, fun f _ => printedFold_unique z (S) P A B f⟩

example (A : Subobject (P ⨯ (S).sentenceObject))
    (B : Endofunctor.Algebra (printedRules z (S) P A).inference) :
    (printedFold z (S) P A B).f.left ≫ B.a.hom = (printedAlgebra z (S) P A).a.hom ∧
    (printedAlgebra z (S) P A).str ≫ (printedFold z (S) P A B).f =
      (printedRules z (S) P A).inference.map (printedFold z (S) P A B).f ≫ B.str :=
  ⟨printedFold_conclusion z (S) P A B, printedFold_constructor z (S) P A B⟩
end Signatures

#print axioms ParameterizedDeduction.numbers
#print axioms ParameterizedDeduction.nullaryPresentations
#print axioms ParameterizedDeduction.proofs
#print axioms ParameterizedDeduction.initial
#print axioms ParameterizedDeduction.axiomArrow_mono
#print axioms ParameterizedDeduction.printedAlgebra
#print axioms ParameterizedDeduction.printedInitial
#print axioms ParameterizedDeduction.printedFold_conclusion
#print axioms ParameterizedDeduction.printedFold_constructor
#print axioms ParameterizedDeduction.printedFold_unique
#print axioms ParameterizedDeduction.printedStatement

#print axioms ParameterizedDeduction.numbers_source_full
#print axioms ParameterizedDeduction.numbers_domain
