/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonLists
import CategoricalEssentialIncompleteness.V46MillerSyntaxTotal
import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport

/-! # The explicitly presented named signature and its canonical push

The source signature is PA-described. Its words retain those labels.
The canonical realization is the actual pointPresentation push of this
constructed algebra, rather than a claim that a chosen inverse-equivalence
counit fixes word coordinates.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
variable (P : Uniform.Family)

section PolynomialEqualities
variable {D : Type*} [Category D] [HasFiniteLimits D] [HasFiniteCoproducts D]
variable {p q r s : SyntaxPolynomial D}

def castAlgebra (hp : p=r) (hq : q=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s) :=
  Eq.mp (congrArg (fun K => Endofunctor.Algebra K) (congrArg₂ SyntaxPolynomial.jointFunctor hp hq)) A

def castAlgebraInitial (hp : p=r) (hq : q=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (hA : IsInitial A) : IsInitial (castAlgebra hp hq A) := by
  cases hp
  cases hq
  exact hA

def castAlgebraStable (hp : p=r) (hq : q=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (hA : ∀ R,IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) :
    ∀ R,IsInitial (SyntaxPolynomial.algebraWithParameters r s (castAlgebra hp hq A) R) := by
  cases hp
  cases hq
  exact hA

theorem castAlgebra_carrier (hp : p=r) (hq : q=s) (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    (castAlgebra hp hq A).a=A.a := by
  cases hp
  cases hq
  rfl
end PolynomialEqualities

def normalizedWordAlgebraIso (a b : SyntacticSyntax.RawPolynomial)
    (p q : SyntaxPolynomial (Total.TotalCategory P))
    (hp : Syntax.Polynomial.mapped P a=p) (hq : Syntax.Polynomial.mapped P b=q) :
    Syntax.Raw.wordAlgebra p q ≅ castAlgebra hp hq
      (Syntax.Polynomial.mappedAlgebra P a b (SyntacticSyntax.plainPostfixAlgebra 𝗣𝗔 a b)) := by
  cases hp
  cases hq
  exact wordAlgebraIso P a b


section Signature
variable (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "a" => SyntaxPolynomial.termExpression V σ d
local notation "b" => SyntaxPolynomial.formulaExpression V π d
local notation "p" => SyntaxPolynomial.termExpression (Functor.obj (Syntax.predicateFunctor P) V)
  (fun n => Functor.obj (Syntax.predicateFunctor P) (σ n)) d
local notation "q" => SyntaxPolynomial.formulaExpression (Functor.obj (Syntax.predicateFunctor P) V)
  (fun n => Functor.obj (Syntax.predicateFunctor P) (π n)) d

def sourceSyntax : CategoricalSyntax V σ π d := SyntacticSyntax.plainCategoricalSyntax 𝗣𝗔 V σ π d

theorem termExpression_mapped : Syntax.Polynomial.mapped P a=p :=
  SyntaxOperationsTransport.mapCoefficients_termExpression (Syntax.predicateFunctor P).obj V σ d

theorem formulaExpression_mapped : Syntax.Polynomial.mapped P b=q :=
  SyntaxOperationsTransport.mapCoefficients_formulaExpression (Syntax.predicateFunctor P).obj V π d

/-- The exact named word algebra, with the list image whose initiality
was proved by its constructor comparison with the direct list algebra. -/
def presentedSyntax : CategoricalSyntax ((F).obj V)
    (fun n => (F).obj (σ n)) (fun n => (F).obj (π n)) d where
  decidableVariables := Derivation.mappedEquality (F) (sourceSyntax V σ π d).decidableVariables
  algebra := Syntax.Raw.wordAlgebra p q
  initial := Syntax.Raw.wordInitial p q
  stable R := Syntax.Raw.wordWithParametersInitial R p q
  lists := mappedListStable P V

def sourceMappedAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q) :=
  castAlgebra (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)
    (Syntax.Polynomial.mappedAlgebra P a b (sourceSyntax V σ π d).algebra)


def sourceAlgebraIso : (presentedSyntax P V σ π d).algebra ≅ sourceMappedAlgebra P V σ π d :=
  normalizedWordAlgebraIso P a b p q (termExpression_mapped P V σ d) (formulaExpression_mapped P V π d)

end Signature

section Push
variable {Q : Uniform.Family} {D : Type*} [Category D] [Regular D] [FinitaryExtensive D]
variable (E : Total.TotalCategory Q ≌ D) (p q : SyntaxPolynomial (Total.TotalCategory Q))

/-- Actual polynomial transport through an equivalence, starting from
the supplied constructed source algebra, with only mapCoefficients-id
normalizations at its source. -/
def pushedData (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (hA : IsInitial A) (hs : ∀ R,IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) :
    Σ B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients E.functor.obj) (q.mapCoefficients E.functor.obj)),
      IsInitial B × (∀ R,IsInitial (SyntaxPolynomial.algebraWithParameters
        (p.mapCoefficients E.functor.obj) (q.mapCoefficients E.functor.obj) B R)) := by
  let A' := castAlgebra (SyntacticSyntax.mapCoefficients_id p).symm
    (SyntacticSyntax.mapCoefficients_id q).symm A
  have hi := castAlgebraInitial (SyntacticSyntax.mapCoefficients_id p).symm
    (SyntacticSyntax.mapCoefficients_id q).symm A hA
  have hp := castAlgebraStable (SyntacticSyntax.mapCoefficients_id p).symm
    (SyntacticSyntax.mapCoefficients_id q).symm A hs
  exact ⟨SyntacticSyntax.Transport.mappedAlgebra E id E.functor.obj (fun X => Iso.refl _) p q A',
    SyntaxPolynomialTransport.initial E id E.functor.obj (fun X => Iso.refl _) p q A' hi,
    SyntacticSyntax.Transport.mappedStable E id E.functor.obj (fun X => Iso.refl _) p q A' hp⟩

end Push

/-- The canonical syntax is an explicit push of the PA-labelled uniform
syntax. No inverse-equivalence word-identity assertion is used. -/
def canonicalPresentedSyntax (z : Point) (V : PredicateCategory 𝗣𝗔)
    (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ) :
    CategoricalSyntax ((Total.pointPresentation z).functor.obj
      ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj V))
      (fun n => (Total.pointPresentation z).functor.obj
        ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj (σ n)))
      (fun n => (Total.pointPresentation z).functor.obj
        ((Syntax.predicateFunctor (Uniform.Family.ofPoint z)).obj (π n))) d := by
  let P := Uniform.Family.ofPoint z
  let E := Total.pointPresentation z
  let S := presentedSyntax P V σ π d
  let p := SyntaxPolynomial.termExpression ((Syntax.predicateFunctor P).obj V)
    (fun n => (Syntax.predicateFunctor P).obj (σ n)) d
  let q := SyntaxPolynomial.formulaExpression ((Syntax.predicateFunctor P).obj V)
    (fun n => (Syntax.predicateFunctor P).obj (π n)) d
  let D := pushedData E p q S.algebra S.initial S.stable
  have hp := SyntaxOperationsTransport.mapCoefficients_termExpression E.functor.obj
    ((Syntax.predicateFunctor P).obj V) (fun n => (Syntax.predicateFunctor P).obj (σ n)) d
  have hq := SyntaxOperationsTransport.mapCoefficients_formulaExpression E.functor.obj
    ((Syntax.predicateFunctor P).obj V) (fun n => (Syntax.predicateFunctor P).obj (π n)) d
  exact {
    decidableVariables := DecidableVariables.Transport.mapped E S.decidableVariables _ (Iso.refl _)
    algebra := castAlgebra hp hq D.1
    initial := castAlgebraInitial hp hq D.1 D.2.1
    stable := castAlgebraStable hp hq D.1 D.2.2
    lists := SyntacticLists.Transport.mappedStableListAlgebra E _ _ (Iso.refl _) S.lists }

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison
