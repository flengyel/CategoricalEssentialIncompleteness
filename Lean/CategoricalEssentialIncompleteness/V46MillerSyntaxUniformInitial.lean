/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxUniformInitialExplicit
public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawConstantComparison
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxTerminal
public import CategoricalEssentialIncompleteness.V46MillerTotalRegular

/-! # Parameter-stable initiality of the literal uniform syntax algebra

The canonical parameter algebra is compared with the actual explicit
parameter-word algebra by constructor-preserving isomorphisms. The carrier
is the guarded literal word; witnesses remain in its membership predicate.
No target operation is required to have an ordinary recursive extension.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding
variable {P : Uniform.Family}
variable (R : Total.TotalCategory P) (p q : SyntaxPolynomial (Total.TotalCategory P))

theorem parameterConstructor_lift (formula : Bool) :
    (liftIso R (wordObject false p q) (wordObject true p q) (if formula then q else p)).hom ≫
      parameterConstructor R p q formula = explicitFamilyMap R (rawWordConstructor p q formula) := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  let Q := if formula then q else p
  let r := (Nat.unpair n).1
  let u := (Nat.unpair n).2
  have hl := liftIso_value R (wordObject false p q) (wordObject true p q) Q n hn
  have hp : fiber R (uniformWordFamily R false p q) (uniformWordFamily R true p q)
      Q (r,constantLift Q r u) :=
    constantLift_supported R (wordObject false p q) (wordObject true p q) Q hn.1 hn.2
  have hc := (parameterConstructor_graph R p q formula r (constantLift Q r u)
    (Nat.pair r (constructor formula (skeleton Q) u))).mpr
      ⟨hp,by rw [constantUnlift_lift]⟩
  have hr := (explicitFamilyMap_graph R (rawWordConstructor p q formula) r u
    (Nat.pair r (constructor formula (skeleton Q) u))).mpr
      ⟨hn.1,_,(rawWordConstructor_graph p q formula u _).mpr ⟨hn.2,rfl⟩,rfl⟩
  change Total.val ((liftIso R (wordObject false p q) (wordObject true p q) Q).hom.left.hom ≫
    (parameterConstructor R p q formula).left.hom) n =
      Total.val (explicitFamilyMap R (rawWordConstructor p q formula)).left.hom n
  rw [Total.val_comp,hl,Part.bind_some]
  exact (Part.eq_some_iff.mpr hc).trans
    (Part.eq_some_iff.mpr (by simpa only [r,u,Nat.pair_unpair] using hr)).symm

theorem parameterPolynomial_constructor (formula : Bool) :
    constantPolynomialLeft R (wordObject false p q) (wordObject true p q)
      (if formula then q else p) ≫ (constantFamilyFunctor R).map
        ((baseComparison (wordObject false p q) (wordObject true p q)
          (if formula then q else p)).inv ≫ rawWordConstructor p q formula) =
      (liftIso R (wordObject false p q) (wordObject true p q)
        (if formula then q else p)).hom ≫ parameterConstructor R p q formula ≫
          (explicitFamilyIso R (wordObject formula p q)).hom := by
  rw [constantPolynomialSquare]
  unfold constantPolynomialRight
  rw [Category.assoc,← CategoryTheory.Functor.map_comp]
  simp only [Iso.hom_inv_id_assoc]
  rw [← explicitFamilyMap_natural,← parameterConstructor_lift]
  simp only [Category.assoc]

def parameterWordPairIso : (parameterWordAlgebra R p q).a ≅
    (SyntaxPolynomial.algebraWithParameters p q (wordAlgebra p q) R).a where
  hom := ((explicitFamilyIso R (wordObject false p q)).hom,
    (explicitFamilyIso R (wordObject true p q)).hom)
  inv := ((explicitFamilyIso R (wordObject false p q)).inv,
    (explicitFamilyIso R (wordObject true p q)).inv)
  hom_inv_id := Prod.ext (explicitFamilyIso R (wordObject false p q)).hom_inv_id
    (explicitFamilyIso R (wordObject true p q)).hom_inv_id
  inv_hom_id := Prod.ext (explicitFamilyIso R (wordObject false p q)).inv_hom_id
    (explicitFamilyIso R (wordObject true p q)).inv_hom_id

def parameterWordAlgebraIso : parameterWordAlgebra R p q ≅
    SyntaxPolynomial.algebraWithParameters p q (wordAlgebra p q) R := by
  refine Endofunctor.Algebra.isoMk (parameterWordPairIso R p q) ?_
  apply Prod.ext
  · apply (cancel_epi ((liftIso R (wordObject false p q) (wordObject true p q) p).hom ≫
      (comparison R (uniformWordFamily R false p q) (uniformWordFamily R true p q) p).hom)).1
    have he := parameterPolynomial_constructor R p q false
    rw [constantPolynomialLeft_direct] at he
    simpa [SyntaxPolynomial.jointFunctor,CategoryTheory.Functor.prod',wordFamily_constant,
      SyntaxPolynomial.algebraWithParameters,parameterWordPairIso,parameterWordAlgebra,
      wordAlgebra,Category.assoc,Iso.hom_inv_id_assoc] using he
  · apply (cancel_epi ((liftIso R (wordObject false p q) (wordObject true p q) q).hom ≫
      (comparison R (uniformWordFamily R false p q) (uniformWordFamily R true p q) q).hom)).1
    have he := parameterPolynomial_constructor R p q true
    rw [constantPolynomialLeft_direct] at he
    simpa [SyntaxPolynomial.jointFunctor,CategoryTheory.Functor.prod',wordFamily_constant,
      SyntaxPolynomial.algebraWithParameters,parameterWordPairIso,parameterWordAlgebra,
      wordAlgebra,Category.assoc,Iso.hom_inv_id_assoc] using he

/-- Every parameter object and every algebra on arbitrary families over it. -/
def wordWithParametersInitial :
    IsInitial (SyntaxPolynomial.algebraWithParameters p q (wordAlgebra p q) R) :=
  (explicitWordInitial R p q).ofIso (parameterWordAlgebraIso R p q)

/-- The actual base algebra, obtained through the proved terminal comparison. -/
def wordInitial (p q : SyntaxPolynomial (Total.TotalCategory P)) : IsInitial (wordAlgebra p q) :=
  SyntacticSyntax.initialOfTerminalParameters p q (wordAlgebra p q)
    (wordWithParametersInitial (⊤_ (Total.TotalCategory P)) p q)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
