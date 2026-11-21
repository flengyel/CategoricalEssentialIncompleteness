/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRawBase
public import CategoricalEssentialIncompleteness.V46MillerSyntaxCarrierConstructors

/-! # The literal uniform-word algebra with arbitrary coefficient objects

The carrier is the constructed guarded postfix word predicate. Its constructors append
the original root record, using the base polynomial comparison. No initiality or fold
law is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
variable {P : Uniform.Family}

def wordObject (formula : Bool) (p q : SyntaxPolynomial (Total.TotalCategory P)) : Total.TotalCategory P :=
  ⟨uniformWords formula p q⟩

def rawWordConstructor (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) :
    (⟨carrier (uniformWords false p q) (uniformWords true p q)
      (if formula then q else p)⟩ : Total.TotalCategory P) ⟶ wordObject formula p q :=
  ⟨Total.totalFromFunction (constructor formula (skeleton (if formula then q else p)))
      (NatVectors.constructor_primrec formula (skeleton (if formula then q else p))).to_comp
      (fun _u hu => uniformWords_constructor p q formula hu),
    Total.totalFromFunction_total _ _ _⟩

theorem rawWordConstructor_graph (p q : SyntaxPolynomial (Total.TotalCategory P)) (formula : Bool) (u word : ℕ) :
    word ∈ Total.val (rawWordConstructor p q formula).hom u ↔
      u ∈ (carrier (uniformWords false p q) (uniformWords true p q)
        (if formula then q else p)).support ∧
      word=constructor formula (skeleton (if formula then q else p)) u :=
  Total.mem_totalFromFunction (constructor formula (skeleton (if formula then q else p)))
    (NatVectors.constructor_primrec formula (skeleton (if formula then q else p))).to_comp
    (fun _u hu => uniformWords_constructor p q formula hu) u word

def wordAlgebra (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q) where
  a := (wordObject false p q,wordObject true p q)
  str := ((baseComparison (wordObject false p q) (wordObject true p q) p).inv ≫ rawWordConstructor p q false,
    (baseComparison (wordObject false p q) (wordObject true p q) q).inv ≫ rawWordConstructor p q true)

/-- This is the constructor diagram on the original numerical raw input,
not a claim deduced from evaluator uniqueness. -/
theorem wordAlgebra_term_constructor (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison (wordObject false p q) (wordObject true p q) p).hom ≫ (wordAlgebra p q).str.1=
      rawWordConstructor p q false := by
  simp only [wordAlgebra,Iso.hom_inv_id_assoc]

theorem wordAlgebra_formula_constructor (p q : SyntaxPolynomial (Total.TotalCategory P)) :
    (baseComparison (wordObject false p q) (wordObject true p q) q).hom ≫ (wordAlgebra p q).str.2=
      rawWordConstructor p q true := by
  simp only [wordAlgebra,Iso.hom_inv_id_assoc]

theorem wordAlgebra_mapped_term_support (a b : SyntacticSyntax.RawPolynomial) :
    (wordAlgebra (a.mapCoefficients (predicateFunctor P).obj)
      (b.mapCoefficients (predicateFunctor P).obj)).a.1.obj.support=(words P false a b).support :=
  uniformWords_mapped_support a b false

theorem wordAlgebra_mapped_formula_support (a b : SyntacticSyntax.RawPolynomial) :
    (wordAlgebra (a.mapCoefficients (predicateFunctor P).obj)
      (b.mapCoefficients (predicateFunctor P).obj)).a.2.obj.support=(words P true a b).support :=
  uniformWords_mapped_support a b true

theorem wordAlgebra_mapped_constructor (a : SyntacticSyntax.RawPolynomial) (formula : Bool) (u : ℕ) :
    constructor formula (skeleton (a.mapCoefficients (predicateFunctor P).obj)) u=
      constructor formula a u := by
  rw [skeleton_mapped]
  exact NumericalDerivationInterpretation.Parser.constructor_map (fun _ => Coding.zeroCarrier) a formula u

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
