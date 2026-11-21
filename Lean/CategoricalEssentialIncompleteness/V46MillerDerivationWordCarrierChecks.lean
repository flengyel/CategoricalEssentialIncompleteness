/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordCarrier


/-! # Successful derivations carried by their original word alone -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open SyntacticDerivation
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example (word : ℕ) : word∈(Derivation.successfulWordObject R).obj.support ↔
    ∃ proofCode,word∈Total.val (Derivation.treeInclusion R).hom proofCode :=
  Derivation.successfulWord_mem R word
example (word formula : ℕ) : formula∈Total.val (Derivation.wordConclusion R).hom word ↔
    ∃ proofCode,word∈Total.val (Derivation.treeInclusion R).hom proofCode ∧
      formula∈Total.val (Derivation.conclusion R).hom proofCode := Derivation.wordConclusion_graph R word formula
example (word : ℕ) : word∈(Derivation.successfulWordObject R).obj.support ↔
    ∃ formula output,output∈Total.val (Derivation.validatorFold R).f.hom word ∧
      output∈Total.val (coprod.inr : F ⟶ OptionSyntax.obj F).hom formula :=
  Derivation.successfulWord_validated R word
example : Derivation.wordAlgebra R ≅ Derivation.derivationAlgebra R := Derivation.wordAlgebraIso R
example : IsInitial (Derivation.wordAlgebra R) := Derivation.wordInitial R
example : (Derivation.wordAlgebra R).str.left ≫ Derivation.wordInclusion R=
    Derivation.wordInputChart R ≫ Syntax.Raw.rawWordConstructor (Derivation.treePolynomial R) .unit false :=
  Derivation.word_constructor_code R
example (input u word : ℕ) (hu : u∈Total.val (Derivation.wordInputChart R).hom input)
    (hw : word∈Total.val (Derivation.wordAlgebra R).str.left.hom input) :
    word=SyntacticSyntax.Coding.constructor false (Syntax.Raw.skeleton (Derivation.treePolynomial R)) u :=
  Derivation.word_constructor_value R input u word hu hw
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.wordFold R B).f.left ≫ B.a.hom=Derivation.wordConclusion R := Derivation.wordFold_conclusion R B
example (B : Endofunctor.Algebra R.inference) :
    (Derivation.wordAlgebra R).str ≫ (Derivation.wordFold R B).f=
      R.inference.map (Derivation.wordFold R B).f ≫ B.str := Derivation.wordFold_constructor R B
example (B : Endofunctor.Algebra R.inference) (f : Derivation.wordAlgebra R ⟶ B) :
    f=Derivation.wordFold R B := Derivation.wordFold_unique R B f
example (B : Endofunctor.Algebra R.inference) (f : Derivation.successfulWordObject R ⟶ B.a.left)
    (hf : f ≫ B.a.hom=Derivation.wordConclusion R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str=
      (Derivation.wordAlgebra R).str ≫ Over.homMk f hf) :
    f=(Derivation.wordFold R B).f.left := Derivation.wordFold_underlying_unique R B f hf hc
example (i : Fin (N+1)) : Derivation.wordConstructor R i ≫ Derivation.wordConclusion R=
    R.ruleConclusion (Derivation.wordAlgebra R).a i := Derivation.wordConstructor_conclusion R i
example : Derivation.wordNullary R ≫ Derivation.wordConclusion R=R.conclusion 0 :=
  Derivation.wordNullary_conclusion R
