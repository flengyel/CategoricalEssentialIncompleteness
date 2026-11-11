/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryTermSubstitution
public import CategoricalEssentialIncompleteness.V46NullarySyntaxOccurrences
public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsent

/-! # The substitution comparison algebra in the parameter slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryInterpretation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)

def substitutionCarrierMap : S.substitutionCarriers ⟶ Q.substitutionCarriers :=
  (prod.map (interpretation S Q f).1 (interpretation S Q f).1,
    prod.map (interpretation S Q f).2 (OptionSyntax.map (interpretation S Q f).2))

def targetVariablePair : S.substitutionParameters ⨯ V ⟶ Q.substitutionCarriers.1 :=
  prod.map (substitutionParameterMap S Q f) (𝟙 V) ≫ Q.variableSubstitutionPair

def targetAtomPair : X ⟶ Q.substitutionCarriers.2 :=
  prod.lift (f ≫ Q.sentenceInclusion) (f ≫ Q.sentenceInclusion ≫ coprod.inr)

def targetQuantifierPair : S.substitutionParameters ⨯ (V ⨯ Q.substitutionCarriers.2) ⟶
    Q.substitutionCarriers.2 :=
  prod.map (substitutionParameterMap S Q f) (𝟙 _) ≫ Q.quantifierSubstitutionPair

def targetSubstitutionAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    ((SyntaxPolynomial.termExpression V (fun _ => ⊥_ D) 0).withParameters
      S.substitutionParameters)
    ((SyntaxPolynomial.formulaExpression V (fun _ => X) 0).withParameters
      S.substitutionParameters)) where
  a := (constantFamily S.substitutionParameters Q.substitutionCarriers.1,
    constantFamily S.substitutionParameters Q.substitutionCarriers.2)
  str := (
    coprod.desc (parameterHom (targetVariablePair S Q f))
      (prod.fst ≫ (NullarySyntaxAlgebra.constantInitial S.substitutionParameters).to _),
    coprod.desc
      (coprod.desc
        (coprod.desc
          (coprod.desc
            (constantProductComparison S.substitutionParameters
                Q.substitutionCarriers.1 Q.substitutionCarriers.1 ≫
              (constantFamilyFunctor S.substitutionParameters).map Q.equalitySubstitutionPair)
            (prod.fst ≫ (constantFamilyFunctor S.substitutionParameters).map (targetAtomPair Q f)))
          ((constantFamilyFunctor S.substitutionParameters).map Q.negationSubstitutionPair))
        (constantProductComparison S.substitutionParameters
            Q.substitutionCarriers.2 Q.substitutionCarriers.2 ≫
          (constantFamilyFunctor S.substitutionParameters).map Q.implicationSubstitutionPair))
      (constantProductComparison S.substitutionParameters V Q.substitutionCarriers.2 ≫
        parameterHom (targetQuantifierPair S Q f)))

end CategoricalEssentialIncompleteness.V46.NullaryInterpretation
