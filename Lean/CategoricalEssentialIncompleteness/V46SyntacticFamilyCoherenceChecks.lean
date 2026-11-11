/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticFamilyCoherence

/-! Explicit Appendix D identity, composition and natural-square coherence. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctionFamilies
open CategoricalEssentialIncompleteness.V46.SyntacticFamilyCoherence

variable (T T' T'' : ArithmeticTheory) [𝗣𝗔 ⪯ T] [𝗣𝗔 ⪯ T'] [𝗣𝗔 ⪯ T'']
variable [T ⪯ T'] [T' ⪯ T'']

example : SyntacticExtension.functor T T = 𝟭 (CodedProgramCategory T) := quotient_id T

example : familyProjection T T = 𝟭 (Family.{0} (ModelIndex T)) := projection_id T

example :
    letI : T ⪯ T'' := WeakerThan.trans
      (inferInstance : T ⪯ T') (inferInstance : T' ⪯ T'')
    SyntacticExtension.functor T T' ⋙ SyntacticExtension.functor T' T'' =
      SyntacticExtension.functor T T'' :=
  quotient_comp T T' T''

example :
    letI : T ⪯ T'' := WeakerThan.trans
      (inferInstance : T ⪯ T') (inferInstance : T' ⪯ T'')
    familyProjection T T' ⋙ familyProjection T' T'' = familyProjection T T'' :=
  projection_comp T T' T''

example : SyntacticExtension.functor T T' ⋙ familyFunctor T' ≅
    familyFunctor T ⋙ familyProjection T T' := square T T'

example {Q R : CodedProgramCategory T} (f : Q ⟶ R) :
    (familyFunctor T').map ((SyntacticExtension.functor T T').map f) ≫
        (square T T').hom.app R =
      (square T T').hom.app Q ≫ (familyProjection T T').map ((familyFunctor T).map f) :=
  square_naturality T T' f

example : pastedSquare T T' T'' = directSquare T T' T'' := square_comp_coherence T T' T''

example : square T T = unitSquare T := square_unit_coherence T
