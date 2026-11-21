/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxParameter
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonModels

/-! # Parameter-comparison points and their product projections -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
variable (P X Y : PredicateCategory T)

/-- Interpret a proved square with opaque morphisms before specializing its nodes to
parameterized polynomial evaluations. -/
theorem parameterPoint_diagram {A B C D : PredicateCategory T}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ C) (k : C ⟶ D)
    (comm : f ≫ g = h ≫ k) (q : Obj T M A) :
    (F T M).map g ((F T M).map f q) = (F T M).map k ((F T M).map h q) := by
  have he := congrArg (fun arrow => (F T M).map arrow q) comm
  simpa only [Functor.map_comp_apply] using he

theorem parameterPoint_product_fst (a b : SyntaxPolynomial (PredicateCategory T))
    (q : Obj T M (((a.product b).withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left) :
    (F T M).map (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _)
      ((F T M).map (parameterValueMap T P X Y (.product a b)) q) =
      (F T M).map (parameterValueMap T P X Y a)
        ((F T M).map (prod.fst : (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⨯
          (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⟶ _).left q) := by
  exact parameterPoint_diagram T M (parameterValueMap T P X Y (.product a b))
    (prod.fst : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _)
    (prod.fst : (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⨯
      (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⟶ _).left
    (parameterValueMap T P X Y a) (parameterValueMap_product_fst T P X Y a b) q

theorem parameterPoint_product_snd (a b : SyntaxPolynomial (PredicateCategory T))
    (q : Obj T M (((a.product b).withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left) :
    (F T M).map (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _)
      ((F T M).map (parameterValueMap T P X Y (.product a b)) q) =
      (F T M).map (parameterValueMap T P X Y b)
        ((F T M).map (prod.snd : (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⨯
          (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⟶ _).left q) := by
  exact parameterPoint_diagram T M (parameterValueMap T P X Y (.product a b))
    (prod.snd : a.eval.obj (X,Y) ⨯ b.eval.obj (X,Y) ⟶ _)
    (prod.snd : (a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⨯
      (b.withParameters P).eval.obj (constantFamily P X,constantFamily P Y) ⟶ _).left
    (parameterValueMap T P X Y b) (parameterValueMap_product_snd T P X Y a b) q

theorem parameterPoint_formula (q : Obj T M (P ⨯ Y)) :
    (F T M).map (parameterValueMap T P X Y .formula) q =
      (F T M).map (prod.snd : P ⨯ Y ⟶ Y) q := by
  erw [parameterValueMap_formula T P X Y]
  rfl

theorem parameterPoint_coefficient (C : PredicateCategory T) (q : Obj T M (P ⨯ C)) :
    (F T M).map (parameterValueMap T P X Y (.coefficient C)) q =
      (F T M).map (prod.snd : P ⨯ C ⟶ C) q := by
  erw [parameterValueMap_coefficient T P X Y C]
  rfl

theorem parameterComparison_point_parameter (a : SyntaxPolynomial (PredicateCategory T))
    (q : Obj T M ((a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left) :
    (F T M).map (prod.fst : P ⨯ a.eval.obj (X,Y) ⟶ P)
      ((F T M).map (SyntaxPolynomial.parameterComparison P (X,Y) a).left q) =
      (F T M).map ((a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).hom q :=
  over_value T M (SyntaxPolynomial.parameterComparison P (X,Y) a) q

theorem parameterComparison_point_value (a : SyntaxPolynomial (PredicateCategory T))
    (q : Obj T M ((a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left) :
    (F T M).map (prod.snd : P ⨯ a.eval.obj (X,Y) ⟶ _)
      ((F T M).map (SyntaxPolynomial.parameterComparison P (X,Y) a).left q) =
      (F T M).map (parameterValueMap T P X Y a) q := by
  change (F T M).map prod.snd ((F T M).map (SyntaxPolynomial.parameterComparison P (X,Y) a).left q) =
    (F T M).map ((SyntaxPolynomial.parameterComparison P (X,Y) a).left ≫ prod.snd) q
  exact ((F T M).map_comp_apply _ _ q).symm

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
