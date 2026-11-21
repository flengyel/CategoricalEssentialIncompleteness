/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationMap


/-! # Forward polynomial charts with arbitrary target leaf relations -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.RelationMapChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {P X Y : PredicateCategory T} {A B : Over P}
example (f : constantFamily P X ⟶ A) (g : constantFamily P Y ⟶ B)
    (rT rF : TernaryGraph) (p : Obj T M P) (φ ψ : M → M)
    (hf : ∀ z : Obj T M (P ⨯ X), (F T M).map (prod.fst : P ⨯ X ⟶ P) z = p →
      rT.val.Evalb ![p.val,φ ((F T M).map (prod.snd : P ⨯ X ⟶ X) z).val,((F T M).map f.left z).val])
    (hg : ∀ z : Obj T M (P ⨯ Y), (F T M).map (prod.fst : P ⨯ Y ⟶ P) z = p →
      rF.val.Evalb ![p.val,ψ ((F T M).map (prod.snd : P ⨯ Y ⟶ Y) z).val,((F T M).map g.left z).val])
    (a : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M ((a.withParameters P).eval.obj (constantFamily P X,constantFamily P Y)).left)
    (hz : (constantRepresentation T P X Y a).val.Evalb ![p.val,u,z.val]) :
    (representation T P (A,B) rT rF a).val.Evalb
      ![p.val,ConcreteNamedSubstitution.mapChildren φ ψ a u,
        ((F T M).map ((a.withParameters P).eval.map ((f,g) : (constantFamily P X,constantFamily P Y) ⟶ (A,B))).left z).val] :=
  relationRepresentation_map T M f g rT rF p φ ψ hf hg a u z hz
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.RelationMapChecks
