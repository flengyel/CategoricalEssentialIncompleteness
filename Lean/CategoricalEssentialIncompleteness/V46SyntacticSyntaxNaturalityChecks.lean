/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxNaturality

/-! # Checks for the actual polynomial naturality comparison -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (P C D : PredicateCategory T) (A B : Over P)
    (f : constantFamily P C ⟶ A) (g : constantFamily P D ⟶ B)
    (a : SyntaxPolynomial (PredicateCategory T)) (p : Obj T M P) (u v : M)
    (z : Obj T M ((a.withParameters P).eval.obj
      (constantFamily P C, constantFamily P D)).left)
    (h : (constantRepresentation T P C D a).val.Evalb ![p.val, u, z.val])
    (hm : (mapRaw P (rawArrow T f) (rawArrow T g) a).val.Evalb ![p.val, u, v]) :
    (fiberRepresentation T P (A, B) a).val.Evalb
      ![p.val, v, ((F T M).map ((a.withParameters P).eval.map ((f, g) :
        (constantFamily P C, constantFamily P D) ⟶ (A, B))).left z).val] :=
  representation_arrow_map T M f g a p u v z h hm
