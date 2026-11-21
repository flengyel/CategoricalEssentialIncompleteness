/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationInitial
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxAlgebra
public import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPolynomial

/-! # Constructor charts for the constructed derivation trees

These charts retain the original numerical tree word. Standard-code
induction uses its node count; no preservation of initiality by a model
interpretation functor is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
open SyntacticSyntax
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (labels : ℕ → PredicateCategory T) (N : ℕ)

def projectedInput := constructorProjection labels N
  (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit)

/-- Forgetting the unused second sort before the unary constructor has
exactly the original joint-algebra first constructor as its composite. -/
theorem projectedInput_structure :
    projectedInput T labels N ≫ (oneSortAlgebra T labels N).str =
      (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit).str.1 := by
  change constructorProjection labels N _ ≫
    (inv (constructorProjection labels N _) ≫ _) = _
  simp only [IsIso.hom_inv_id_assoc]

section Rules
variable {F₀ : PredicateCategory T} {bound : ℕ} (R : RulePresentation F₀ bound)

def ordinaryInput :=
  projectedInput T (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound ≫
    (PolynomialComparison.comparison R).hom.app
      (oneSortAlgebra T (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound).a

instance ordinaryInput_isIso : IsIso (ordinaryInput T R) := by
  unfold ordinaryInput projectedInput
  infer_instance

theorem comparison_structure :
    (PolynomialComparison.comparison R).hom.app
        (oneSortAlgebra T (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound).a ≫
      (ordinaryTree T R).str =
        (oneSortAlgebra T (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound).str := by
  simp [ordinaryTree, PolynomialComparison.mappedAlgebra, AlgebraTransport.mappedAlgebra,
    PolynomialComparison.endofunctorComparison]

/-- The finite coproduct comparison changes the chosen categorical
input object, while preserving the same postfix constructor composite. -/
theorem ordinaryInput_structure :
    ordinaryInput T R ≫ (ordinaryTree T R).str =
      (postfixAlgebra T
        (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit).str.1 := by
  rw [ordinaryInput, Category.assoc, comparison_structure, projectedInput_structure]

end Rules

variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- A represented ordered input to the concrete unary tree algebra produces the same word
number as the postfix constructor. -/
theorem projected_constructor_value (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors labels N).eval.obj
      (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit).a))
    (h : (baseRepresentation T
      (termCarrier (SyntaxPolynomial.constructors labels N) .unit)
      (formulaCarrier (SyntaxPolynomial.constructors labels N) .unit)
      (SyntaxPolynomial.constructors labels N)).val.Evalb ![u,z.val]) :
    ((F T M).map (oneSortAlgebra T labels N).str
      ((F T M).map (projectedInput T labels N) z)).val =
      Coding.constructor false (SyntaxPolynomial.constructors labels N) u := by
  calc
    _ = ((F T M).map (projectedInput T labels N ≫ (oneSortAlgebra T labels N).str) z).val := by
      rw [Functor.map_comp]
      rfl
    _ = ((F T M).map
        (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit).str.1 z).val := by
      rw [projectedInput_structure]
      rfl
    _ = _ := postfixTerm_value T M (SyntaxPolynomial.constructors labels N) .unit u z h

theorem ordinary_constructor_value {F₀ : PredicateCategory T} {bound : ℕ}
    (R : RulePresentation F₀ bound) (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound).eval.obj
      (postfixAlgebra T (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit).a))
    (h : (baseRepresentation T
      (termCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
      (formulaCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
      (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound)).val.Evalb ![u,z.val]) :
    ((F T M).map (ordinaryTree T R).str
      ((F T M).map (ordinaryInput T R) z)).val =
      Coding.constructor false (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) u := by
  calc
    _ = ((F T M).map (ordinaryInput T R ≫ (ordinaryTree T R).str) z).val := by
      rw [Functor.map_comp]
      rfl
    _ = ((F T M).map (postfixAlgebra T
        (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit).str.1 z).val := by
      rw [ordinaryInput_structure]
      rfl
    _ = _ := postfixTerm_value T M
      (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit u z h

omit [M↓[ℒₒᵣ] ⊧* T] in
theorem mapChildren_power_second (f g h : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.power .term n) u =
      ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.power .term n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change Arithmetic.pair
              (ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.power .term (n + 1)) (π₁ u))
              (f (π₂ u)) =
            Arithmetic.pair
              (ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.power .term (n + 1)) (π₁ u))
              (f (π₂ u))
          rw [ih]

omit [M↓[ℒₒᵣ] ⊧* T] in
theorem mapChildren_constructors_second (families : ℕ → Carrier)
    (f g h : M → M) (n : ℕ) (u : M) :
    ConcreteNamedSubstitution.mapChildren f g (SyntaxPolynomial.constructors families n) u =
      ConcreteNamedSubstitution.mapChildren f h (SyntaxPolynomial.constructors families n) u := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      simp only [SyntaxPolynomial.constructors, ConcreteNamedSubstitution.mapChildren, ih,
        mapChildren_power_second M f g h]

/-- A metatheoretic extension of an interpreted morphism is used only to state the finite
chart equation. No computability of the morphism is inferred. -/
def scalarExtension {X Y : PredicateCategory T} (f : X ⟶ Y) (u : M) : M := by
  classical
  exact if hu : X.val.Evalb ![u] then ((F T M).map f ⟨u,hu⟩).val else 0

omit [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem scalarExtension_value {X Y : PredicateCategory T} (f : X ⟶ Y) (x : Obj T M X) :
    ((F T M).map f x).val = scalarExtension T M f x.val := by
  simp only [scalarExtension, dite_eq_left x.property]

/-- The unary projection preserves the complete ordered numerical input,
since the ordinary rule polynomial contains no formula positions. -/
theorem projectedInput_chart (u : M)
    (z : Obj T M ((SyntaxPolynomial.constructors labels N).eval.obj
      (postfixAlgebra T (SyntaxPolynomial.constructors labels N) .unit).a))
    (h : (baseRepresentation T
      (termCarrier (SyntaxPolynomial.constructors labels N) .unit)
      (formulaCarrier (SyntaxPolynomial.constructors labels N) .unit)
      (SyntaxPolynomial.constructors labels N)).val.Evalb ![u,z.val]) :
    (baseRepresentation T (oneSortAlgebra T labels N).a (⊤_ (PredicateCategory T))
      (SyntaxPolynomial.constructors labels N)).val.Evalb
        ![u,((F T M).map (projectedInput T labels N) z).val] := by
  let X : PredicateCategory T := termCarrier (SyntaxPolynomial.constructors labels N) .unit
  let Y : PredicateCategory T := formulaCarrier (SyntaxPolynomial.constructors labels N) .unit
  let g : Y ⟶ (⊤_ (PredicateCategory T)) := terminal.from Y
  have hg := scalarExtension_value T M g
  have hi : ∀ x : Obj T M X, ((F T M).map (𝟙 X) x).val = id x.val := by simp
  have hr := ConcreteNamedComparison.representation_map T M (𝟙 X) g id
    (scalarExtension T M g) hi hg (SyntaxPolynomial.constructors labels N) u z h
  have hu := (baseRepresentation_support T M X Y
    (SyntaxPolynomial.constructors labels N) u z.val h).1
  rw [mapChildren_constructors_second M labels id (scalarExtension T M g) id N u,
    ConcreteNamedSubstitution.mapChildren_id (SyntaxPolynomial.constructors labels N) u hu] at hr
  exact hr

/-- Every interpreted input to the ordinary tree constructor has an ordered numerical
chart and the size-decrease certificate. -/
theorem ordinary_input_chart {F₀ : PredicateCategory T} {bound : ℕ}
    (R : RulePresentation F₀ bound)
    (z : Obj T M ((PolynomialComparison.ordinary R).obj (ordinaryTree T R).a)) :
    ∃ (u : M)
      (source : Obj T M ((SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound).eval.obj
        (postfixAlgebra T (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit).a)),
      (baseRepresentation T
        (termCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
        (formulaCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
        (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound)).val.Evalb ![u,source.val] ∧
      (F T M).map (ordinaryInput T R) source = z ∧
      ((F T M).map (ordinaryTree T R).str z).val =
        Coding.constructor false (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) u ∧
      Coding.ChildSize (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound)
        (len ((F T M).map (ordinaryTree T R).str z).val) u := by
  let source := (F T M).map (inv (ordinaryInput T R)) z
  obtain ⟨u,hu⟩ := baseRepresentation_cover T M
    (termCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
    (formulaCarrier (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) .unit)
    (SyntaxPolynomial.constructors (PolynomialComparison.coefficients (D := PredicateCategory T) R) bound) source
  have hs : (F T M).map (ordinaryInput T R) source = z := by
    change (F T M).map (ordinaryInput T R) ((F T M).map (inv (ordinaryInput T R)) z) = z
    calc
      _ = (F T M).map (inv (ordinaryInput T R) ≫ ordinaryInput T R) z := by
        rw [Functor.map_comp]
        rfl
      _ = z := by
        rw [IsIso.inv_hom_id, (F T M).map_id]
        rfl
  have hv := ordinary_constructor_value T M R u source hu
  rw [hs] at hv
  refine ⟨u,source,hu,hs,hv,?_⟩
  rw [hv]
  exact (Coding.childSizeGraph_eval _ _ _).mp (Coding.children_smaller false _ u)

end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.StandardInduction
