/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonAtomicSteps
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonNegationStep
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonImplicationStep
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonQuantifierStep
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonRelationCoproductValue

/-! # The actual full formula-substitution structure has the numeric root result -/

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
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "S" => categoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (categoricalSyntax T V σ π d)
local notation "Y" => (syntaxCarrier V σ π d true : PredicateCategory T)
local notation "B" => SyntaxPolynomial.formulaExpression V π d
local notation "E" => SyntaxPolynomial.power (SyntaxPolynomial.term : SyntaxPolynomial (PredicateCategory T)) 2
local notation "R" => SyntaxPolynomial.constructors π d
local notation "I" => SyntaxPolynomial.power (SyntaxPolynomial.formula : SyntaxPolynomial (PredicateCategory T)) 2
local notation "Q₀" => SyntaxPolynomial.product (SyntaxPolynomial.coefficient V)
  (SyntaxPolynomial.formula : SyntaxPolynomial (PredicateCategory T))

theorem formulaSubstitution_structure_result_value (p : Obj T M P) (u : M)
    (q : Obj T M (((B).withParameters P).eval.obj (S).substitutionAlgebra.a).left)
    (hq : (representation T P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true) B).val.Evalb ![p.val,u,q.val]) :
    optionCode T M Y ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ _)
      ((F T M).map (prod.snd : P ⨯ (S).substitutionCarriers.2 ⟶ _)
        ((F T M).map (S).substitutionAlgebra.str.2.left q))) =
      ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d
        (Arithmetic.pair ((F T M).map (prod.fst : P ⟶ V) p).val
          (Arithmetic.pair ((F T M).map (prod.snd : P ⟶ _) p).val
            (ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map (prod.snd : P ⟶ _) p).val))) u) := by
  let Z := constantFamily P (S).substitutionCarriers.2
  let C := fun a : SyntaxPolynomial (PredicateCategory T) => (a.withParameters P).eval.obj (S).substitutionAlgebra.a
  let opE : C E ⟶ Z := SyntaxPolynomial.parameterComparison P (S).substitutionCarriers E ≫
    (constantFamilyFunctor P).map (S).equalitySubstitutionPair
  let opR : C R ⟶ Z := SyntaxPolynomial.parameterComparison P (S).substitutionCarriers R ≫
    (constantFamilyFunctor P).map (S).relationSubstitutionPair
  let opN : C .formula ⟶ Z := (constantFamilyFunctor P).map (S).negationSubstitutionPair
  let opI : C I ⟶ Z := SyntaxPolynomial.parameterComparison P (S).substitutionCarriers I ≫
    (constantFamilyFunctor P).map (S).implicationSubstitutionPair
  let opQ : C Q₀ ⟶ Z := SyntaxPolynomial.parameterComparison P (S).substitutionCarriers Q₀ ≫
    parameterHom (S).quantifierSubstitutionPair
  let er := coprod.desc opE opR
  let ern := coprod.desc er opN
  let erni := coprod.desc ern opI
  let all := coprod.desc erni opQ
  let value := fun z : Obj T M Z.left => optionCode T M Y
    ((F T M).map (prod.snd : (S).substitutionCarriers.2 ⟶ OptionSyntax.obj Y)
      ((F T M).map prod.snd z))
  let param := Arithmetic.pair ((F T M).map (prod.fst : P ⟶ V) p).val
    (Arithmetic.pair ((F T M).map (prod.snd : P ⟶ _) p).val
      (ConcreteNamedSubstitution.freeVariables V σ π d ((F T M).map (prod.snd : P ⟶ _) p).val))
  let φ := fun v : M => ConcreteNamedSubstitution.result (ConcreteNamedSubstitution.formulaRoot V π d param v)
  change value ((F T M).map all.left q) = φ u
  apply relation_coprod_value T M P (S).substitutionAlgebra.a
    (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
    (.sum (.sum (.sum E R) .formula) I) Q₀ erni opQ value φ p.val ?_ ?_ u q hq
  · intro v z hz
    apply relation_coprod_value T M P (S).substitutionAlgebra.a
      (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
      (.sum (.sum E R) .formula) I ern opI value (fun w => φ (Arithmetic.pair w 0)) p.val ?_ ?_ v z hz
    · intro w z hz
      apply relation_coprod_value T M P (S).substitutionAlgebra.a
        (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
        (.sum E R) .formula er opN value (fun t => φ (Arithmetic.pair (Arithmetic.pair t 0) 0)) p.val ?_ ?_ w z hz
      · intro t z hz
        apply relation_coprod_value T M P (S).substitutionAlgebra.a
          (stateLeaf T P V σ π d false) (stateLeaf T P V σ π d true)
          E R opE opR value (fun x => φ (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair x 0) 0) 0))
          p.val ?_ ?_ t z hz
        · intro x z hz
          exact (equalitySubstitutionPair_result_code T V σ π d M p x z hz).trans
            (formulaRoot_equality_result V π d param x).symm
        · intro x z hz
          exact (relationSubstitutionPair_result_code T V σ π d M p x z hz).trans
            (formulaRoot_relation_result V π d param x).symm
      · intro t z hz
        exact negationSubstitutionPair_result_code T V σ π d M p t param z hz
    · intro w z hz
      exact implicationSubstitutionPair_result_code T V σ π d M p w param z hz
  · intro v z hz
    exact quantifierSubstitutionPair_result_code T V σ π d M p v z hz

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
