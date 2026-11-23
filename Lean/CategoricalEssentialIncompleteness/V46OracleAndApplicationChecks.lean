/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MachineOracleTuring
public import CategoricalEssentialIncompleteness.V46ForkOpenGluing
public import CategoricalEssentialIncompleteness.V46ForkUndecidedAtoms
public import CategoricalEssentialIncompleteness.V46ForkSignedAtomInclusion
public import CategoricalEssentialIncompleteness.V46WeightedCubeTopology
public import CategoricalEssentialIncompleteness.V46PrecompleteClasses

/-! # Oracle indices, fork subspaces, signed supports and the weighted topology -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46

section Oracle
open OracleComputation OracleComputation.Restricted
open CategoryTheory.CoprodStruct
example : Computable₂ sectionIndex := sectionIndex_computable
example (A : Set ℕ) (e z x : ℕ) :
    (Miller.OracleProgram.numberedEval (sectionIndex e z) (bits A) x).Dom ↔
      (Miller.OracleProgram.numberedEval e (bits A) (Nat.pair z x)).Dom :=
  machine_section A e z x
example : ∃ c : ℕ → ℕ, Computable c ∧ ∀ A e x,
    oracleDomain A (c e) x ↔ (Miller.OracleProgram.numberedEval e (bits A) x).Dom := exists_prefix_compiler
example : ∃ c : ℕ → ℕ, Computable c ∧ ∀ A e x,
    (Miller.OracleProgram.numberedEval (c e) (bits A) x).Dom ↔ oracleDomain A e x := exists_machine_compiler
example (A : Set ℕ) (e a x y : ℕ) :
    y ∈ (machineTau A).val (Nat.pair e a, x) ↔
      (Miller.OracleProgram.numberedEval a (bits A) x).Dom ∧ y ∈ ordinaryEval e x := by
  simpa only [Nat.unpair_pair, machineDomain] using mem_machineTau A (Nat.pair e a) x y
example (A : Set ℕ) : RecursionCategory.IsTuringMorphism (machineTau A) := machineTau_isTuring A
example : Complementary separator separatorComplement ∧
    machinePair0 K ≤ separator ∧ machinePair1 K ≤ separatorComplement :=
  ⟨separator_complementary, machine_separator_bounds⟩
example : ¬ Inseparable (machinePair0 K) (machinePair1 K) := machine_pair_separated
example (s : PartialFun.of ℕ ⟶ coprod (PartialFun.of ℕ) (PartialFun.of ℕ))
    (hn : Idem.pull s (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separatorComplement)
    (hp : Idem.pull s (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) = (rangeFunctor K).mapIdem separator) :
    ¬ ∃ ℓ : N K ⟶ coprod (N K) (N K),
      (inclusion K).map ℓ = s ≫ ((rangeFunctor K).comparison (N K) (N K)).hom :=
  machine_no_lift s hn hp
end Oracle

section Bernardi
example {R : ℕ → ℕ → Prop} (h : Precomplete R) {P N : Set ℕ}
    (hP : P.Nonempty) (hN : N.Nonempty) (hd : Disjoint P N)
    (p : ∀ x y, R x y → y ∈ P → x ∈ P) (n : ∀ x y, R x y → y ∈ N → x ∈ N) :
    Numerical.RecursivelyInseparable P N := h.inseparable_unions hP hN hd p n
end Bernardi

section Metric
open Miller Miller.Cut.Distance
example : weightedMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace Point) := rfl
example (U : Set Point) : IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, productDistance x y < ε → y ∈ U :=
  isOpen_iff_productDistance U
end Metric

section Topology
open ForkTopology SierpinskiPoint
example {Y : Type*} [TopologicalSpace Y] (f g : C(SierpinskiPoint, Y)) (h : f openPoint = g openPoint) :
    ∃! k : C(Point,Y), (∀ x, k (inclusion false x) = f x) ∧ (∀ x, k (inclusion true x) = g x) :=
  existsUnique_gluing f g h
end Topology

section Atoms
open ForkSyntax ForkAxiomClosure ForkDerivation
example (i : Bool) (A : Set ℕ) (hA : REPred (· ∈ A))
    (hin : EnumerableCarriers.support (endpointTheory i categoricalTheory) ⊆ theoremCodes A)
    (hcon : ∀ p : Formula, ¬(Derives A p ∧ Derives A (.neg p))) :
    ∃ n : ℕ, ¬Derives A (.atom n) ∧ ¬Derives A (.neg (.atom n)) :=
  axioms_undecided_atom i A hA hin hcon
example (P M : Idem EffectiveFork.V) :
    Mono (coprod.desc (NumericalForkPartialMaps.totalEquivalence.inverse.map (axiomInclusion P ≫ ForkDerivation.atom))
      (NumericalForkPartialMaps.totalEquivalence.inverse.map (axiomInclusion M ≫ ForkDerivation.atom ≫ negation))) :=
  tuple_signed_atoms_mono P M
end Atoms

#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.image_switch_eq
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.left_evaluation_turing
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.right_evaluation_turing
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.syntaxAlgebra
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.polynomialTotal
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.ForkSyntax.t0_consistency
#print axioms CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation.Restricted.rangeFunctor
