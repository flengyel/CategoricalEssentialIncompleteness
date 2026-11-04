import CategoricalEssentialIncompleteness.V46NumericalTuples

/-! Literal tuple carriers, partial-program graph comparison and equivalence. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.NumericalTuples

example : Tuple 0 = Unit := rfl
example : Tuple 1 = ℕ := rfl
example : Tuple 2 = (ℕ × ℕ) := rfl
example : codeSet 0 = {0} := codeSet_zero
example : codeSet 0 ≠ Set.univ := codeSet_zero_proper
example (n : ℕ) : decodeTuple 0 (n + 1) = Part.none := decodeTuple_zero_succ n
example (x : Tuple 0) : code 0 x = 0 := code_zero x
example (x : ℕ) : code 1 x = x := code_one x
example (x y : ℕ) : code 2 (x, y) = Nat.pair x y := rfl
example (m : ℕ) (x : Tuple m) : decodeTuple m (code m x) = Part.some x :=
  decodeTuple_code m x
example (m n : ℕ) : (decodeTuple m n).Dom ↔ n ∈ codeSet m := decodeTuple_domain m n

example {C D : Object} (f g : C ⟶ D) :
    f = g ↔ ∀ x : Point C, f.toFun x = g.toFun x := map_eq_iff f g

example {C D : Object} (f : C ⟶ D) :
    ∃ p : Tuple C.dimension → Part (Tuple D.dimension),
      Partrec p ∧ ∀ x : Point C, p x.val = Part.some (f.toFun x).val := f.represented

example {C D : Object} (f : C ⟶ D) (n k : ℕ) :
    k ∈ EnumerableCarriers.val (comparison.map f).hom n ↔ ∃ x : Point C,
      code C.dimension x.val = n ∧ code D.dimension (f.toFun x).val = k :=
  comparisonMap_graph f n k

example {C D : Object} (f : C ⟶ D) (n : ℕ) :
    (EnumerableCarriers.val (comparison.map f).hom n).Dom ↔ n ∈ codedSupport C :=
  f.restrictedProgram_domain n

example {C D : Object} (f : C ⟶ D) (x : Point C) :
    EnumerableCarriers.totalFunction (comparison.map f) (pointEquiv C x) =
      pointEquiv D (f.toFun x) := comparisonMap_function f x

example : CategoryTheory.Limits.IsTerminal (C := Object) terminalObject := terminalIsTerminal
example : codedSupport terminalObject = {0} := codedSupport_terminalObject
example : Object ≌ EnumerableCarriers.Total := equivalence
example : Object ≌ WideSubcategory (isTotal (C := SplitObject ClassicalPrograms.Rec)) :=
  classicalTotalEquivalence
