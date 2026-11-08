import CategoricalEssentialIncompleteness.V46MillerCutDyadicArithmetic
noncomputable section
open CategoricalEssentialIncompleteness.V46.Miller

example (a b : Cut.Dyadic.Code) :
    Cut.Dyadic.value (Cut.Dyadic.positiveSub a b)=
      max (Cut.Dyadic.value a-Cut.Dyadic.value b) 0 := Cut.Dyadic.value_positiveSub a b

example (a b : Cut.Dyadic.Code) (ha : Cut.Dyadic.value a≤1) :
    Cut.Dyadic.value (Cut.Dyadic.separator a b)=
      1/2+(Cut.Dyadic.value b-Cut.Dyadic.value a)/4 := Cut.Dyadic.value_separator a b ha

example (a : ℕ × ℕ) :
    (Rationals.q (Cut.Dyadic.outputIndex a):ℝ)=(a.1:ℝ)/(2:ℝ)^a.2 :=
  Cut.Dyadic.outputIndex_value a

example : Primrec₂ Cut.Dyadic.separator := Cut.Dyadic.separator_primrec
example : Primrec Cut.Dyadic.outputIndex := Cut.Dyadic.outputIndex_primrec
