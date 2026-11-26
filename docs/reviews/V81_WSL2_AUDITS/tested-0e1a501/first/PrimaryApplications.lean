module

import CategoricalEssentialIncompleteness.V46MachineOracleTuring
import CategoricalEssentialIncompleteness.V46SyntacticNonLocalConnectedness

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open OracleComputation OracleComputation.Restricted

namespace FirstReaderPrimary

-- The second projection is the projection denoted p₁ in the 2006 report.
example (u : N K ⟶ N K) :
    ∃ e : N K ⟶ N K, isTotal e ∧
      productMap e (𝟙 (N K)) ≫ machineTau K = second (N K) (N K) ≫ u := by
  obtain ⟨e, ht, eq⟩ :=
    machineTau_isTuring K (N K) (second (N K) (N K) ≫ u)
  refine ⟨e, ?_, eq⟩
  change PCategoryStruct.rst e = 𝟙 _ at ht
  rw [induced_restriction] at ht
  exact ht

example : ¬ Inseparable (machinePair0 K) (machinePair1 K) :=
  machine_pair_separated

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46

-- Corollary 4.4 concerns the unprimed category of every consistent c.e. extension.
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [Consistent T] [T.RE] :
    ¬ LocallyConnected (PrintedObjectCoding.NormalizedCategory T) :=
  ConnectedNumeralDomains.unprimed_not_locallyConnected T

#check @machine_no_lift
#check @ConnectedNumeralDomains.connected_le_numeral
#check @ConnectedNumeralDomains.indistinguishable_on_connected
#print axioms machine_pair_separated
#print axioms machine_no_lift
#print axioms ConnectedNumeralDomains.unprimed_not_locallyConnected

end FirstReaderPrimary
