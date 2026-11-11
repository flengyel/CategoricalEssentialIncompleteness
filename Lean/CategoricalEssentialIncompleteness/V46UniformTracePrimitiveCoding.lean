/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceProgram
public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveHistory

/-! # Native primitive certificates for the literal trace program

The actual all-model PA graph comparison was proved in UniformTraceProgram
before any native certificate is used. The native code computation theorem
below is used over the standard natural numbers only.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
namespace PrimitiveCoding
namespace PrimitiveTotal

theorem earlier : PrimitiveTotal earlierCode := by
  have hhistory : PrimitiveTotal (codeHistoryEvaluator.comp
      ![Code.proj (0 : Fin 4), Code.proj 2, Code.proj 3]) := by
    apply comp historyEvaluator
    intro i
    fin_cases i
    · exact proj 0
    · exact proj 2
    · exact proj 3
  exact prec (one 2) (ifPos hhistory (zero 4) (proj 1))

/-- This closed certificate is constructed from the literal evaluator,
fixed numeric equality and primitive recursion. -/
theorem traceProgram :
    PrimitiveTotal CategoricalEssentialIncompleteness.V46.UniformTrace.traceProgram := by
  have hargs : ∀ i, PrimitiveTotal (traceArguments i) := by
    intro i
    fin_cases i
    · exact unpair1 (proj 2)
    · exact proj 0
    · exact proj 1
  exact mul (eq (comp historyEvaluator hargs) (succ (unpair2 (proj 2))))
    (eq (comp earlier hargs) (one 3))

end PrimitiveTotal
end PrimitiveCoding

noncomputable def traceCheck (e x t : ℕ) : ℕ := by
  classical
  exact if traceFormula.val.Evalb ![e, x, t] then 1 else 0

/-- The primitive function comes with its actual Code.eval proof.
The standard model bridge identifies it with the chosen trace check. -/
theorem traceCheck_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ => traceCheck p.1 p.2.1 p.2.2) := by
  obtain ⟨f, hcf, hpf⟩ := PrimitiveCoding.PrimitiveTotal.traceProgram
  have hv : Primrec (fun p : ℕ × ℕ × ℕ => List.Vector.ofFn ![p.1, p.2.1, p.2.2]) := by
    apply Primrec.vector_ofFn
    intro i
    fin_cases i
    · exact Primrec.fst
    · exact Primrec.fst.comp Primrec.snd
    · exact Primrec.snd.comp Primrec.snd
  apply Primrec.of_eq (hpf.comp hv)
  intro p
  symm
  have hm := FFL.FirstOrder.Arithmetic.models_code hcf
    (traceCheck p.1 p.2.1 p.2.2) ![p.1, p.2.1, p.2.2]
  exact Part.mem_some_iff.mp (hm.mp (traceProgram_value p.1 p.2.1 p.2.2))

/-- The certificate concerns the actual trace formula over Nat. It has
no assumed primitive predicate or evaluator premise. -/
theorem trace_primrec :
    PrimrecPred (fun p : ℕ × ℕ × ℕ => traceFormula.val.Evalb ![p.1, p.2.1, p.2.2]) := by
  have h := Primrec.eq.comp traceCheck_primrec (Primrec.const 1)
  apply PrimrecPred.of_eq h
  intro p
  classical
  by_cases hp : traceFormula.val.Evalb ![p.1, p.2.1, p.2.2] <;>
    simp [traceCheck, hp]

private theorem decodeTriple_primrec {f : ℕ × ℕ × ℕ → ℕ} (hf : Primrec f) :
    Primrec (fun n : ℕ => f (n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2)) := by
  have hleft := Primrec.fst.comp Primrec.unpair
  have hright := Primrec.snd.comp Primrec.unpair
  exact hf.comp (Primrec.pair hleft
    (Primrec.pair (hleft.comp hright) (hright.comp hright)))

theorem traceCheck_natPrimrec : Nat.Primrec (fun n : ℕ =>
    traceCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) :=
  Primrec.nat_iff.mp (decodeTriple_primrec traceCheck_primrec)

end CategoricalEssentialIncompleteness.V46.UniformTrace
