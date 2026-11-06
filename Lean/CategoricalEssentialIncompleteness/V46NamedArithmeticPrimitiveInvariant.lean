import CategoricalEssentialIncompleteness.V46NamedArithmeticPrimitiveRecursion
import CategoricalEssentialIncompleteness.V46SyntacticPredicates

/-! Internal arithmetic induction for a carrier invariant of a constructed
primitive recursion, before specializing its graph or carrier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion

def zeroFiberCarrier (C : Carrier) (F : 𝚺₁.Semisentence 2) : Carrier :=
  .mkSigma “word. !C.val word ∧ !F.val 0 word”

@[simp] theorem zeroFiberCarrier_eval (C : Carrier) (F : 𝚺₁.Semisentence 2)
    {M : Type} [ORingStructure M] (word : M) :
    (zeroFiberCarrier C F).val.Evalb ![word] ↔
      C.val.Evalb ![word] ∧ F.val.Evalb ![0,word] := by
  simp [zeroFiberCarrier]

section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {p : PR.Blueprint 0} (c : PR.Construction M p) (C : Carrier)

theorem scalarResult_carrier
    (hz : C.val.Evalb ![c.zero ![]])
    (hs : ∀ n previous : M, C.val.Evalb ![previous] →
      C.val.Evalb ![c.succ ![] n previous]) (n : M) :
    C.val.Evalb ![scalarResult c n] := by
  have hCd : 𝚺₁-Predicate (fun word : M => C.val.Evalb ![word]) via C := .mk fun v => by
    have hv : ![v 0] = v := by funext i; fin_cases i; rfl
    simp only [hv]
  have hC : 𝚺₁-Predicate (fun word : M => C.val.Evalb ![word]) := hCd.to_definable
  induction n using ISigma1.sigma1_succ_induction
  · exact hC.comp (scalarResult_definable c)
  case zero =>
    change C.val.Evalb ![c.result ![] 0]
    rw [c.result_zero]
    exact hz
  case succ n ih =>
    change C.val.Evalb ![c.result ![] (n+1)]
    rw [c.result_succ]
    exact hs n (scalarResult c n) ih
end Models
end CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion
