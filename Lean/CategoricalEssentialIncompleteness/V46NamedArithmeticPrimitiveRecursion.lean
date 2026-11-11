/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveVectors

/-! Empty-parameter primitive recursion, proved before specializing the
blueprint to the concrete arithmetic syntax operations. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
variable {p : PR.Blueprint 0} (c : PR.Construction M p)

def scalarResult (n : M) : M := c.result ![] n

@[simp] theorem scalarResult_eval (out n : M) :
    p.resultDef.val.Evalb ![out,n] ↔ out = scalarResult c n := by
  change p.resultDef.val.Evalb ![out,n] ↔ out = c.result ![] n
  rw [c.result_defined_iff]
  have hp : (fun i : Fin 0 => (![out,n] : Fin 2 → M) i.succ.succ) = ![] := by
    funext i
    exact Fin.elim0 i
  rw [hp]
  rfl

theorem scalarResult_defined : 𝚺₁-Function₁ (scalarResult c) via p.resultDef := .mk fun v => by
  change p.resultDef.val.Evalb v ↔ v 0 = scalarResult c (v 1)
  have hv : ![v 0,v 1] = v := (Matrix.fun_eq_vec_two v).symm
  simpa only [hv] using scalarResult_eval c (v 0) (v 1)
theorem scalarResult_definable : 𝚺₁-Function₁ (scalarResult c) := (scalarResult_defined c).to_definable
theorem scalarResult_definable' (Γ m) : Γ-[m+1]-Function₁ (scalarResult c) :=
  (scalarResult_definable c).of_sigmaOne
end Models

open SyntacticSyntax.NatVectors
variable {p : PR.Blueprint 0} (c : PR.Construction ℕ p)

theorem scalarResult_primrec
    (hz : Primrec (fun _ : Unit => c.zero ![]))
    (hs : Primrec₂ (fun (_ : Unit) (v : ℕ × ℕ) => c.succ ![] v.1 v.2)) :
    Primrec (scalarResult c) := by
  have h := pr_primrec c (fun _ : Unit => ![]) hz hs
  exact h.comp (Primrec.pair (Primrec.const ()) Primrec.id)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion
