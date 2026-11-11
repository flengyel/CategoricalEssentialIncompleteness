/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTraceTemplates
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveParser

/-! # Actual native primitive-recursion certificates for index construction

These are standard certificates only. The all-model semantic parameter
equation is proved separately in UniformTraceTemplates.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoricalEssentialIncompleteness.V46.UniformTrace
open ProgramIndices

theorem pairIndex_primrec : Primrec₂ (pairIndex : ℕ → ℕ → ℕ) := by
  have hp := SyntacticSyntax.NatVectors.pair_primrec
  exact Primrec.of_eq
    (Primrec.nat_add.comp (Primrec.const 4) (Primrec.nat_mul.comp (Primrec.const 4) hp))
    (fun p => rfl)

theorem compIndex_primrec : Primrec₂ (compIndex : ℕ → ℕ → ℕ) := by
  have hp := SyntacticSyntax.NatVectors.pair_primrec
  exact Primrec.of_eq
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 4) (Primrec.nat_mul.comp (Primrec.const 4) hp))
      (Primrec.const 2)) (fun p => rfl)

theorem constantIndex_primrec : Primrec (constantIndex : ℕ → ℕ) := by
  have hz : Primrec (fun _ : Unit => (constantIndexConstruction (M := ℕ)).zero ![]) :=
    Primrec.const 0
  have hs : Primrec₂ (fun (_ : Unit) (t : ℕ × ℕ) =>
      (constantIndexConstruction (M := ℕ)).succ ![] t.1 t.2) :=
    compIndex_primrec.comp (Primrec.const 1) (Primrec.snd.comp Primrec.snd)
  have hr := SyntacticSyntax.NatVectors.pr_primrec
    (constantIndexConstruction (M := ℕ)) (fun _ : Unit => ![]) hz hs
  exact Primrec.of_eq (hr.comp (Primrec.pair (Primrec.const ()) Primrec.id)) (fun _ => rfl)

theorem templateIndex_primrec (v : ℕ) : Primrec (templateIndex v : ℕ → ℕ) :=
  compIndex_primrec.comp (Primrec.const _)
    (pairIndex_primrec.comp constantIndex_primrec (Primrec.const _))

theorem constantIndex_natPrimrec : Nat.Primrec (constantIndex : ℕ → ℕ) :=
  Primrec.nat_iff.mp constantIndex_primrec

theorem templateIndex_natPrimrec (v : ℕ) : Nat.Primrec (templateIndex v : ℕ → ℕ) :=
  Primrec.nat_iff.mp (templateIndex_primrec v)

end CategoricalEssentialIncompleteness.V46.UniformTrace
