/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveIndices
public import CategoricalEssentialIncompleteness.V46UniformTraceBuilders

/-! # Native certificates for the actual composition and s-m-n index builders -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoricalEssentialIncompleteness.V46.UniformTrace

theorem specialize_primrec : Primrec₂ (specialize : ℕ → ℕ → ℕ) :=
  (templateIndex_primrec specializationTemplateIndex).comp SyntacticSyntax.NatVectors.pair_primrec

theorem compose_primrec : Primrec₂ (compose : ℕ → ℕ → ℕ) :=
  (templateIndex_primrec compositionTemplateIndex).comp SyntacticSyntax.NatVectors.pair_primrec

theorem specialize_natPrimrec : Nat.Primrec (Nat.unpaired (specialize : ℕ → ℕ → ℕ)) :=
  Primrec.nat_iff.mp (specialize_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

theorem compose_natPrimrec : Nat.Primrec (Nat.unpaired (compose : ℕ → ℕ → ℕ)) :=
  Primrec.nat_iff.mp (compose_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))

end CategoricalEssentialIncompleteness.V46.UniformTrace
