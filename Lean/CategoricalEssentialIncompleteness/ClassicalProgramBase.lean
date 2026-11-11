/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.FunctorImage
public import CategoricalEssentialIncompleteness.SyntacticFiniteSwitch

/-! # Extensional standard evaluation on the formal numerical types -/

@[expose] public section

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

noncomputable section

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

abbrev standardFunctor := SyntacticModel.modelFunctor 𝗣𝗔 ℕ
abbrev Rec := FunctorImage standardFunctor
abbrev Q := FunctorImage.quotient standardFunctor
abbrev J := FunctorImage.inclusion standardFunctor

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
