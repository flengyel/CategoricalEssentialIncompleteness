/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ModelSubstitutionSoundness


/-! # Instantiation and equality through the admissibility diagrams -/

@[expose] public section
noncomputable section
universe v u w k
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ModelSubstitutionSoundnessChecks
open ModelSubstitutionSoundness
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable (G : C ⥤ Type w) {V : C} {σ π : ℕ → C} {d : ℕ}
variable (S : CategoricalSyntax V σ π d) {K : Type k}
variable (name : G.obj V → ℕ)
variable (eval : G.obj S.algebra.a.1 → (ℕ → K) → K)
variable (P : G.obj S.algebra.a.2 → (ℕ → K) → Prop)
variable (hsub : ∀ (a : G.obj S.admissibleSubstitution) (ρ : ℕ → K),
  P (G.map S.formulaSubstitution a) ρ ↔
    P (G.map prod.fst (G.map S.admissibleInclusion a))
      (Function.update ρ
        (name (G.map prod.fst (G.map prod.snd (G.map S.admissibleInclusion a))))
        (eval (G.map prod.snd (G.map prod.snd (G.map S.admissibleInclusion a))) ρ)))

variable (himp : ∀ (z : G.obj (S.algebra.a.2 ⨯ S.algebra.a.2)) (ρ : ℕ → K),
  P (G.map S.implicationConstructor z) ρ ↔
    (P (G.map prod.fst z) ρ → P (G.map prod.snd z) ρ))
variable (hall : ∀ (z : G.obj (V ⨯ S.algebra.a.2)) (ρ : ℕ → K),
  P (G.map S.quantifierConstructor z) ρ ↔
    ∀ a : K, P (G.map prod.snd z)
      (Function.update ρ (name (G.map prod.fst z)) a))
variable (heq : ∀ (z : G.obj (S.algebra.a.1 ⨯ S.algebra.a.1)) (ρ : ℕ → K),
  P (G.map S.equalityConstructor z) ρ ↔
    eval (G.map prod.fst z) ρ = eval (G.map prod.snd z) ρ)

example (z : G.obj S.instantiationParameters) :
    ∀ ρ : ℕ → K, P (G.map S.hilbertInstantiation z) ρ :=
  valid_instantiation G S name eval P hsub himp hall z
example (z : G.obj S.equalitySchemeParameters) :
    ∀ ρ : ℕ → K, P (G.map S.hilbertEquality z) ρ :=
  valid_equality G S name eval P hsub himp heq z
end CategoricalEssentialIncompleteness.V46.ModelSubstitutionSoundnessChecks
