/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerUniformComputations


/-! # Statement checks in `V46MillerUniformComputationsChecks` -/

@[expose] public section
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
open OracleComputation (Ty)

example (z : Point) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented (Family.ofPoint z) X Y f ↔
      ∃ e : ℕ,∀ p ∈ representations z,∀ x y,
        y ∈ f x ↔ Y.toNat y ∈ OracleProgram.numberedEval e p (X.toNat x) := Iff.rfl

example {α : Type} [Primcodable α] (Q : α × ℕ → Prop) (hQ : REPred Q) :
    Partrec (positiveChoice Q hQ) := positiveChoice_partrec Q hQ
example {α : Type} [Primcodable α] (Q : α × ℕ → Prop) (hQ : REPred Q)
    (a : α) (y : ℕ) (hy : y ∈ positiveChoice Q hQ a) : Q (a,y) :=
  positiveChoice_sound Q hQ a y hy
example {α : Type} [Primcodable α] (Q : α × ℕ → Prop) (hQ : REPred Q) (a : α) :
    (positiveChoice Q hQ a).Dom ↔ ∃ y,Q (a,y) := positiveChoice_domain Q hQ a

example (z : Family) (f : ℕ → Part ℕ) :
    Numerical z f ↔ ∃ e : ℕ,∀ p ∈ z.oracles,∀ n y,
      y ∈ f n ↔ y ∈ OracleProgram.numberedEval e p n := Iff.rfl
example (z : Family) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented z X Y f ↔ ∃ e : ℕ,∀ p ∈ z.oracles,∀ x y,
      y ∈ f x ↔ Y.toNat y ∈ OracleProgram.numberedEval e p (X.toNat x) := Iff.rfl
example (z : Family) (f : ℕ → Part ℕ) :
    Numerical z f ↔ Enumerable z (fun a : ℕ × ℕ => a.2 ∈ f a.1) :=
  numerical_iff_graph_enumerable z f
example (z : Family) (X Y : Ty) (f : X.carrier → Part Y.carrier) :
    Represented z X Y f ↔ Enumerable z (fun a : X.carrier × Y.carrier => a.2 ∈ f a.1) :=
  represented_iff_graph_enumerable z X Y f

example {z : Family} {X Y Z : Ty} {f : X.carrier → Part Y.carrier}
    {g : Y.carrier → Part Z.carrier} (hf : Represented z X Y f) (hg : Represented z Y Z g) :
    Represented z X Z (fun x => (f x).bind g) := Represented.comp hf hg
example {z : Family} {X Y : Ty} {f : X.carrier → Part Y.carrier} (hf : Represented z X Y f) :
    Enumerable z (fun y => ∃ x,y ∈ f x) := hf.image
example {z : Family} {X Y : Ty} {f : X.carrier → Part Y.carrier} (hf : Represented z X Y f) :
    Enumerable z (fun x => (f x).Dom) := hf.domain
example {z : Family} (X : Ty) (A : Set X.carrier) (hA : Enumerable z (· ∈ A)) :
    Represented z X X (fun x => Part.assert (x ∈ A) (fun _ => Part.some x)) :=
  Represented.identityOn X A hA
example {z : Family} {W X Y : Ty} {f : W.carrier → Part X.carrier}
    {g : W.carrier → Part Y.carrier} (hf : Represented z W X f) (hg : Represented z W Y g) :
    Represented z W (.product X Y) (fun w => (f w).bind (fun x => (g w).map (Prod.mk x))) :=
  Represented.pair hf hg
example {z : Family} {X Y Z : Ty} {f : X.carrier → Part Z.carrier}
    {g : Y.carrier → Part Z.carrier} (hf : Represented z X Z f) (hg : Represented z Y Z g) :
    Represented z (.coproduct X Y) Z (Sum.elim f g) := Represented.sum hf hg
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
