/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxTrace


/-! # Statement checks in `V46MillerSyntaxTraceChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
open CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y : Over R}
variable {p q : SyntaxPolynomial (Total.TotalCategory P)}
variable (hT : Raw.object R X Y p ⟶ X) (hF : Raw.object R X Y q ⟶ Y)

example (r word final : ℕ) :
    final ∈ Raw.evaluation hT hF (Nat.pair r word) ↔
      Raw.Trace hT hF r (Nat.natToList word) 1 final := Raw.evaluation_trace hT hF r word final

example {r : ℕ} {left right : List ℕ} {s t u : ℕ}
    (hl : Raw.Trace hT hF r left s t) (hr : Raw.Trace hT hF r right t u) :
    Raw.Trace hT hF r (left++right) s u := Raw.Trace.append hT hF hl hr

example {r : ℕ} {records : List ℕ} {s t : ℕ}
    (h : Raw.Trace hT hF r records s t) (ht : t≠0) (tail : ℕ) :
    Raw.Trace hT hF r records
      (SyntacticSyntax.Coding.frameStatus s tail) (SyntacticSyntax.Coding.frameStatus t tail) :=
  Raw.Trace.frame hT hF h ht tail

example {r : ℕ} {records : List ℕ} {s t u : ℕ}
    (ht : Raw.Trace hT hF r records s t) (hu : Raw.Trace hT hF r records s u) : t=u :=
  Raw.Trace.functional hT hF ht hu
