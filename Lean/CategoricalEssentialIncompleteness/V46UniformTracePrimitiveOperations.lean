/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalRiceShapiro.Evaluator.History
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPrimitiveVectors

/-! # Constructing standard primitive values for the arithmetic codes

Each closure theorem constructs a function, its `Code.eval` proof and its `Primrec`
certificate. No primitive certificate for the history evaluator is supplied as a
hypothesis of the eventual history theorem.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding

def PrimitiveTotal {n : ℕ} (c : Code n) : Prop :=
  ∃ f : List.Vector ℕ n → ℕ, Computes c f ∧ Primrec f

namespace PrimitiveTotal

theorem zero (n : ℕ) : PrimitiveTotal (Code.zero n) :=
  ⟨fun _ => 0, computes_zero, Primrec.const 0⟩

theorem one (n : ℕ) : PrimitiveTotal (Code.one n) :=
  ⟨fun _ => 1, computes_one, Primrec.const 1⟩

theorem const (n m : ℕ) : PrimitiveTotal (codeConst (n := n) m) :=
  ⟨fun _ => m, computes_codeConst m, Primrec.const m⟩

theorem proj {n : ℕ} (i : Fin n) : PrimitiveTotal (Code.proj i) :=
  ⟨fun v => v.get i, computes_proj i, Primrec.vector_get.comp Primrec.id (Primrec.const i)⟩

theorem comp {m n : ℕ} {c : Code m} {d : Fin m → Code n}
    (hc : PrimitiveTotal c) (hd : ∀ i, PrimitiveTotal (d i)) :
    PrimitiveTotal (c.comp d) := by
  classical
  obtain ⟨f, hcf, hpf⟩ := hc
  choose g hcg hpg using hd
  exact ⟨fun v => f (List.Vector.ofFn fun i => g i v),
    computes_comp hcf hcg, hpf.comp (Primrec.vector_ofFn hpg)⟩

theorem lift {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeLift c) :=
  comp hc (fun i => proj i.succ)

theorem bind {n : ℕ} {c : Code n} {d : Code (n + 1)}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) : PrimitiveTotal (codeBind c d) := by
  apply comp hd
  intro i
  exact Fin.cases hc (fun j => proj j) i

theorem succ {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeSucc c) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  exact ⟨fun v => f v + 1, computes_codeSucc hcf, Primrec.succ.comp hpf⟩

theorem add {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeAdd c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  exact ⟨fun v => f v + g v, computes_codeAdd hcf hcg, Primrec.nat_add.comp hpf hpg⟩

theorem mul {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeMul c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  exact ⟨fun v => f v * g v, computes_codeMul hcf hcg, Primrec.nat_mul.comp hpf hpg⟩

theorem sub {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeSub c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  exact ⟨fun v => f v - g v, computes_codeSub hcf hcg, Primrec.nat_sub.comp hpf hpg⟩

theorem rem {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeRem c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  exact ⟨fun v => f v % g v, computes_codeRem hcf hcg, Primrec.nat_mod.comp hpf hpg⟩

theorem unpair1 {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeUnpair₁ c) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  exact ⟨fun v => (f v).unpair.1, computes_codeUnpair₁ hcf,
    Primrec.fst.comp (Primrec.unpair.comp hpf)⟩

theorem unpair2 {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeUnpair₂ c) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  exact ⟨fun v => (f v).unpair.2, computes_codeUnpair₂ hcf,
    Primrec.snd.comp (Primrec.unpair.comp hpf)⟩

theorem eq {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeEq c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  refine ⟨fun v => isEqNat (f v) (g v), computes_codeEq hcf hcg, ?_⟩
  exact Primrec.ite (Primrec.eq.comp hpf hpg) (Primrec.const 1) (Primrec.const 0)

theorem lt {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codeLt c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  refine ⟨fun v => isLtNat (f v) (g v), computes_codeLt hcf hcg, ?_⟩
  exact Primrec.ite (Primrec.nat_lt.comp hpf hpg) (Primrec.const 1) (Primrec.const 0)

theorem ifPos {n : ℕ} {c d e : Code n}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) (he : PrimitiveTotal e) :
    PrimitiveTotal (codeIfPos c d e) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  obtain ⟨h, hch, hph⟩ := he
  exact ⟨fun v => if 0 < f v then g v else h v, computes_codeIfPos hcf hcg hch,
    Primrec.ite (Primrec.nat_lt.comp (Primrec.const 0) hpf) hpg hph⟩

theorem pair {n : ℕ} {c d : Code n} (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) :
    PrimitiveTotal (codePair c d) :=
  ifPos (lt hc hd) (add (mul hd hd) hc) (add (add (mul hc hc) hc) hd)

/-- Primitive recursion is certified from its nil and step computations. The arithmetic
code still contains its beta-history search; the existing computation theorem proves
that it performs this fold. -/
theorem prec {n : ℕ} {c : Code n} {d : Code (n + 2)}
    (hc : PrimitiveTotal c) (hd : PrimitiveTotal d) : PrimitiveTotal (codePrec c d) := by
  obtain ⟨f, hcf, hpf⟩ := hc
  obtain ⟨g, hcg, hpg⟩ := hd
  have hargs : Primrec (fun p : List.Vector ℕ n × (ℕ × ℕ) => p.2.1 ::ᵥ p.2.2 ::ᵥ p.1) :=
    Primrec.vector_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.vector_cons.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
  have hs : Primrec₂ (fun v (t : ℕ × ℕ) => g (t.1 ::ᵥ t.2 ::ᵥ v)) :=
    hpg.comp hargs
  exact ⟨fun v => v.head.rec (f v.tail) (fun i prev => g (i ::ᵥ prev ::ᵥ v.tail)),
    computes_codePrec hcf hcg, (Primrec.nat_rec hpf hs).comp Primrec.vector_tail Primrec.vector_head⟩

theorem bodd {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeBodd c) :=
  rem hc (const n 2)

theorem div2Unary : PrimitiveTotal codeDiv2Unary :=
  prec (zero 0) (ifPos (bodd (proj 0)) (succ (proj 1)) (proj 1))

theorem div2 {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codeDiv2 c) := by
  apply comp div2Unary
  intro i
  fin_cases i
  exact hc

theorem partrecTag {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) : PrimitiveTotal (codePartrecTag c) :=
  ifPos (lt hc (const n 4)) hc
    (add (add (const n 4) (mul (const n 2) (bodd (sub hc (const n 4)))))
      (bodd (div2 (sub hc (const n 4)))))

theorem partrecPayload {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codePartrecPayload c) := div2 (div2 (sub hc (const n 4)))

theorem partrecPayload1 {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codePartrecPayload₁ c) := unpair1 (partrecPayload hc)

theorem partrecPayload2 {n : ℕ} {c : Code n} (hc : PrimitiveTotal c) :
    PrimitiveTotal (codePartrecPayload₂ c) := unpair2 (partrecPayload hc)

end PrimitiveTotal
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding
