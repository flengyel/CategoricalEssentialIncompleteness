/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46UniformTracePrimitiveLists

/-! # The literal production history evaluator has a primitive native value

This is a closed derivation through the actual numeric cell, row and table
constructors. It assumes no primitive certificate for an evaluator, a trace
predicate, a program index, or a computation graph.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Nat Nat.ArithPart₁ CategoricalRiceShapiro.ArithmeticCode CategoricalRiceShapiro.Evaluator

namespace CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding
namespace PrimitiveTotal

theorem tableLookup {n : ℕ} {table k q input : Code n}
    (ht : PrimitiveTotal table) (hk : PrimitiveTotal k)
    (hq : PrimitiveTotal q) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codeTableLookup table k q input) :=
  sub (listGet (sub (listGet ht (pair hk hq)) (const n 1)) hi) (const n 1)

theorem baseCell {n : ℕ} {table input : Code n}
    (ht : PrimitiveTotal table) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codeBaseEvaluatorCell table input) := by
  have hk := unpair1 (listLength ht)
  have htag := partrecTag (unpair2 (listLength ht))
  exact ifPos hk
    (ifPos (eq htag (const n 0)) (const n 1)
      (ifPos (eq htag (const n 1)) (succ (succ hi))
        (ifPos (eq htag (const n 2)) (succ (unpair1 hi))
          (ifPos (eq htag (const n 3)) (succ (unpair2 hi)) (const n 0))))) (const n 0)

theorem pairCell {n : ℕ} {table k f g input : Code n}
    (ht : PrimitiveTotal table) (hk : PrimitiveTotal k) (hf : PrimitiveTotal f)
    (hg : PrimitiveTotal g) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codePairEvaluatorCell table k f g input) :=
  optionBind (tableLookup ht hk hf hi)
    (optionBind (tableLookup (lift ht) (lift hk) (lift hg) (lift hi))
      (succ (pair (proj 1) (proj 0))))

theorem compCell {n : ℕ} {table k f g input : Code n}
    (ht : PrimitiveTotal table) (hk : PrimitiveTotal k) (hf : PrimitiveTotal f)
    (hg : PrimitiveTotal g) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codeCompEvaluatorCell table k f g input) :=
  optionBind (tableLookup ht hk hg hi)
    (tableLookup (lift ht) (lift hk) (lift hf) (proj 0))

theorem precCell {n : ℕ} {table kp q f g input : Code n}
    (ht : PrimitiveTotal table) (hkp : PrimitiveTotal kp) (hq : PrimitiveTotal q)
    (hf : PrimitiveTotal f) (hg : PrimitiveTotal g) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codePrecEvaluatorCell table kp q f g input) := by
  have hk := succ hkp
  have hz := unpair1 hi
  have htime := unpair2 hi
  have hy := sub htime (const n 1)
  exact ifPos htime
    (optionBind (tableLookup ht hkp hq (pair hz hy))
      (tableLookup (lift ht) (lift hk) (lift hg)
        (pair (lift hz) (pair (lift hy) (proj 0)))))
    (tableLookup ht hk hf hz)

theorem rfindCell {n : ℕ} {table kp q f input : Code n}
    (ht : PrimitiveTotal table) (hkp : PrimitiveTotal kp) (hq : PrimitiveTotal q)
    (hf : PrimitiveTotal f) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codeRfindEvaluatorCell table kp q f input) := by
  have hk := succ hkp
  have hz := unpair1 hi
  have hm := unpair2 hi
  exact optionBind (tableLookup ht hk hf (pair hz hm))
    (ifPos (proj 0)
      (tableLookup (lift ht) (lift hkp) (lift hq) (pair (lift hz) (succ (lift hm))))
      (succ (lift hm)))

theorem evaluatorCell {n : ℕ} {table input : Code n}
    (ht : PrimitiveTotal table) (hi : PrimitiveTotal input) :
    PrimitiveTotal (codeEvaluatorCell table input) := by
  have hlen := listLength ht
  have hk := unpair1 hlen
  have hkp := sub hk (const n 1)
  have hq := unpair2 hlen
  have htag := partrecTag hq
  have hf := partrecPayload1 hq
  have hg := partrecPayload2 hq
  have hrfind := partrecPayload hq
  exact ifPos hk
    (ifPos (eq htag (const n 4)) (pairCell ht hk hf hg hi)
      (ifPos (eq htag (const n 5)) (compCell ht hk hf hg hi)
        (ifPos (eq htag (const n 6)) (precCell ht hkp hq hf hg hi)
          (ifPos (eq htag (const n 7)) (rfindCell ht hkp hq hrfind hi) (baseCell ht hi)))))
    (const n 0)

theorem rowCore {n : ℕ} {table : Code n} (ht : PrimitiveTotal table) :
    PrimitiveTotal (codeEvaluatorRowCore table) :=
  prec (listNil n)
    (listCons (evaluatorCell (lift (lift ht))
      (sub (unpair1 (listLength (lift (lift ht)))) (succ (proj 0)))) (proj 1))

theorem row {n : ℕ} {table : Code n} (ht : PrimitiveTotal table) :
    PrimitiveTotal (codeEvaluatorRow table) := bind (unpair1 (listLength ht)) (rowCore ht)

theorem tableStep {n : ℕ} {table : Code n} (ht : PrimitiveTotal table) :
    PrimitiveTotal (codeEvaluatorTableStep table) := listSnoc ht (row ht)

theorem evaluatorHistory : PrimitiveTotal codeEvaluatorHistory :=
  prec (listNil 0) (tableStep (proj 1))

/-- The actual closed production interpreter is primitive recursive at
each bounded stage. Its program index and input remain arbitrary numbers. -/
theorem historyEvaluator : PrimitiveTotal codeHistoryEvaluator := by
  have hh : PrimitiveTotal (codeEvaluatorHistory.comp
      ![codeSucc (codePair (Code.proj (0 : Fin 3)) (Code.proj (1 : Fin 3)))]) := by
    apply comp evaluatorHistory
    intro i
    fin_cases i
    exact succ (pair (proj 0) (proj 1))
  exact tableLookup hh (proj 0) (proj 1) (proj 2)

end PrimitiveTotal
end CategoricalEssentialIncompleteness.V46.UniformTrace.PrimitiveCoding
