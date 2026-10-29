/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Metamath.Feferman.MPSequence

/-!
# Natural-number codes for formulas and proof sequences

`MPSequence.lean` defines finite strings and proof sequences with modus ponens
as the sole inference rule. This module gives a bijection between `ℕ` and
`List ℕ`, applies it to formula strings and proof sequences, and defines
numerical implication, modus ponens, and a proof predicate by decoding.

## Pairing

The pairing is a bit-interleaving bijection. `bitSpread` sends the binary
digit in position `i` to position `2 * i`; `codePair a b` places the digits of
`a` in the even positions and those of `b` in the odd positions. `codeUnpair`
recovers both coordinates.

```
bitSpread 0       = 0
bitSpread (n + 1) = (n + 1) % 2 + 4 * bitSpread ((n + 1) / 2)

codePair a b = bitSpread a + 2 * bitSpread b

codeUnpair 0       = (0, 0)
codeUnpair (n + 1) = (2 * (codeUnpair ((n + 1) / 4)).1 + (n + 1) % 2,
                      2 * (codeUnpair ((n + 1) / 4)).2 + ((n + 1) / 2) % 2)
```

The recursive arguments decrease by division by two and four, respectively.
Thus `codeUnpair` takes one recursive step per pair of binary digits.
`codePair_codeUnpair` and `codeUnpair_codePair` prove the inverse laws.
`codeUnpair_right_le` supplies the bound used to prove termination of
`listDecode`.

## List coding

```
listEncode []        = 0
listEncode (x :: xs) = codePair x (listEncode xs) + 1

listDecode 0       = []
listDecode (n + 1) = (codeUnpair n).1 :: listDecode (codeUnpair n).2
```

`listDecode` is defined by well-founded recursion on `n`.
`listDecode_listEncode` and `listEncode_listDecode` prove that the two functions
are mutually inverse. Every natural number therefore codes one finite token
list. The `formula` predicate of a `SyntaxPresentation` determines whether the
decoded list is a formula.

`FormulaCode` and `ProofSequenceCode` are abbreviations for `ℕ`.
Their decoders distinguish the intended interpretations: `decodeFormula`
yields a `FormulaString`, whereas `decodeProof` yields a `ProofSequence`.
In particular, `encodeProof [] ≠ encodeProof [[]]` distinguishes an empty proof
sequence from a sequence containing the empty formula string.

## Numerical proof predicate and arithmetic representation

`Proof_T Th p a` relates a proof-sequence code `p` to a formula code `a`.
The theorem `proof_T_mp` states that if `p` codes a proof of `a` and `r` codes
a proof of `imp a b`, then `mp r p` codes a proof of `b`.
`primrecRel_proof_T` establishes primitive recursiveness for a
`PRTheoryPresentation`.

These are external statements about numerical codes. The separate `Arith`
root defines the arithmetic formula `proofTFormula` and proves standard-model
adequacy and numeralwise weak representation. A uniform object-language
preservation theorem, quantified over free proof and formula codes, is not
provided. This module does not construct Feferman's `Fm_K` or `Ax_K`, implement
`Sb` or `SSb`, or perform Craig conversion.

## Axiom dependencies

The computational definitions, the inverse laws, `Proof_T`, and `proof_T_mp`
do not depend on `Classical.choice`. Their arithmetic dependencies include
`Nat.div_lt_self`, `Nat.mod_add_div`, and `Nat.div_div_eq_div_mul`; these and the
`omega` proofs use only `propext` and `Quot.sound`.

The thirteen `Primrec` certificates depend on Mathlib declarations that use
`Classical.choice`. `check_metamath_axioms.lean` records the declaration
dependencies. This observation does not establish that the dependency is
necessary.

## Mathlib declarations used

`Nat.div_lt_self`, `Nat.mod_add_div`, `Nat.div_div_eq_div_mul`,
`Primrec.list_foldr`, `Primrec.nat_strong_rec`, `Primrec.list_map`,
`Primrec.nat_casesOn`, `Primrec.list_getD`, `Primrec.nat_div`,
`Primrec.nat_mod`, `Primrec.nat_add`, and `Primrec.nat_mul`.
-/

namespace Metamath.Feferman

/-! ### Codes -/

/-- The code of a formula string. Underlying type `ℕ`; decoded by
`decodeFormula`. -/
abbrev FormulaCode := ℕ

/-- The code of a proof sequence. Underlying type `ℕ`; decoded by
`decodeProof`. -/
abbrev ProofSequenceCode := ℕ

/-! ### A bit-interleaving pairing -/

/-- Spread the binary digits of `n` into the even positions: the digit in
position `i` moves to position `2 * i`. -/
def bitSpread : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + 4 * bitSpread ((n + 1) / 2)
  decreasing_by omega

/-- Interleave the binary digits of `a` and `b`: those of `a` occupy the even
positions and those of `b` the odd positions. -/
def codePair (a b : ℕ) : ℕ := bitSpread a + 2 * bitSpread b

/-- Read the interleaved digits back. The recursion is at `n / 4`, so it takes
one step per pair of binary digits. -/
def codeUnpair : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      (2 * (codeUnpair ((n + 1) / 4)).1 + (n + 1) % 2,
        2 * (codeUnpair ((n + 1) / 4)).2 + ((n + 1) / 2) % 2)
  decreasing_by all_goals omega

@[simp] theorem bitSpread_zero : bitSpread 0 = 0 := by rw [bitSpread]

@[simp] theorem codeUnpair_zero : codeUnpair 0 = (0, 0) := by rw [codeUnpair]

/-- The defining recurrence of `bitSpread`, valid at every `n` including `0`. -/
theorem bitSpread_eq (n : ℕ) : bitSpread n = n % 2 + 4 * bitSpread (n / 2) := by
  cases n with
  | zero => simp
  | succ m => rw [bitSpread]

/-- The first component of the `codeUnpair` recurrence, valid at every `n`. -/
theorem codeUnpair_fst (n : ℕ) :
    (codeUnpair n).1 = 2 * (codeUnpair (n / 4)).1 + n % 2 := by
  cases n with
  | zero => simp
  | succ m => rw [codeUnpair]

/-- The second component of the `codeUnpair` recurrence, valid at every `n`. -/
theorem codeUnpair_snd (n : ℕ) :
    (codeUnpair n).2 = 2 * (codeUnpair (n / 4)).2 + (n / 2) % 2 := by
  cases n with
  | zero => simp
  | succ m => rw [codeUnpair]

@[simp] theorem codePair_zero_zero : codePair 0 0 = 0 := by simp [codePair]

/-- The paired recurrence: one binary digit of each argument is consumed per
step. -/
theorem codePair_eq (a b : ℕ) :
    codePair a b = a % 2 + 2 * (b % 2) + 4 * codePair (a / 2) (b / 2) := by
  rw [codePair, codePair, bitSpread_eq a, bitSpread_eq b]
  omega

/-- Spreading the binary digits of `n` cannot decrease it. -/
theorem le_bitSpread (n : ℕ) : n ≤ bitSpread n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h := ih (n / 2) (by omega)
      rw [bitSpread_eq n]
      omega

/-- `codeUnpair` is a right inverse of `codePair`. Proved by strong induction
on `n`, consuming two binary digits per step. -/
@[simp] theorem codePair_codeUnpair (n : ℕ) :
    codePair (codeUnpair n).1 (codeUnpair n).2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hih : codePair (codeUnpair (n / 4)).1 (codeUnpair (n / 4)).2 = n / 4 :=
        ih (n / 4) (by omega)
      have h1 : bitSpread (2 * (codeUnpair (n / 4)).1 + n % 2)
          = n % 2 + 4 * bitSpread (codeUnpair (n / 4)).1 := by
        rw [bitSpread_eq (2 * (codeUnpair (n / 4)).1 + n % 2)]
        have e1 : (2 * (codeUnpair (n / 4)).1 + n % 2) % 2 = n % 2 := by omega
        have e2 : (2 * (codeUnpair (n / 4)).1 + n % 2) / 2
            = (codeUnpair (n / 4)).1 := by omega
        rw [e1, e2]
      have h2 : bitSpread (2 * (codeUnpair (n / 4)).2 + (n / 2) % 2)
          = (n / 2) % 2 + 4 * bitSpread (codeUnpair (n / 4)).2 := by
        rw [bitSpread_eq (2 * (codeUnpair (n / 4)).2 + (n / 2) % 2)]
        have e1 : (2 * (codeUnpair (n / 4)).2 + (n / 2) % 2) % 2
            = (n / 2) % 2 := by omega
        have e2 : (2 * (codeUnpair (n / 4)).2 + (n / 2) % 2) / 2
            = (codeUnpair (n / 4)).2 := by omega
        rw [e1, e2]
      rw [codePair] at hih ⊢
      rw [codeUnpair_fst n, codeUnpair_snd n, h1, h2]
      omega

private theorem codeUnpair_codePair_aux :
    ∀ s a b, a + b ≤ s → codeUnpair (codePair a b) = (a, b) := by
  intro s
  induction s with
  | zero =>
    intro a b h
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb; simp
  | succ k ih =>
    intro a b h
    rcases Nat.eq_zero_or_pos (a + b) with h0 | hpos
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst ha; subst hb; simp
    · have hrec := codePair_eq a b
      have e0 : codePair a b % 2 = a % 2 := by omega
      have e1 : codePair a b / 2 % 2 = b % 2 := by omega
      have e2 : codePair a b / 4 = codePair (a / 2) (b / 2) := by omega
      have hih : codeUnpair (codePair (a / 2) (b / 2)) = (a / 2, b / 2) :=
        ih (a / 2) (b / 2) (by omega)
      have hfst : (codeUnpair (codePair a b)).1 = a := by
        rw [codeUnpair_fst, e2, hih, e0]; omega
      have hsnd : (codeUnpair (codePair a b)).2 = b := by
        rw [codeUnpair_snd, e2, hih, e1]; omega
      exact Prod.ext hfst hsnd

/-- `codeUnpair` is a left inverse of `codePair`. Proved by induction on a
bound for `a + b`, with `(0, 0)` treated separately. -/
@[simp] theorem codeUnpair_codePair (a b : ℕ) :
    codeUnpair (codePair a b) = (a, b) :=
  codeUnpair_codePair_aux (a + b) a b le_rfl

/-- The right coordinate is bounded by the code. This discharges the
termination obligation of `listDecode`. -/
theorem codeUnpair_right_le (n : ℕ) : (codeUnpair n).2 ≤ n := by
  have h := codePair_codeUnpair n
  have hb := le_bitSpread (codeUnpair n).2
  rw [codePair] at h
  omega

theorem codeUnpair_left_le (n : ℕ) : (codeUnpair n).1 ≤ n := by
  have h := codePair_codeUnpair n
  have ha := le_bitSpread (codeUnpair n).1
  rw [codePair] at h
  omega

/-! ### The list coding -/

/-- Encode a finite token list. `0` codes the empty list; a nonempty list is
coded by `codePair` of its head with the code of its tail, shifted by one so
that `0` is not reused. -/
def listEncode : List ℕ → ℕ
  | [] => 0
  | x :: xs => codePair x (listEncode xs) + 1

/-- Decode a natural number to a finite token list. Total, by well-founded
recursion on the argument; the recursive call is at `(codeUnpair n).2`, which
`codeUnpair_right_le` bounds by `n`. -/
def listDecode : ℕ → List ℕ
  | 0 => []
  | n + 1 => (codeUnpair n).1 :: listDecode (codeUnpair n).2
  decreasing_by exact Nat.lt_succ_of_le (codeUnpair_right_le n)

@[simp] theorem listEncode_nil : listEncode [] = 0 := rfl

@[simp] theorem listEncode_cons (x : ℕ) (xs : List ℕ) :
    listEncode (x :: xs) = codePair x (listEncode xs) + 1 := rfl

@[simp] theorem listDecode_zero : listDecode 0 = [] := by
  rw [listDecode]

@[simp] theorem listDecode_succ (n : ℕ) :
    listDecode (n + 1) = (codeUnpair n).1 :: listDecode (codeUnpair n).2 := by
  rw [listDecode]

/-- `listDecode` inverts `listEncode`. -/
@[simp] theorem listDecode_listEncode (xs : List ℕ) :
    listDecode (listEncode xs) = xs := by
  induction xs with
  | nil => rw [listEncode_nil, listDecode_zero]
  | cons x xs ih =>
    rw [listEncode_cons, listDecode_succ, codeUnpair_codePair, ih]

/-- `listEncode` inverts `listDecode`. With `listDecode_listEncode` this states
that the two functions are mutually inverse bijections, so every natural number
is the code of exactly one finite token list. -/
@[simp] theorem listEncode_listDecode (n : ℕ) :
    listEncode (listDecode n) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [listDecode_zero, listEncode_nil]
    | succ m =>
      rw [listDecode_succ, listEncode_cons,
        ih (codeUnpair m).2 (Nat.lt_succ_of_le (codeUnpair_right_le m)),
        codePair_codeUnpair]

theorem listEncode_injective : Function.Injective listEncode := by
  intro xs ys h
  rw [← listDecode_listEncode xs, ← listDecode_listEncode ys, h]

theorem listDecode_injective : Function.Injective listDecode := by
  intro m n h
  rw [← listEncode_listDecode m, ← listEncode_listDecode n, h]

/-! ### Codes of formula strings and of proof sequences -/

/-- The code of a candidate formula string. -/
def encodeFormula (φ : FormulaString) : FormulaCode := listEncode φ

/-- The candidate formula string coded by a natural number. Total. -/
def decodeFormula (a : FormulaCode) : FormulaString := listDecode a

/-- The code of a proof sequence: encode each line, then encode the resulting
list of codes. -/
def encodeProof (Ψ : ProofSequence) : ProofSequenceCode :=
  listEncode (Ψ.map encodeFormula)

/-- The proof sequence coded by a natural number. Total. -/
def decodeProof (p : ProofSequenceCode) : ProofSequence :=
  (listDecode p).map decodeFormula

@[simp] theorem decodeFormula_encodeFormula (φ : FormulaString) :
    decodeFormula (encodeFormula φ) = φ := listDecode_listEncode φ

@[simp] theorem encodeFormula_decodeFormula (a : FormulaCode) :
    encodeFormula (decodeFormula a) = a := listEncode_listDecode a

@[simp] theorem decodeProof_encodeProof (Ψ : ProofSequence) :
    decodeProof (encodeProof Ψ) = Ψ := by
  rw [decodeProof, encodeProof, listDecode_listEncode, List.map_map]
  have hcomp : (decodeFormula ∘ encodeFormula) = id := by
    funext φ; exact decodeFormula_encodeFormula φ
  rw [hcomp, List.map_id]

@[simp] theorem encodeProof_decodeProof (p : ProofSequenceCode) :
    encodeProof (decodeProof p) = p := by
  rw [encodeProof, decodeProof, List.map_map]
  have : (encodeFormula ∘ decodeFormula) = id := by
    funext a; exact encodeFormula_decodeFormula a
  rw [this, List.map_id, listEncode_listDecode]

theorem encodeFormula_injective : Function.Injective encodeFormula := by
  intro φ ψ h
  have h' := congrArg decodeFormula h
  rwa [decodeFormula_encodeFormula, decodeFormula_encodeFormula] at h'

theorem encodeProof_injective : Function.Injective encodeProof := by
  intro Ψ Φ h
  have h' := congrArg decodeProof h
  rwa [decodeProof_encodeProof, decodeProof_encodeProof] at h'

/-- The empty proof sequence and the one-line sequence whose single line is the
empty candidate string have different codes: the nesting is not collapsed. -/
theorem encodeProof_nil_ne_encodeProof_nil_nil :
    encodeProof [] ≠ encodeProof [[]] := by decide

/-! ### Numerical implication and modus ponens -/

/-- The code of the implication with the given coded antecedent and
consequent. -/
def imp (a b : FormulaCode) : FormulaCode :=
  encodeFormula (impString (decodeFormula a) (decodeFormula b))

/-- The coded antecedent of a coded implication. Total, with the behaviour of
`lhsString` on malformed input. -/
def lhs (s : FormulaCode) : FormulaCode :=
  encodeFormula (lhsString (decodeFormula s))

/-- The coded consequent of a coded implication. Total, with the behaviour of
`rhsString` on malformed input. -/
def rhs (s : FormulaCode) : FormulaCode :=
  encodeFormula (rhsString (decodeFormula s))

/-- The numerical modus-ponens transformation. The argument order is fixed:
`r` codes a proof of the implication and `p` codes a proof of its antecedent. -/
def mp (r p : ProofSequenceCode) : ProofSequenceCode :=
  encodeProof (mpList (decodeProof r) (decodeProof p))

@[simp] theorem decodeFormula_imp (a b : FormulaCode) :
    decodeFormula (imp a b) = impString (decodeFormula a) (decodeFormula b) := by
  rw [imp, decodeFormula_encodeFormula]

@[simp] theorem lhs_imp (a b : FormulaCode) : lhs (imp a b) = a := by
  rw [lhs, decodeFormula_imp, lhsString_impString, encodeFormula_decodeFormula]

@[simp] theorem rhs_imp (a b : FormulaCode) : rhs (imp a b) = b := by
  rw [rhs, decodeFormula_imp, rhsString_impString, encodeFormula_decodeFormula]

@[simp] theorem decodeProof_mp (r p : ProofSequenceCode) :
    decodeProof (mp r p) = mpList (decodeProof r) (decodeProof p) := by
  rw [mp, decodeProof_encodeProof]

/-- `imp` is injective in both arguments, derived from the accessor equations
and the two-sided coding laws. -/
theorem imp_inj {a b a' b' : FormulaCode} :
    imp a b = imp a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    exact ⟨by rw [← lhs_imp a b, h, lhs_imp], by rw [← rhs_imp a b, h, rhs_imp]⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ### Primitive recursiveness of the coding

Each of the three recursions below is certified through
`Primrec.nat_strong_rec`. The history supplied at stage `n` is
`[f 0, …, f (n - 1)]`, so its length is `n`; the earlier value the recurrence
needs is retrieved by `List.getD` at an index that the strict decrease of the
recursion places inside that history. -/

/-- The history lookup used by all three strong-recursion certificates. -/
private theorem getD_map_range {σ : Type} (f : ℕ → σ) (n k : ℕ) (h : k < n)
    (d : σ) : ((List.range n).map f).getD k d = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simpa using h)]
  rfl

/-! #### `bitSpread` -/

private def spreadStep (H : List ℕ) : Option ℕ :=
  Nat.casesOn H.length (some 0)
    fun m => some ((m + 1) % 2 + 4 * H.getD ((m + 1) / 2) 0)

private theorem primrec_spreadStep : Primrec spreadStep := by
  have hstep : Primrec₂ fun (H : List ℕ) (m : ℕ) =>
      some ((m + 1) % 2 + 4 * H.getD ((m + 1) / 2) 0) := by
    have hs : Primrec fun x : List ℕ × ℕ => x.2 + 1 :=
      Primrec.succ.comp Primrec.snd
    have hmod : Primrec fun x : List ℕ × ℕ => (x.2 + 1) % 2 :=
      Primrec.nat_mod.comp hs (Primrec.const 2)
    have hdiv : Primrec fun x : List ℕ × ℕ => (x.2 + 1) / 2 :=
      Primrec.nat_div.comp hs (Primrec.const 2)
    have hget : Primrec fun x : List ℕ × ℕ => x.1.getD ((x.2 + 1) / 2) 0 :=
      (Primrec.list_getD 0).comp Primrec.fst hdiv
    have hmul : Primrec fun x : List ℕ × ℕ => 4 * x.1.getD ((x.2 + 1) / 2) 0 :=
      Primrec.nat_mul.comp (Primrec.const 4) hget
    exact (Primrec.option_some.comp (Primrec.nat_add.comp hmod hmul)).to₂
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const _) hstep

private theorem spreadStep_history (n : ℕ) :
    spreadStep ((List.range n).map bitSpread) = some (bitSpread n) := by
  cases n with
  | zero => simp [spreadStep]
  | succ m =>
    have hlen : ((List.range (m + 1)).map bitSpread).length = m + 1 := by simp
    have hget : ((List.range (m + 1)).map bitSpread).getD ((m + 1) / 2) 0
        = bitSpread ((m + 1) / 2) :=
      getD_map_range bitSpread (m + 1) ((m + 1) / 2) (by omega) 0
    unfold spreadStep
    rw [hlen]
    change some ((m + 1) % 2
      + 4 * ((List.range (m + 1)).map bitSpread).getD ((m + 1) / 2) 0) = _
    rw [hget, bitSpread_eq (m + 1)]

theorem primrec_bitSpread : Primrec bitSpread := by
  have h : Primrec₂ fun (_ : Unit) (n : ℕ) => bitSpread n :=
    Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => bitSpread n)
      (primrec_spreadStep.comp Primrec.snd).to₂
      fun _ n => spreadStep_history n
  exact Primrec₂.comp h (Primrec.const ()) Primrec.id

theorem primrec_codePair : Primrec₂ codePair := by
  have h : Primrec fun x : ℕ × ℕ => bitSpread x.1 + 2 * bitSpread x.2 :=
    Primrec.nat_add.comp (primrec_bitSpread.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (primrec_bitSpread.comp Primrec.snd))
  exact h.to₂

/-! #### `codeUnpair` -/

private def unpairStep (H : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  Nat.casesOn H.length (some ((0, 0) : ℕ × ℕ))
    fun m => some (2 * (H.getD ((m + 1) / 4) (0, 0)).1 + (m + 1) % 2,
      2 * (H.getD ((m + 1) / 4) (0, 0)).2 + ((m + 1) / 2) % 2)

private theorem primrec_unpairStep : Primrec unpairStep := by
  have hstep : Primrec₂ fun (H : List (ℕ × ℕ)) (m : ℕ) =>
      some (2 * (H.getD ((m + 1) / 4) (0, 0)).1 + (m + 1) % 2,
        2 * (H.getD ((m + 1) / 4) (0, 0)).2 + ((m + 1) / 2) % 2) := by
    have hs : Primrec fun x : List (ℕ × ℕ) × ℕ => x.2 + 1 :=
      Primrec.succ.comp Primrec.snd
    have hq : Primrec fun x : List (ℕ × ℕ) × ℕ =>
        x.1.getD ((x.2 + 1) / 4) (0, 0) :=
      (Primrec.list_getD (0, 0)).comp Primrec.fst
        (Primrec.nat_div.comp hs (Primrec.const 4))
    have hd2 : Primrec fun x : List (ℕ × ℕ) × ℕ => (x.2 + 1) / 2 :=
      Primrec.nat_div.comp hs (Primrec.const 2)
    have hfst : Primrec fun x : List (ℕ × ℕ) × ℕ =>
        2 * (x.1.getD ((x.2 + 1) / 4) (0, 0)).1 + (x.2 + 1) % 2 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp hq))
        (Primrec.nat_mod.comp hs (Primrec.const 2))
    have hsnd : Primrec fun x : List (ℕ × ℕ) × ℕ =>
        2 * (x.1.getD ((x.2 + 1) / 4) (0, 0)).2 + ((x.2 + 1) / 2) % 2 :=
      Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp hq))
        (Primrec.nat_mod.comp hd2 (Primrec.const 2))
    exact (Primrec.option_some.comp (Primrec.pair hfst hsnd)).to₂
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const _) hstep

private theorem unpairStep_history (n : ℕ) :
    unpairStep ((List.range n).map codeUnpair) = some (codeUnpair n) := by
  cases n with
  | zero => simp [unpairStep]
  | succ m =>
    have hlen : ((List.range (m + 1)).map codeUnpair).length = m + 1 := by simp
    have hget : ((List.range (m + 1)).map codeUnpair).getD ((m + 1) / 4) (0, 0)
        = codeUnpair ((m + 1) / 4) :=
      getD_map_range codeUnpair (m + 1) ((m + 1) / 4) (by omega) (0, 0)
    unfold unpairStep
    rw [hlen]
    change some (2 * (((List.range (m + 1)).map codeUnpair).getD
        ((m + 1) / 4) (0, 0)).1 + (m + 1) % 2,
      2 * (((List.range (m + 1)).map codeUnpair).getD
        ((m + 1) / 4) (0, 0)).2 + ((m + 1) / 2) % 2) = _
    rw [hget, ← codeUnpair_fst (m + 1), ← codeUnpair_snd (m + 1)]

theorem primrec_codeUnpair : Primrec codeUnpair := by
  have h : Primrec₂ fun (_ : Unit) (n : ℕ) => codeUnpair n :=
    Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => codeUnpair n)
      (primrec_unpairStep.comp Primrec.snd).to₂
      fun _ n => unpairStep_history n
  exact Primrec₂.comp h (Primrec.const ()) Primrec.id

/-! #### The list codec -/

private theorem listEncode_eq_foldr (xs : List ℕ) :
    listEncode xs = xs.foldr (fun x s => codePair x s + 1) 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [listEncode_cons, List.foldr_cons, ih]

theorem primrec_listEncode : Primrec listEncode := by
  have h : Primrec fun xs : List ℕ =>
      xs.foldr (fun x s => codePair x s + 1) 0 :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.succ.comp
        (Primrec₂.comp primrec_codePair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp Primrec.snd))).to₂
  exact h.of_eq fun xs => (listEncode_eq_foldr xs).symm

private def decodeStep (H : List (List ℕ)) : Option (List ℕ) :=
  Nat.casesOn H.length (some ([] : List ℕ))
    fun m => some ((codeUnpair m).1 :: H.getD (codeUnpair m).2 [])

private theorem primrec_decodeStep : Primrec decodeStep := by
  have hstep : Primrec₂ fun (H : List (List ℕ)) (m : ℕ) =>
      some ((codeUnpair m).1 :: H.getD (codeUnpair m).2 []) := by
    have hu : Primrec fun x : List (List ℕ) × ℕ => codeUnpair x.2 :=
      primrec_codeUnpair.comp Primrec.snd
    have hget : Primrec fun x : List (List ℕ) × ℕ =>
        x.1.getD (codeUnpair x.2).2 [] :=
      (Primrec.list_getD []).comp Primrec.fst (Primrec.snd.comp hu)
    exact (Primrec.option_some.comp
      (Primrec.list_cons.comp (Primrec.fst.comp hu) hget)).to₂
  exact Primrec.nat_casesOn Primrec.list_length (Primrec.const _) hstep

private theorem decodeStep_history (n : ℕ) :
    decodeStep ((List.range n).map listDecode) = some (listDecode n) := by
  cases n with
  | zero => simp [decodeStep]
  | succ m =>
    have hlen : ((List.range (m + 1)).map listDecode).length = m + 1 := by simp
    have hget : ((List.range (m + 1)).map listDecode).getD (codeUnpair m).2 []
        = listDecode (codeUnpair m).2 :=
      getD_map_range listDecode (m + 1) (codeUnpair m).2
        (Nat.lt_succ_of_le (codeUnpair_right_le m)) []
    unfold decodeStep
    rw [hlen]
    change some ((codeUnpair m).1 ::
      ((List.range (m + 1)).map listDecode).getD (codeUnpair m).2 []) = _
    rw [hget, listDecode_succ]

theorem primrec_listDecode : Primrec listDecode := by
  have h : Primrec₂ fun (_ : Unit) (n : ℕ) => listDecode n :=
    Primrec.nat_strong_rec (fun (_ : Unit) (n : ℕ) => listDecode n)
      (primrec_decodeStep.comp Primrec.snd).to₂
      fun _ n => decodeStep_history n
  exact Primrec₂.comp h (Primrec.const ()) Primrec.id


theorem primrec_encodeFormula : Primrec encodeFormula := primrec_listEncode

theorem primrec_decodeFormula : Primrec decodeFormula := primrec_listDecode

theorem primrec_encodeProof : Primrec encodeProof :=
  primrec_listEncode.comp
    (Primrec.list_map Primrec.id (primrec_encodeFormula.comp Primrec.snd).to₂)

theorem primrec_decodeProof : Primrec decodeProof :=
  Primrec.list_map primrec_listDecode
    (primrec_decodeFormula.comp Primrec.snd).to₂

/-! ### Primitive recursiveness of the numerical operations -/

theorem primrec_imp : Primrec₂ imp := by
  have hstr : Primrec fun x : FormulaCode × FormulaCode =>
      impString (decodeFormula x.1) (decodeFormula x.2) :=
    Primrec₂.comp primrec_impString (primrec_decodeFormula.comp Primrec.fst)
      (primrec_decodeFormula.comp Primrec.snd)
  exact (primrec_encodeFormula.comp hstr).to₂

theorem primrec_lhs : Primrec lhs :=
  primrec_encodeFormula.comp (primrec_lhsString.comp primrec_decodeFormula)

theorem primrec_rhs : Primrec rhs :=
  primrec_encodeFormula.comp (primrec_rhsString.comp primrec_decodeFormula)

theorem primrec_mp : Primrec₂ mp := by
  have hlist : Primrec fun x : ProofSequenceCode × ProofSequenceCode =>
      mpList (decodeProof x.1) (decodeProof x.2) :=
    Primrec₂.comp primrec_mpList (primrec_decodeProof.comp Primrec.fst)
      (primrec_decodeProof.comp Primrec.snd)
  exact (primrec_encodeProof.comp hlist).to₂

/-! ### The numerical proof predicate -/

/-- `Proof_T Th p a` asserts that the proof sequence coded by `p` is a proof,
in the theory presentation `Th`, of the candidate formula string coded by `a`.
It is defined by decoding and appealing to `IsProofList`, and depends only on
`TheoryPresentation`: no primitive-recursive certificate is required to state
it. -/
def Proof_T (Th : TheoryPresentation) (p : ProofSequenceCode)
    (a : FormulaCode) : Prop :=
  IsProofList Th (decodeProof p) (decodeFormula a)

/-- External preservation of provability under the numerical transformation.
The argument order is fixed: `r` codes a proof of `imp a b` and `p` codes a
proof of `a`.

The proof rewrites through `decodeProof_mp` and `decodeFormula_imp` and then
appeals to `proofList_mp`. The index-shift argument is not repeated here. -/
theorem proof_T_mp (Th : TheoryPresentation) {p r : ProofSequenceCode}
    {a b : FormulaCode} (hp : Proof_T Th p a) (hr : Proof_T Th r (imp a b)) :
    Proof_T Th (mp r p) b := by
  rw [Proof_T, decodeFormula_imp] at hr
  rw [Proof_T, decodeProof_mp]
  exact proofList_mp hp hr

/-! ### Primitive recursiveness of the numerical proof predicate

`LineJustified` and `IsProofList` are stated with the unbounded quantifiers
`∃ j < i`, `∃ k < i` and `∀ i, i < Ψ.length → …`. The certificates below are
built for `List.range`-bounded forms of exactly those clauses and transported to
the existing predicates by `PrimrecRel.of_eq`, using `List.mem_range`. No
predicate is redefined, weakened, or replaced, and no classical decision
procedure is used for the unbounded surface form. -/

private theorem primrecPred_holds {P : StringPredicate} (h : Primrec P.test) :
    PrimrecPred P.Holds :=
  Primrec.eq.comp h (Primrec.const true)

/-- `List.getLastD` at the default `[]`, in the form used by the certificate.
Its equality with the accessor `IsProofList` uses is proved here. -/
private theorem getLastD_eq_option_getD (l : ProofSequence) :
    l.getLastD [] = (l.reverse.head?).getD [] := by
  rw [List.getLastD_eq_getLast?, List.head?_reverse]

private theorem primrec_getLastD :
    Primrec fun l : ProofSequence => l.getLastD [] := by
  have h : Primrec fun l : ProofSequence => (l.reverse.head?).getD [] :=
    Primrec.option_getD.comp
      (Primrec.list_head?.comp Primrec.list_reverse) (Primrec.const [])
  simpa only [getLastD_eq_option_getD] using h

/-- The `List.range`-bounded form of the modus-ponens clause of
`LineJustified`. The two strict bounds `j < i` and `k < i` are preserved
exactly; `List.mem_range` is the only change. -/
private theorem primrecPred_mpClause :
    PrimrecPred fun x : ProofSequence × ℕ =>
      ∃ j ∈ List.range x.2, ∃ k ∈ List.range x.2,
        x.1.getD k [] = impString (x.1.getD j []) (x.1.getD x.2 []) := by
  -- innermost, over `k`, with context `c = (Ψ, i, j)`
  have hk : PrimrecRel fun (k : ℕ) (c : ProofSequence × ℕ × ℕ) =>
      c.1.getD k [] = impString (c.1.getD c.2.2 []) (c.1.getD c.2.1 []) := by
    have hΨ : Primrec fun p : ℕ × ProofSequence × ℕ × ℕ => p.2.1 :=
      Primrec.fst.comp Primrec.snd
    have hi : Primrec fun p : ℕ × ProofSequence × ℕ × ℕ => p.2.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hj : Primrec fun p : ℕ × ProofSequence × ℕ × ℕ => p.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hlhs : Primrec fun p : ℕ × ProofSequence × ℕ × ℕ =>
        p.2.1.getD p.1 [] := (Primrec.list_getD []).comp hΨ Primrec.fst
    have hrhs : Primrec fun p : ℕ × ProofSequence × ℕ × ℕ =>
        impString (p.2.1.getD p.2.2.2 []) (p.2.1.getD p.2.2.1 []) :=
      Primrec₂.comp primrec_impString
        ((Primrec.list_getD []).comp hΨ hj) ((Primrec.list_getD []).comp hΨ hi)
    exact Primrec.eq.comp₂ hlhs.to₂ hrhs.to₂
  -- bound `k` by `List.range i`
  have hkb : PrimrecPred fun c : ProofSequence × ℕ × ℕ =>
      ∃ k ∈ List.range c.2.1,
        c.1.getD k [] = impString (c.1.getD c.2.2 []) (c.1.getD c.2.1 []) :=
    hk.exists_mem_list.comp
      (Primrec.list_range.comp (Primrec.fst.comp Primrec.snd)) Primrec.id
  -- reassociate to a relation in `j` over context `x = (Ψ, i)`
  have hj : PrimrecRel fun (j : ℕ) (x : ProofSequence × ℕ) =>
      ∃ k ∈ List.range x.2,
        x.1.getD k [] = impString (x.1.getD j []) (x.1.getD x.2 []) := by
    have hre : Primrec fun p : ℕ × ProofSequence × ℕ =>
        ((p.2.1, p.2.2, p.1) : ProofSequence × ℕ × ℕ) :=
      Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.pair (Primrec.snd.comp Primrec.snd) Primrec.fst)
    exact (hkb.comp hre).primrecRel
  -- bound `j` by `List.range i`
  exact hj.exists_mem_list.comp (Primrec.list_range.comp Primrec.snd) Primrec.id

private theorem primrecRel_lineJustified (Th : PRTheoryPresentation) :
    PrimrecRel (LineJustified Th.toTheory) := by
  have hline : Primrec fun x : ProofSequence × ℕ => x.1.getD x.2 [] :=
    (Primrec.list_getD []).comp Primrec.fst Primrec.snd
  have hlen : PrimrecPred fun x : ProofSequence × ℕ => x.2 < x.1.length :=
    Primrec.nat_lt.comp Primrec.snd (Primrec.list_length.comp Primrec.fst)
  have hform : PrimrecPred fun x : ProofSequence × ℕ =>
      Th.toTheory.syn.formula.Holds (x.1.getD x.2 []) :=
    (primrecPred_holds Th.formula_prim).comp hline
  have hlog : PrimrecPred fun x : ProofSequence × ℕ =>
      Th.toTheory.syn.logicalAxiom.Holds (x.1.getD x.2 []) :=
    (primrecPred_holds Th.logicalAxiom_prim).comp hline
  have hax : PrimrecPred fun x : ProofSequence × ℕ =>
      Th.toTheory.ax.Holds (x.1.getD x.2 []) :=
    (primrecPred_holds Th.ax_prim).comp hline
  have hbounded : PrimrecRel fun (Ψ : ProofSequence) (i : ℕ) =>
      i < Ψ.length ∧
        Th.toTheory.syn.formula.Holds (Ψ.getD i []) ∧
          (Th.toTheory.syn.logicalAxiom.Holds (Ψ.getD i []) ∨
            Th.toTheory.ax.Holds (Ψ.getD i []) ∨
            ∃ j ∈ List.range i, ∃ k ∈ List.range i,
              Ψ.getD k [] = impString (Ψ.getD j []) (Ψ.getD i [])) :=
    (hlen.and (hform.and (hlog.or (hax.or primrecPred_mpClause)))).primrecRel
  refine hbounded.of_eq fun Ψ i => ?_
  simp only [LineJustified, List.mem_range]

private theorem primrecRel_isProofList (Th : PRTheoryPresentation) :
    PrimrecRel (IsProofList Th.toTheory) := by
  have hne : PrimrecPred fun x : ProofSequence × FormulaString => ¬ (x.1 = []) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [])).not
  have hlast : PrimrecPred fun x : ProofSequence × FormulaString =>
      x.1.getLastD [] = x.2 :=
    Primrec.eq.comp (primrec_getLastD.comp Primrec.fst) Primrec.snd
  have hall : PrimrecPred fun x : ProofSequence × FormulaString =>
      ∀ i ∈ List.range x.1.length, LineJustified Th.toTheory x.1 i :=
    ((primrecRel_lineJustified Th).swap.forall_mem_list).comp
      (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst))
      Primrec.fst
  have hbounded : PrimrecRel fun (Ψ : ProofSequence) (φ : FormulaString) =>
      ¬ (Ψ = []) ∧ Ψ.getLastD [] = φ ∧
        ∀ i ∈ List.range Ψ.length, LineJustified Th.toTheory Ψ i :=
    (hne.and (hlast.and hall)).primrecRel
  refine hbounded.of_eq fun Ψ φ => ?_
  simp only [IsProofList, ne_eq, List.mem_range]

/-- The numerical proof predicate of a primitive-recursively presented theory is
primitive recursive. This is external Lean certification of the existing
`Proof_T`. This module defines no arithmetic formula for it; the separate
`Arith` root supplies one. Nothing here is proved in PA. -/
theorem primrecRel_proof_T (Th : PRTheoryPresentation) :
    PrimrecRel (Proof_T Th.toTheory) :=
  ((primrecRel_isProofList Th).comp₂
      (primrec_decodeProof.comp₂ Primrec₂.left)
      (primrec_decodeFormula.comp₂ Primrec₂.right)).of_eq
    fun _ _ => Iff.rfl

end Metamath.Feferman
