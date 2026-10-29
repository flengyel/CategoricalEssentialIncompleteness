/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import Mathlib.Computability.Primrec.List

/-!
# Feferman proof sequences with modus ponens as the sole inference rule

Feferman, *Arithmetization of Metamathematics in a General Setting*,
Fund. Math. 49 (1960), §2(c), p. 44: a proof is a finite sequence of formulas
whose last entry is the conclusion and each of whose entries is a logical
axiom, an axiom of the theory, or follows from two earlier entries by modus
ponens — **modus ponens is the only rule of inference**. `IsProofList`
formalizes these defining clauses at the list level, relative to a
`TheoryPresentation`; it is not yet Feferman's arithmetized predicate `Prf_𝒜`.
`mpList` is the explicit structural transformation combining a proof of `a → b`
with a proof of `a`, and `proofList_mp` is the external preservation theorem.

## Representation

Three levels are kept apart. This module occupies the first two.

* `Token = ℕ`, `FormulaString = List Token` — finite token strings.
* `ProofSequence = List FormulaString` — finite sequences of candidate formulas.
* natural-number codes — **not** in this module; see the boundary note below.

A `FormulaString` is a *candidate* formula string. Whether it is a formula is
decided by the `formula` predicate of a `SyntaxPresentation`, not by the type.

`impString` is self-delimiting:
`impString a b` records the tag, the length of the antecedent, and then the
concatenation, so the antecedent and consequent are recoverable by taking and
dropping. That is what lets the later numeric `mp` recover `b` from the final
implication of `r` when it is handed only two proof codes.

## Behaviour of the accessors

`lhsString` and `rhsString` are total, defined by `take`/`drop` rather than by
pattern matching, which keeps them directly primitive recursive. On an
arbitrary string `s` they behave as follows.

* The first token of `s` is ignored. Neither accessor inspects it, so neither
  checks that `s` opens with `impTag`.
* The second token of `s` is read as the split point `n := s.getD 1 0`.
* Both accessors then operate on `s.drop 2`: `lhsString s = (s.drop 2).take n`
  and `rhsString s = (s.drop 2).drop n`.
* `List.take` and `List.drop` truncate. If `n` exceeds `(s.drop 2).length` then
  `lhsString s` is all of `s.drop 2` and `rhsString s` is `[]`.
* If `s` has fewer than two tokens then `s.drop 2 = []` and `n = 0`, so both
  accessors return `[]`.

## Two interface layers

Structural data and primitive-recursive certification are separate.
`SyntaxPresentation` and `TheoryPresentation` hold Boolean tests and the
propositions relating them; `PRTheoryPresentation` adds `Primrec` certificates
for the three tests. `LineJustified`, `IsProofList` and `proofList_mp` are
parameterized by `TheoryPresentation` alone, because none of them uses a
certificate.

## Pinned-Mathlib API used

`Primrec.list_cons`, `list_length`, `list_append`, `list_concat`, `list_take`,
`list_drop`, `list_getD`, `list_reverse`, `list_head?`, from
`Mathlib/Computability/Primrec/List.lean` together with
`Primrec.option_getD`. `List.take` and `List.drop` are `Primrec₂` in the
argument order `(n, l)`.

## Field naming

`TheoryPresentation` uses the field names `syn` and `ax`. `syntax` and `axiom`
are Lean 4 keywords and cannot be field names.

## Boundary

This module supplies the external finite-string formulation of Feferman's
MP-only proof sequences, the structural `mpList` transformation, external
preservation, and primitive recursiveness of the string and list operations
constructed here.

It does **not** supply natural-number proof codes, `Proof_T : ℕ → ℕ → Prop`,
primitive recursiveness of the coded proof predicate, Feferman's concrete
`Fm_K` or the ten logical-axiom schemata `Ax_K`, substitution, or any
arithmetic internalization.
-/

namespace Metamath.Feferman

/-! ### Representation -/

/-- A syntactic token. -/
abbrev Token := ℕ

/-- A candidate formula string: a finite token string. Whether it is a formula
is decided by a `SyntaxPresentation`, not by membership in this type. -/
abbrev FormulaString := List Token

/-- A proof sequence: a finite list of candidate formula strings. -/
abbrev ProofSequence := List FormulaString

/-- The tag opening an implication string. -/
def impTag : Token := 0

/-- The self-delimiting implication string: tag, length of the antecedent,
then the antecedent followed by the consequent. -/
def impString (a b : FormulaString) : FormulaString :=
  impTag :: a.length :: (a ++ b)

/-- The antecedent of an implication string: ignore the first token, read the
second as the split point, and `take` that many tokens of the remainder. See
the module docstring for the behaviour on malformed input. -/
def lhsString (s : FormulaString) : FormulaString :=
  (s.drop 2).take (s.getD 1 0)

/-- The consequent of an implication string: ignore the first token, read the
second as the split point, and `drop` that many tokens of the remainder. See
the module docstring for the behaviour on malformed input. -/
def rhsString (s : FormulaString) : FormulaString :=
  (s.drop 2).drop (s.getD 1 0)

/-- The length field of an implication string. Stated separately and proved by
`rfl`: `#print axioms` on the `simp` route through `List.getD` at a literal
index lists `Classical.choice` at this Mathlib revision, and this route does
not. -/
private theorem impString_getD_one (a b : FormulaString) :
    (impString a b).getD 1 0 = a.length := rfl

@[simp] theorem lhsString_impString (a b : FormulaString) :
    lhsString (impString a b) = a := by
  change ((impString a b).drop 2).take ((impString a b).getD 1 0) = a
  rw [impString_getD_one]
  change (a ++ b).take a.length = a
  simp

@[simp] theorem rhsString_impString (a b : FormulaString) :
    rhsString (impString a b) = b := by
  change ((impString a b).drop 2).drop ((impString a b).getD 1 0) = b
  rw [impString_getD_one]
  change (a ++ b).drop a.length = b
  simp

/-! ### Structural presentation

No `Primrec` data appears in this section. Certificates are added separately in
the next one. -/

/-- A predicate on candidate formula strings, presented by a Boolean decision
procedure. -/
structure StringPredicate where
  /-- The deciding function. -/
  test : FormulaString → Bool

/-- The proposition decided by a `StringPredicate`. -/
def StringPredicate.Holds (P : StringPredicate) (φ : FormulaString) : Prop :=
  P.test φ = true

/-- `StringPredicate.Holds` is decidable, by the Boolean test that defines it. -/
instance StringPredicate.decidableHolds (P : StringPredicate) (φ : FormulaString) :
    Decidable (P.Holds φ) :=
  inferInstanceAs (Decidable (P.test φ = true))

/-- A syntax presentation: the predicates and implication-formation facts
required by this module. The formula predicate corresponds to `Fm_K` from
Feferman §2(b); the logical-axiom predicate corresponds to `Ax_K` from §2(c). -/
structure SyntaxPresentation where
  /-- Which candidate strings are formulas. -/
  formula : StringPredicate
  /-- Which candidate strings are logical axioms (Feferman §2(c)). -/
  logicalAxiom : StringPredicate
  /-- Logical axioms are formulas. -/
  logicalAxiom_formula : ∀ {φ}, logicalAxiom.Holds φ → formula.Holds φ
  /-- An implication is a formula exactly when both of its parts are. -/
  formula_imp_iff : ∀ a b,
    formula.Holds (impString a b) ↔ formula.Holds a ∧ formula.Holds b

/-- A theory presentation over a syntax presentation. -/
structure TheoryPresentation where
  /-- The syntax presentation. Named `syn` because `syntax` is a keyword. -/
  syn : SyntaxPresentation
  /-- The non-logical axioms. Named `ax` because `axiom` is a keyword. -/
  ax : StringPredicate
  /-- Axioms are formulas. -/
  ax_formula : ∀ {φ}, ax.Holds φ → syn.formula.Holds φ

/-! ### Primitive-recursive certification

This is the only part of the module that mentions `Primrec`. `#print axioms`
on `PRTheoryPresentation` lists `Classical.choice`; it depends on it through
the `Primcodable` instances selected for `List ℕ` and `Bool` at this Mathlib
revision. Nothing in the previous section or in `proofList_mp` refers to this
structure. -/

/-- A theory presentation together with `Primrec` certificates for its three
Boolean tests. -/
structure PRTheoryPresentation where
  /-- The underlying structural presentation. -/
  toTheory : TheoryPresentation
  /-- The formula test is primitive recursive. -/
  formula_prim : Primrec toTheory.syn.formula.test
  /-- The logical-axiom test is primitive recursive. -/
  logicalAxiom_prim : Primrec toTheory.syn.logicalAxiom.test
  /-- The axiom test is primitive recursive. -/
  ax_prim : Primrec toTheory.ax.test

/-! ### The proof-sequence predicate -/

variable (Th : TheoryPresentation)

/-- Line `i` of `Ψ` is justified: `i` is in range, the line is a formula, and it
is a logical axiom, a theory axiom, or the consequent of an implication
appearing at an earlier line `k` whose antecedent appears at an earlier line
`j`.

The range condition `i < Ψ.length` is part of the definition. Without it the
predicate would be satisfiable out of range, since `List.getD` returns the
default `[]` there and `[]` may well be an axiom of a given presentation.

The orientation is Feferman's: line `k` is the implication, line `j` the
antecedent, line `i` the consequent. -/
def LineJustified (Ψ : ProofSequence) (i : ℕ) : Prop :=
  i < Ψ.length ∧
    Th.syn.formula.Holds (Ψ.getD i []) ∧
      (Th.syn.logicalAxiom.Holds (Ψ.getD i []) ∨
        Th.ax.Holds (Ψ.getD i []) ∨
        ∃ j < i, ∃ k < i, Ψ.getD k [] = impString (Ψ.getD j []) (Ψ.getD i []))

/-- `Ψ` is a Feferman §2(c) proof of `φ` in `Th`: nonempty, ending in `φ`, with
every line justified. The empty list is never a proof. -/
def IsProofList (Ψ : ProofSequence) (φ : FormulaString) : Prop :=
  Ψ ≠ [] ∧ Ψ.getLastD [] = φ ∧ ∀ i, i < Ψ.length → LineJustified Th Ψ i

variable {Th}

/-! ### The `mp` transformation -/

/-- The structural modus-ponens transformation. `r` proves `impString a b` and
`p` proves `a`; the concatenation followed by the consequent of the last line
of `r` proves `b`. -/
def mpList (r p : ProofSequence) : ProofSequence :=
  r ++ p ++ [rhsString (r.getLastD [])]

/-! ### Indexing lemmas -/

private theorem getD_append_left {l₁ l₂ : ProofSequence} {i : ℕ}
    (h : i < l₁.length) : (l₁ ++ l₂).getD i [] = l₁.getD i [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right {l₁ l₂ : ProofSequence} {i : ℕ}
    (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i [] = l₂.getD (i - l₁.length) [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- No nonemptiness hypothesis is needed: for `l = []` both sides are `[]`. -/
private theorem getD_last (l : ProofSequence) :
    l.getD (l.length - 1) [] = l.getLastD [] := by
  rw [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?,
    List.getLast?_eq_getElem?]

private theorem getLastD_eq_head?_reverse (l : ProofSequence) :
    l.getLastD [] = (l.reverse.head?).getD [] := by
  rw [List.getLastD_eq_getLast?, List.head?_reverse]

/-! ### External preservation -/

/-- External preservation of provability under `mpList`: Feferman §2(c) modus
ponens at the level of proof sequences. -/
theorem proofList_mp {p r : ProofSequence} {a b : FormulaString}
    (hp : IsProofList Th p a) (hr : IsProofList Th r (impString a b)) :
    IsProofList Th (mpList r p) b := by
  obtain ⟨hpne, hplast, hpj⟩ := hp
  obtain ⟨hrne, hrlast, hrj⟩ := hr
  -- The appended line is `b`.
  have hrhs : rhsString (r.getLastD []) = b := by
    rw [hrlast]; exact rhsString_impString a b
  have hshape : mpList r p = r ++ p ++ [b] := by
    simp only [mpList, hrhs]
  rw [hshape]
  -- Notation for the three index regions.
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  have hrlen : 0 < r.length := List.length_pos_of_ne_nil hrne
  have hlen : (r ++ p ++ [b]).length = r.length + p.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  -- Lines of `r` are unchanged.
  have hget_r : ∀ i, i < r.length → (r ++ p ++ [b]).getD i [] = r.getD i [] := by
    intro i hi
    rw [getD_append_left (by simpa using Nat.lt_add_right p.length hi),
      getD_append_left hi]
  -- Lines of `p` are shifted by `r.length`.
  have hget_p : ∀ i, i < p.length →
      (r ++ p ++ [b]).getD (r.length + i) [] = p.getD i [] := by
    intro i hi
    have h1 : r.length + i < (r ++ p).length := by simp; omega
    rw [getD_append_left h1,
      getD_append_right (Nat.le_add_right r.length i), Nat.add_sub_cancel_left]
  -- The final line is `b`.
  have hget_b : (r ++ p ++ [b]).getD (r.length + p.length) [] = b := by
    rw [getD_append_right (by simp)]
    simp
  refine ⟨by simp, ?_, ?_⟩
  · -- last entry
    exact List.getLastD_concat
  · -- every line is justified
    intro i hi
    rw [hlen] at hi
    rcases Nat.lt_or_ge i r.length with hir | hir
    · -- (1) unchanged lines from `r`
      obtain ⟨-, hform, hcase⟩ := hrj i hir
      rw [LineJustified, hget_r i hir]
      refine ⟨by rw [hlen]; omega, hform, ?_⟩
      rcases hcase with h | h | ⟨j, hj, k, hk, hjk⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr
          ⟨j, hj, k, hk, by
            rw [hget_r j (lt_trans hj hir), hget_r k (lt_trans hk hir)]; exact hjk⟩)
    · rcases Nat.lt_or_ge i (r.length + p.length) with hip | hip
      · -- (2) shifted lines from `p`
        obtain ⟨m, rfl⟩ : ∃ m, i = r.length + m := ⟨i - r.length, by omega⟩
        have hm : m < p.length := by omega
        obtain ⟨-, hform, hcase⟩ := hpj m hm
        rw [LineJustified, hget_p m hm]
        refine ⟨by rw [hlen]; omega, hform, ?_⟩
        rcases hcase with h | h | ⟨j, hj, k, hk, hjk⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ⟨r.length + j, by omega, r.length + k, by omega, ?_⟩)
          rw [hget_p j (lt_trans hj hm), hget_p k (lt_trans hk hm)]
          exact hjk
      · -- (3) the appended line `b`
        have hieq : i = r.length + p.length := by omega
        subst hieq
        rw [LineJustified, hget_b]
        -- `b` is a formula, because `impString a b` is the last line of `r`
        have hlastr : r.getD (r.length - 1) [] = impString a b := by
          rw [getD_last, hrlast]
        obtain ⟨-, hformr, -⟩ := hrj (r.length - 1) (by omega)
        rw [hlastr] at hformr
        have hformb : Th.syn.formula.Holds b :=
          ((Th.syn.formula_imp_iff a b).1 hformr).2
        refine ⟨by rw [hlen]; omega, hformb, Or.inr (Or.inr ?_)⟩
        -- witnesses: `j` is the last line of `p` (namely `a`),
        -- `k` is the last line of `r` (namely `impString a b`)
        refine ⟨r.length + (p.length - 1), by omega, r.length - 1, by omega, ?_⟩
        have hj' : (r ++ p ++ [b]).getD (r.length + (p.length - 1)) [] = a := by
          rw [hget_p (p.length - 1) (by omega), getD_last, hplast]
        have hk' : (r ++ p ++ [b]).getD (r.length - 1) [] = impString a b := by
          rw [hget_r (r.length - 1) (by omega), hlastr]
        rw [hj', hk']

/-! ### Primitive recursiveness of the string and list operations -/

theorem primrec_impString : Primrec₂ impString := by
  have happ : Primrec fun x : FormulaString × FormulaString => x.1 ++ x.2 :=
    Primrec.list_append
  have hlen : Primrec fun x : FormulaString × FormulaString => x.1.length :=
    Primrec.list_length.comp Primrec.fst
  have h2 : Primrec fun x : FormulaString × FormulaString =>
      x.1.length :: (x.1 ++ x.2) := Primrec.list_cons.comp hlen happ
  exact Primrec.list_cons.comp (Primrec.const impTag) h2

theorem primrec_lhsString : Primrec lhsString := by
  have hdrop : Primrec fun s : FormulaString => s.drop 2 :=
    Primrec.list_drop.comp (Primrec.const 2) Primrec.id
  have hidx : Primrec fun s : FormulaString => s.getD 1 0 :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const 1)
  exact Primrec.list_take.comp hidx hdrop

theorem primrec_rhsString : Primrec rhsString := by
  have hdrop : Primrec fun s : FormulaString => s.drop 2 :=
    Primrec.list_drop.comp (Primrec.const 2) Primrec.id
  have hidx : Primrec fun s : FormulaString => s.getD 1 0 :=
    (Primrec.list_getD 0).comp Primrec.id (Primrec.const 1)
  exact Primrec.list_drop.comp hidx hdrop

theorem primrec_mpList : Primrec₂ mpList := by
  have hlast : Primrec fun x : ProofSequence × ProofSequence =>
      x.1.getLastD [] := by
    have h : Primrec fun x : ProofSequence × ProofSequence =>
        (x.1.reverse.head?).getD [] :=
      Primrec.option_getD.comp
        (Primrec.list_head?.comp (Primrec.list_reverse.comp Primrec.fst))
        (Primrec.const [])
    simpa only [getLastD_eq_head?_reverse] using h
  have hrhs : Primrec fun x : ProofSequence × ProofSequence =>
      rhsString (x.1.getLastD []) := primrec_rhsString.comp hlast
  have happ : Primrec fun x : ProofSequence × ProofSequence => x.1 ++ x.2 :=
    Primrec.list_append
  exact Primrec.list_concat.comp happ hrhs

end Metamath.Feferman
