/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import RiceShapiro.Selection

/-!
# Joins, complemented domains, decisions, and case distinction

This module formalizes binary joins of domains, specified complements,
decisions, inverse images of complements under route (ii) of the manuscript,
and the two branch equations for the case-distinction morphism.

The manuscript reserves `decidable` for the existence of a quasicomplement;
`Complemented` records a specified lattice complement.

Route (i) and the derivation of decisions from local connectedness are not
formalized here. The full case-distinction laws are proved in
`RiceShapiro.CaseLaws`.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory CoprodStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]

namespace DomSemilattice

variable {Q : C}

/-- `d₀ ∨ d₁ = ran [d₀, d₁]`. -/
def join (d e : DomSemilattice Q) : DomSemilattice Q :=
  ⟨HasRanges.ran (copair d.hom e.hom), HasRanges.rst_ran _⟩

omit [HasCoproducts C] in
@[simp] lemma join_hom (d e : DomSemilattice Q) :
    (join d e).hom = HasRanges.ran (copair d.hom e.hom) := rfl

lemma left_le_join (d e : DomSemilattice Q) : d ≤ join d e := by
  change d.hom ≫ HasRanges.ran (copair d.hom e.hom) = d.hom
  calc d.hom ≫ HasRanges.ran (copair d.hom e.hom)
      = (i0 Q Q ≫ copair d.hom e.hom) ≫ HasRanges.ran (copair d.hom e.hom) := by
        rw [HasCoproducts.i0_copair]
    _ = i0 Q Q ≫ copair d.hom e.hom ≫ HasRanges.ran (copair d.hom e.hom) :=
        Category.assoc _ _ _
    _ = i0 Q Q ≫ copair d.hom e.hom := by rw [HasRanges.comp_ran]
    _ = d.hom := HasCoproducts.i0_copair _ _

lemma right_le_join (d e : DomSemilattice Q) : e ≤ join d e := by
  change e.hom ≫ HasRanges.ran (copair d.hom e.hom) = e.hom
  calc e.hom ≫ HasRanges.ran (copair d.hom e.hom)
      = (i1 Q Q ≫ copair d.hom e.hom) ≫ HasRanges.ran (copair d.hom e.hom) := by
        rw [HasCoproducts.i1_copair]
    _ = i1 Q Q ≫ copair d.hom e.hom ≫ HasRanges.ran (copair d.hom e.hom) :=
        Category.assoc _ _ _
    _ = i1 Q Q ≫ copair d.hom e.hom := by rw [HasRanges.comp_ran]
    _ = e.hom := HasCoproducts.i1_copair _ _

lemma join_le {d e f : DomSemilattice Q} (h0 : d ≤ f) (h1 : e ≤ f) :
    join d e ≤ f := by
  have hrec : copair d.hom e.hom ≫ f.hom = copair d.hom e.hom := by
    rw [HasCoproducts.copair_comp, show d.hom ≫ f.hom = d.hom from h0,
      show e.hom ≫ f.hom = e.hom from h1]
  change HasRanges.ran (copair d.hom e.hom) ≫ f.hom
      = HasRanges.ran (copair d.hom e.hom)
  exact HasRanges.ran_le_of_receives _ hrec

/-- Morphisms agreeing after `d` and after `e` are equal when `d ∨ e = 1`.
Since `d ∨ e = ran [d, e]`, agreement after the copairing forces agreement
after the identity. -/
theorem eq_of_agree_on_join_top {Q R : C} {d e : DomSemilattice Q}
    (hjoin : join d e = top Q) {F G : Q ⟶ R}
    (hd : d.hom ≫ F = d.hom ≫ G) (he : e.hom ≫ F = e.hom ≫ G) : F = G := by
  have hj : HasRanges.ran (copair d.hom e.hom) = 𝟙 Q :=
    congrArg DomSemilattice.hom hjoin
  have hc : copair d.hom e.hom ≫ F = copair d.hom e.hom ≫ G := by
    rw [HasCoproducts.copair_comp, HasCoproducts.copair_comp, hd, he]
  have hr := HasRanges.ran_uniq (copair d.hom e.hom) F G hc
  rwa [hj, Category.id_comp, Category.id_comp] at hr

/-! ### Complemented domains and decisions -/

variable [Limits.HasZeroMorphisms C]

/-- A specified complement: `d d⊥ = 0` and `d ∨ d⊥ = 1`. Not to be confused
with *decidable*, which the manuscript reserves for a domain with a
quasicomplement. -/
structure Complemented (d : DomSemilattice Q) where
  /-- The specified complement. -/
  compl : DomSemilattice Q
  /-- `d d⊥ = 0`. -/
  meet_zero : d.hom ≫ compl.hom = 0
  /-- `d ∨ d⊥ = 1`. -/
  join_top : join d compl = top Q

/-- A decision for a complemented domain: a total `δ_d : Q ⟶ Q + Q` sending `d`
into the right summand and `d⊥` into the left. -/
structure Decision {d : DomSemilattice Q} (dc : Complemented d) where
  /-- `δ_d : Q ⟶ Q + Q`. -/
  delta : Q ⟶ coprod Q Q
  /-- `δ_d` is total. -/
  delta_total : rst delta = 𝟙 Q
  /-- `δ_d d = ι₁ d`. -/
  on_dom : d.hom ≫ delta = d.hom ≫ i1 Q Q
  /-- `δ_d d⊥ = ι₀ d⊥`. -/
  on_compl : dc.compl.hom ≫ delta = dc.compl.hom ≫ i0 Q Q

/-- Morphisms agreeing after a domain and its specified complement are equal.
Only the join equation of the complement is used. -/
theorem eq_of_agree_on_complement {Q R : C} {d : DomSemilattice Q}
    (dc : Complemented d) {F G : Q ⟶ R}
    (h : d.hom ≫ F = d.hom ≫ G)
    (h' : dc.compl.hom ≫ F = dc.compl.hom ≫ G) : F = G :=
  eq_of_agree_on_join_top dc.join_top h h'

section Quasicomplement

-- `rst 0 = 0` is needed below, and that is `DomSemilattice.rst_zero`, which
-- assumes zero absorption. The complement and decision definitions above do
-- not.
variable [RecursionCategory.Prodominical C]

/-! ### Inverse images, quasicomplements, and dense domains

This section proves the manuscript's inverse-image result under route (ii): if
every dense domain on the source is total, then the inverse image of a
complemented domain along a total morphism is complemented. Route (i), based on
preservation of binary joins by inverse image, is not formalized.

`Prodominical` is used only through `DomSemilattice.rst_zero`.
-/

/-- `f^* a = rst (a f)`. -/
def invImage {P Q : C} (f : P ⟶ Q) (a : DomSemilattice Q) : DomSemilattice P :=
  ⟨rst (f ≫ a.hom), rst_rst _⟩

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
@[simp] lemma invImage_hom {P Q : C} (f : P ⟶ Q) (a : DomSemilattice Q) :
    (invImage f a).hom = rst (f ≫ a.hom) := rfl

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- Inverse image preserves the meet. R4 moves `f^* a` past `f`, R3 splits the
restriction. -/
lemma invImage_meet {P Q : C} (f : P ⟶ Q) (a b : DomSemilattice Q) :
    invImage f (meet a b) = meet (invImage f a) (invImage f b) := by
  apply ext'
  have h4 : rst (f ≫ a.hom) ≫ f = f ≫ a.hom := by
    have hx := PCategory.rst_comp' f a.hom
    rwa [a.isDomain] at hx
  change rst (f ≫ a.hom ≫ b.hom) = rst (f ≫ a.hom) ≫ rst (f ≫ b.hom)
  calc rst (f ≫ a.hom ≫ b.hom)
      = rst ((f ≫ a.hom) ≫ b.hom) := by rw [Category.assoc]
    _ = rst ((rst (f ≫ a.hom) ≫ f) ≫ b.hom) := by rw [h4]
    _ = rst (rst (f ≫ a.hom) ≫ f ≫ b.hom) := by rw [Category.assoc]
    _ = rst (f ≫ a.hom) ≫ rst (f ≫ b.hom) := PCategory.rst_comp_rst' _ _

/-- `d'` is a quasicomplement of `d`: they meet in `0`, and only `0` is killed
by both. Di Paola–Heller Defs. 3.8–3.9; the manuscript reserves *decidable*
for a domain admitting one. -/
def IsQuasicomplement {Q : C} (d d' : DomSemilattice Q) : Prop :=
  d.hom ≫ d'.hom = 0 ∧
    ∀ {R : C} (φ : R ⟶ Q), φ ≫ d.hom = 0 → φ ≫ d'.hom = 0 → φ = 0

/-- A domain is dense when only `0` meets it in `0`. -/
def IsDense {Q : C} (h : DomSemilattice Q) : Prop :=
  ∀ c : DomSemilattice Q, c.hom ≫ h.hom = 0 → c.hom = 0

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [RecursionCategory.Prodominical C] in
/-- Density is preserved upwards. -/
theorem IsDense.mono {Q : C} {d e : DomSemilattice Q} (hde : d ≤ e)
    (hd : IsDense d) : IsDense e := by
  intro c hc
  refine hd c ?_
  calc c.hom ≫ d.hom = c.hom ≫ d.hom ≫ e.hom := by rw [show d.hom ≫ e.hom = d.hom from hde]
    _ = c.hom ≫ e.hom ≫ d.hom := by rw [comm]
    _ = (c.hom ≫ e.hom) ≫ d.hom := (Category.assoc _ _ _).symm
    _ = 0 := by rw [hc, Limits.zero_comp]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C] in
/-- Quasicomplements pull back along a total morphism. -/
theorem isQuasicomplement_invImage {P Q : C} (f : P ⟶ Q) (hf : rst f = 𝟙 P)
    {d d' : DomSemilattice Q} (h : IsQuasicomplement d d') :
    IsQuasicomplement (invImage f d) (invImage f d') := by
  have hpast : ∀ a : DomSemilattice Q, (invImage f a).hom ≫ f = f ≫ a.hom := by
    intro a
    have hx := PCategory.rst_comp' f a.hom
    rwa [a.isDomain] at hx
  constructor
  · have hm := congrArg DomSemilattice.hom (invImage_meet f d d')
    change ((invImage f d).meet (invImage f d')).hom = 0
    rw [← hm]
    change rst (f ≫ (meet d d').hom) = 0
    rw [show (meet d d').hom = 0 from h.1, Limits.comp_zero, rst_zero]
  · intro R ψ h0 h1
    have hd : (ψ ≫ f) ≫ d.hom = 0 := by
      rw [Category.assoc, ← hpast d, ← Category.assoc, h0, Limits.zero_comp]
    have hd' : (ψ ≫ f) ≫ d'.hom = 0 := by
      rw [Category.assoc, ← hpast d', ← Category.assoc, h1, Limits.zero_comp]
    have hzero : ψ ≫ f = 0 := h.2 (ψ ≫ f) hd hd'
    have hrst : rst ψ = 0 := by
      rw [← rst_comp_of_isTotal' ψ hf, hzero, rst_zero]
    calc ψ = rst ψ ≫ ψ := (RestrictionCategory.rst_comp_self ψ).symm
      _ = (0 : R ⟶ R) ≫ ψ := by rw [hrst]
      _ = 0 := Limits.zero_comp

omit [RecursionCategory.Prodominical C] in
/-- The join of the two inverse images is dense. -/
theorem isDense_join_of_isQuasicomplement {Q : C} {d d' : DomSemilattice Q}
    (h : IsQuasicomplement d d') : IsDense (join d d') := by
  intro c hc
  have hcd : c.hom ≫ d.hom = 0 := by
    have hle : d.hom ≫ (join d d').hom = d.hom := left_le_join d d'
    calc c.hom ≫ d.hom = c.hom ≫ d.hom ≫ (join d d').hom := by rw [hle]
      _ = c.hom ≫ (join d d').hom ≫ d.hom := by rw [comm d (join d d')]
      _ = (c.hom ≫ (join d d').hom) ≫ d.hom := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hc, Limits.zero_comp]
  have hcd' : c.hom ≫ d'.hom = 0 := by
    have hle : d'.hom ≫ (join d d').hom = d'.hom := right_le_join d d'
    calc c.hom ≫ d'.hom = c.hom ≫ d'.hom ≫ (join d d').hom := by rw [hle]
      _ = c.hom ≫ (join d d').hom ≫ d'.hom := by rw [comm d' (join d d')]
      _ = (c.hom ≫ (join d d').hom) ≫ d'.hom := (Category.assoc _ _ _).symm
      _ = 0 := by rw [hc, Limits.zero_comp]
  exact h.2 c.hom hcd hcd'

omit [RecursionCategory.Prodominical C] in
/-- A specified complement is a quasicomplement. No distributivity hypothesis
is required. -/
theorem Complemented.isQuasicomplement {Q : C} {d : DomSemilattice Q}
    (dc : Complemented d) : IsQuasicomplement d dc.compl := by
  refine ⟨dc.meet_zero, ?_⟩
  intro R φ h0 h1
  have hd : HasRanges.ran φ ≫ d.hom = 0 := by
    have hx := HasRanges.ran_uniq φ d.hom 0 (by rw [h0, Limits.comp_zero])
    rwa [Limits.comp_zero] at hx
  have hd' : HasRanges.ran φ ≫ dc.compl.hom = 0 := by
    have hx := HasRanges.ran_uniq φ dc.compl.hom 0 (by rw [h1, Limits.comp_zero])
    rwa [Limits.comp_zero] at hx
  have hcomm : d.hom ≫ HasRanges.ran φ = HasRanges.ran φ ≫ d.hom := by
    have hx := PCategory.rst_comm' d.hom (HasRanges.ran φ)
    rwa [d.isDomain, HasRanges.rst_ran] at hx
  have hcomm' :
      dc.compl.hom ≫ HasRanges.ran φ = HasRanges.ran φ ≫ dc.compl.hom := by
    have hx := PCategory.rst_comm' dc.compl.hom (HasRanges.ran φ)
    rwa [dc.compl.isDomain, HasRanges.rst_ran] at hx
  have hzero : HasRanges.ran φ = (0 : Q ⟶ Q) := by
    apply eq_of_agree_on_complement dc
    · rw [hcomm, hd, Limits.comp_zero]
    · rw [hcomm', hd', Limits.comp_zero]
  calc φ = φ ≫ HasRanges.ran φ := (HasRanges.comp_ran φ).symm
    _ = φ ≫ 0 := by rw [hzero]
    _ = 0 := Limits.comp_zero

/-- If every dense domain on `P` is total, the inverse image along a total
morphism of a complemented domain is complemented. -/
def complementedInvImage {P Q : C} (f : P ⟶ Q) (hf : rst f = 𝟙 P)
    (hdense : ∀ h : DomSemilattice P, IsDense h → h.hom = 𝟙 P)
    {d : DomSemilattice Q} (dc : Complemented d) :
    Complemented (invImage f d) where
  compl := invImage f dc.compl
  meet_zero := (isQuasicomplement_invImage f hf dc.isQuasicomplement).1
  join_top :=
    ext' (hdense _ (isDense_join_of_isQuasicomplement
      (isQuasicomplement_invImage f hf dc.isQuasicomplement)))

end Quasicomplement

end DomSemilattice

/-! ### Case distinction along a decision -/

namespace ApproximationDatum

open DomSemilattice

variable [Limits.HasZeroMorphisms C]
variable {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)

/-- `P = (A ⊠ I) ⊠ I`. -/
abbrev caseP : C := nearProd (nearProd 𝒜.A 𝒜.I) 𝒜.I

/-- `Q = P ⊠ X`. -/
abbrev caseQ : C := nearProd 𝒜.caseP X

/-- `π_A : P ⟶ A`. -/
def projA : 𝒜.caseP ⟶ 𝒜.A := p0 (nearProd 𝒜.A 𝒜.I) 𝒜.I ≫ p0 𝒜.A 𝒜.I

/-- `π_i : P ⟶ I`. -/
def projI : 𝒜.caseP ⟶ 𝒜.I := p0 (nearProd 𝒜.A 𝒜.I) 𝒜.I ≫ p1 𝒜.A 𝒜.I

/-- `π_k : P ⟶ I`. -/
def projK : 𝒜.caseP ⟶ 𝒜.I := p1 (nearProd 𝒜.A 𝒜.I) 𝒜.I

/-- `α̂ = α(π_A ⊠ 1_X)`. -/
def alphaHat : 𝒜.caseQ ⟶ Y := evalAt 𝒜.approx 𝒜.projA

/-- `ε̂ = ε(π_i ⊠ 1_X)`. -/
def evHat : 𝒜.caseQ ⟶ Y := evalAt 𝒜.ev 𝒜.projI

/-- `U = u ⊠ 1_X` for `u = rst (s π_k)`. -/
def restrU : 𝒜.caseQ ⟶ 𝒜.caseQ := nearProd_map (entry s 𝒜.projK) (𝟙 X)

/-- `D = rst α̂`. -/
def domD : DomSemilattice 𝒜.caseQ := ⟨rst 𝒜.alphaHat, rst_rst _⟩

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] in
@[simp] lemma domD_hom : (𝒜.domD).hom = rst 𝒜.alphaHat := rfl

/-- The data the case-distinction morphism needs: a complement for `D` and a
decision for it. -/
structure CaseData where
  /-- `D` is complemented. -/
  complemented : Complemented 𝒜.domD
  /-- A decision for `D`. -/
  decision : Decision complemented

/-- `Case_s = [ε̂ U D⊥, α̂] δ_D`. -/
def Case (cd : 𝒜.CaseData) : 𝒜.caseQ ⟶ Y :=
  cd.decision.delta ≫
    copair (cd.complemented.compl.hom ≫ 𝒜.restrU s ≫ 𝒜.evHat) 𝒜.alphaHat

/-- First branch equation: `Case_s D = α̂`. -/
lemma case_on_domD (cd : 𝒜.CaseData) :
    𝒜.domD.hom ≫ 𝒜.Case s cd = 𝒜.alphaHat := by
  dsimp only [Case]
  rw [← Category.assoc, cd.decision.on_dom, Category.assoc,
    HasCoproducts.i1_copair]
  exact RestrictionCategory.rst_comp_self _

/-- Second branch equation: `Case_s D⊥ = ε̂ U D⊥`. -/
lemma case_on_compl (cd : 𝒜.CaseData) :
    cd.complemented.compl.hom ≫ 𝒜.Case s cd
      = cd.complemented.compl.hom ≫ 𝒜.restrU s ≫ 𝒜.evHat := by
  dsimp only [Case]
  rw [← Category.assoc, cd.decision.on_compl, Category.assoc,
    HasCoproducts.i0_copair, ← Category.assoc, DomSemilattice.idem]

end ApproximationDatum

end CategoryTheory
