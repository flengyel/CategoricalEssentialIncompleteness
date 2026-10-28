/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import RiceShapiro.GeneratedRepresentation
import RiceShapiro.Decisions

/-!
# Connected domains and local connectedness

`IsConnected` and `LocallyConnected` are the definitions of the manuscript's
subsection on total morphisms jointly epimorphic on domains.

`isPartialMono_of_total_test` is part (i) of the lemma on consequences of
jointly epimorphic total morphisms: a morphism is a partial monomorphism as
soon as the defining implication holds for total morphisms. It assumes only the
`P`-category structure and the hypothesis that total morphisms are jointly
epimorphic on domains.

`Decision.delta_eq` is the uniqueness half of the manuscript's proposition that
local connectedness supplies decisions. It uses the two branch equations and
`eq_of_agree_on_complement`, and neither local connectedness nor weak choice.

`leftBranch` and `rightBranch` are the complementary domains `1_Q + 0_Q` and
`0_Q + 1_Q` on `Q + Q`, and `decisionCollapse dc` is `c_d = ∇(d⊥ + d)`.

`existsDecision_of_locallyConnected` is the existence half. Its branch argument
is `connected_branch`: on a connected domain a total morphism into `Q + Q`
factors through one of the two injections, because the inverse images of the
branch domains are complementary there and `ran_comp_dom` decomposes the
connected domain along them. Partial monicity of `c_d` then follows from
`isPartialMono_of_total_test`, weak choice supplies a section, and the section
equation together with `rst_decisionCollapse` yields the two branch equations.
The route through `complementedInvImage` is route (ii) of the manuscript, which
is why the theorem assumes that every dense domain is total; no distributivity
is used.
-/

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory DomSemilattice CoprodStruct

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]

/-- Part (i) of the lemma on consequences of jointly epimorphic total
morphisms: the defining implication for a partial monomorphism need only be
checked on total morphisms. -/
theorem isPartialMono_of_total_test
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C) {Q R : C} (c : Q ⟶ R)
    (htest : ∀ {Z : C} (f g : Z ⟶ Q), rst f = 𝟙 Z → rst g = 𝟙 Z →
      f ≫ c = g ≫ c → f ≫ rst c = g ≫ rst c) :
    IsPartialMono c := by
  have hidem : rst c ≫ rst c = rst c := RestrictionCategory.rst_idem c
  have hR4 : ∀ {Z : C} (k : Z ⟶ Q), rst (k ≫ c) ≫ k = k ≫ rst c :=
    fun k => PCategory.rst_comp' k c
  have hle : ∀ {Z : C} (k : Z ⟶ Q), rst (k ≫ c) ≫ rst k = rst (k ≫ c) := by
    intro Z k
    have hx : rst (rst (k ≫ c) ≫ k) = rst (k ≫ rst c) := by rw [hR4 k]
    rwa [PCategory.rst_comp_rst', ← rst_comp_rst_right'] at hx
  have habsorb : ∀ {Z : C} (k : Z ⟶ Q),
      rst (k ≫ c) ≫ (k ≫ rst c) = k ≫ rst c := by
    intro Z k
    rw [← Category.assoc, hR4 k, Category.assoc, hidem]
  have hrec : ∀ {Z T : C} (k : Z ⟶ Q) (r : T ⟶ Z),
      rst r = 𝟙 T → r ≫ rst (k ≫ c) = r → rst (r ≫ k) = 𝟙 T := by
    intro Z T k r hr hrd
    have hk : r ≫ rst k = r :=
      calc r ≫ rst k = (r ≫ rst (k ≫ c)) ≫ rst k := by rw [hrd]
        _ = r ≫ rst (k ≫ c) ≫ rst k := Category.assoc _ _ _
        _ = r ≫ rst (k ≫ c) := by rw [hle k]
        _ = r := hrd
    rw [rst_comp_rst_right', hk, hr]
  intro Z f g hfg
  have hcond : ∀ {T : C} (r : T ⟶ Z), rst r = 𝟙 T →
      r ≫ (⟨rst (f ≫ c), rst_rst _⟩ : DomSemilattice Z).hom = r →
      r ≫ (f ≫ rst c) = r ≫ (g ≫ rst c) := by
    intro T r hr hrd
    have hrdf : r ≫ rst (f ≫ c) = r := hrd
    have hrdg : r ≫ rst (g ≫ c) = r := by rw [← hfg]; exact hrdf
    have hx := htest (r ≫ f) (r ≫ g) (hrec f r hr hrdf) (hrec g r hr hrdg)
      (by rw [Category.assoc, Category.assoc, hfg])
    rw [Category.assoc, Category.assoc] at hx
    exact hx
  have hj := hjoint (⟨rst (f ≫ c), rst_rst _⟩ : DomSemilattice Z)
    (f ≫ rst c) (g ≫ rst c) hcond
  have hjg : rst (f ≫ c) ≫ (g ≫ rst c) = g ≫ rst c := by
    rw [hfg]; exact habsorb g
  calc f ≫ rst c = rst (f ≫ c) ≫ (f ≫ rst c) := (habsorb f).symm
    _ = rst (f ≫ c) ≫ (g ≫ rst c) := hj
    _ = g ≫ rst c := hjg

section Connected

variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]
variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

namespace DomSemilattice

/-- `d` is connected: a decomposition `d = d₀ ∨ d₁` with `d₀ d₁ = 0` has a zero
summand. -/
def IsConnected {Q : C} (d : DomSemilattice Q) : Prop :=
  ∀ d₀ d₁ : DomSemilattice Q, d = join d₀ d₁ → d₀.hom ≫ d₁.hom = 0 →
    d₀ = bot Q ∨ d₁ = bot Q

omit [RecursionCategory.Prodominical C] in
/-- Two decisions for the same complemented domain have the same underlying
morphism. -/
theorem Decision.delta_eq {Q : C} {d : DomSemilattice Q}
    {dc : Complemented d} (D E : Decision dc) : D.delta = E.delta :=
  eq_of_agree_on_complement dc (by rw [D.on_dom, E.on_dom])
    (by rw [D.on_compl, E.on_compl])

end DomSemilattice

/-! ### The coproduct branch domains -/

namespace DomSemilattice

/-- `λ = 1_Q + 0_Q`. -/
def leftBranch (Q : C) : DomSemilattice (coprod Q Q) :=
  ⟨coprod_map (𝟙 Q) 0, by
    rw [HasCoproducts.rst_coprod_map_self, PCategory.rst_id, rst_zero]⟩

/-- `ρ = 0_Q + 1_Q`. -/
def rightBranch (Q : C) : DomSemilattice (coprod Q Q) :=
  ⟨coprod_map 0 (𝟙 Q), by
    rw [HasCoproducts.rst_coprod_map_self, PCategory.rst_id, rst_zero]⟩

omit [HasRanges C] in
@[simp] lemma leftBranch_hom (Q : C) :
    (leftBranch Q).hom = coprod_map (𝟙 Q) 0 := rfl

omit [HasRanges C] in
@[simp] lemma rightBranch_hom (Q : C) :
    (rightBranch Q).hom = coprod_map 0 (𝟙 Q) := rfl

/-- `λ` and `ρ` are complementary. -/
def complementedLeftBranch (Q : C) : Complemented (leftBranch Q) where
  compl := rightBranch Q
  meet_zero := by
    rw [leftBranch_hom, rightBranch_hom, HasCoproducts.coprod_comp,
      Category.id_comp, Category.comp_id, HasCoproducts.coprod_map_zero]
  join_top := by
    apply ext'
    change HasRanges.ran (copair (coprod_map (𝟙 Q) (0 : Q ⟶ Q))
      (coprod_map (0 : Q ⟶ Q) (𝟙 Q))) = 𝟙 (coprod Q Q)
    set k := copair (coprod_map (𝟙 Q) (0 : Q ⟶ Q))
      (coprod_map (0 : Q ⟶ Q) (𝟙 Q)) with hk
    have hr : k ≫ HasRanges.ran k = k := HasRanges.comp_ran k
    have hi0k : i0 (coprod Q Q) (coprod Q Q) ≫ k
        = coprod_map (𝟙 Q) (0 : Q ⟶ Q) := by
      rw [hk]; exact HasCoproducts.i0_copair _ _
    have hi1k : i1 (coprod Q Q) (coprod Q Q) ≫ k
        = coprod_map (0 : Q ⟶ Q) (𝟙 Q) := by
      rw [hk]; exact HasCoproducts.i1_copair _ _
    have h0 : i0 Q Q ≫ coprod_map (𝟙 Q) (0 : Q ⟶ Q) = i0 Q Q := by
      rw [HasCoproducts.i0_coprod_map, Category.id_comp]
    have h1 : i1 Q Q ≫ coprod_map (0 : Q ⟶ Q) (𝟙 Q) = i1 Q Q := by
      rw [HasCoproducts.i1_coprod_map, Category.id_comp]
    have hlam : coprod_map (𝟙 Q) (0 : Q ⟶ Q) ≫ HasRanges.ran k
        = coprod_map (𝟙 Q) (0 : Q ⟶ Q) :=
      calc coprod_map (𝟙 Q) (0 : Q ⟶ Q) ≫ HasRanges.ran k
          = (i0 (coprod Q Q) (coprod Q Q) ≫ k) ≫ HasRanges.ran k := by
            rw [hi0k]
        _ = i0 (coprod Q Q) (coprod Q Q) ≫ k ≫ HasRanges.ran k :=
            Category.assoc _ _ _
        _ = i0 (coprod Q Q) (coprod Q Q) ≫ k := by rw [hr]
        _ = coprod_map (𝟙 Q) (0 : Q ⟶ Q) := hi0k
    have hrho : coprod_map (0 : Q ⟶ Q) (𝟙 Q) ≫ HasRanges.ran k
        = coprod_map (0 : Q ⟶ Q) (𝟙 Q) :=
      calc coprod_map (0 : Q ⟶ Q) (𝟙 Q) ≫ HasRanges.ran k
          = (i1 (coprod Q Q) (coprod Q Q) ≫ k) ≫ HasRanges.ran k := by
            rw [hi1k]
        _ = i1 (coprod Q Q) (coprod Q Q) ≫ k ≫ HasRanges.ran k :=
            Category.assoc _ _ _
        _ = i1 (coprod Q Q) (coprod Q Q) ≫ k := by rw [hr]
        _ = coprod_map (0 : Q ⟶ Q) (𝟙 Q) := hi1k
    apply HasCoproducts.hom_ext
    · calc i0 Q Q ≫ HasRanges.ran k
          = (i0 Q Q ≫ coprod_map (𝟙 Q) (0 : Q ⟶ Q)) ≫ HasRanges.ran k := by
            rw [h0]
        _ = i0 Q Q ≫ coprod_map (𝟙 Q) (0 : Q ⟶ Q) ≫ HasRanges.ran k :=
            Category.assoc _ _ _
        _ = i0 Q Q ≫ coprod_map (𝟙 Q) (0 : Q ⟶ Q) := by rw [hlam]
        _ = i0 Q Q := h0
        _ = i0 Q Q ≫ 𝟙 (coprod Q Q) := (Category.comp_id _).symm
    · calc i1 Q Q ≫ HasRanges.ran k
          = (i1 Q Q ≫ coprod_map (0 : Q ⟶ Q) (𝟙 Q)) ≫ HasRanges.ran k := by
            rw [h1]
        _ = i1 Q Q ≫ coprod_map (0 : Q ⟶ Q) (𝟙 Q) ≫ HasRanges.ran k :=
            Category.assoc _ _ _
        _ = i1 Q Q ≫ coprod_map (0 : Q ⟶ Q) (𝟙 Q) := by rw [hrho]
        _ = i1 Q Q := h1
        _ = i1 Q Q ≫ 𝟙 (coprod Q Q) := (Category.comp_id _).symm

/-- `c_d = [d⊥, d] : Q + Q ⟶ Q`. -/
def decisionCollapse {Q : C} {d : DomSemilattice Q} (dc : Complemented d) :
    coprod Q Q ⟶ Q :=
  copair dc.compl.hom d.hom

omit [RecursionCategory.Prodominical C] in
/-- `rst c_d = d⊥ + d`. -/
lemma rst_decisionCollapse {Q : C} {d : DomSemilattice Q}
    (dc : Complemented d) :
    rst (decisionCollapse dc) = coprod_map dc.compl.hom d.hom := by
  dsimp only [decisionCollapse]
  rw [HasCoproducts.rst_copair, dc.compl.isDomain, d.isDomain]

/-! ### Decomposing a connected domain along a complemented pair -/

omit [CoprodStruct C] [HasCoproducts C] [Limits.HasZeroMorphisms C]
  [RecursionCategory.Prodominical C] in
/-- `ran (kγ) = γ` when `ran k = 1`. Precomposition by a morphism of total
range does not shrink a domain, and the range calculus alone proves it. -/
lemma ran_comp_dom {W X : C} {k : W ⟶ X} (hk : HasRanges.ran k = 𝟙 X)
    (γ : DomSemilattice X) : HasRanges.ran (k ≫ γ.hom) = γ.hom := by
  have hle : HasRanges.ran (k ≫ γ.hom) ≫ γ.hom = HasRanges.ran (k ≫ γ.hom) :=
    HasRanges.ran_le_of_receives _ (by rw [Category.assoc, γ.idem])
  have hge : γ.hom ≫ HasRanges.ran (k ≫ γ.hom) = γ.hom := by
    have h := HasRanges.ran_uniq k (γ.hom ≫ HasRanges.ran (k ≫ γ.hom)) γ.hom
      (by rw [← Category.assoc, HasRanges.comp_ran])
    rwa [hk, Category.id_comp, Category.id_comp] at h
  have hcomm := PCategory.rst_comm' (HasRanges.ran (k ≫ γ.hom)) γ.hom
  rw [HasRanges.rst_ran, γ.isDomain] at hcomm
  calc HasRanges.ran (k ≫ γ.hom)
      = HasRanges.ran (k ≫ γ.hom) ≫ γ.hom := hle.symm
    _ = γ.hom ≫ HasRanges.ran (k ≫ γ.hom) := hcomm
    _ = γ.hom := hge

lemma join_bot {X : C} (x : DomSemilattice X) : join x (bot X) = x :=
  le_antisymm (join_le le_rfl (bot_le x)) (left_le_join x (bot X))

lemma bot_join {X : C} (x : DomSemilattice X) : join (bot X) x = x :=
  le_antisymm (join_le (bot_le x) le_rfl) (right_le_join (bot X) x)

/-- A connected domain lies under one side of a complemented pair. The
decomposition `γ = γa ∨ γa⊥` needs no distributivity: it is `ran_comp_dom`
applied to `[a, a⊥]`, whose range is `a ∨ a⊥ = 1`. -/
lemma IsConnected.le_or_le_compl {X : C} {a : DomSemilattice X}
    (ac : Complemented a) {γ : DomSemilattice X} (hγ : γ.IsConnected) :
    γ.hom ≫ a.hom = γ.hom ∨ γ.hom ≫ ac.compl.hom = γ.hom := by
  have hk : HasRanges.ran (copair a.hom ac.compl.hom) = 𝟙 X := by
    have h := congrArg DomSemilattice.hom ac.join_top
    rwa [join_hom, top_hom] at h
  have hjoin : γ = join (meet a γ) (meet ac.compl γ) := by
    apply ext'
    rw [join_hom, meet_hom, meet_hom, ← HasCoproducts.copair_comp,
      ran_comp_dom hk γ]
  have hmeet : (meet a γ).hom ≫ (meet ac.compl γ).hom = 0 := by
    rw [meet_hom, meet_hom]
    calc (a.hom ≫ γ.hom) ≫ ac.compl.hom ≫ γ.hom
        = a.hom ≫ (γ.hom ≫ ac.compl.hom) ≫ γ.hom := by
          simp only [Category.assoc]
      _ = a.hom ≫ (ac.compl.hom ≫ γ.hom) ≫ γ.hom := by rw [comm γ ac.compl]
      _ = a.hom ≫ ac.compl.hom ≫ γ.hom ≫ γ.hom := by simp only [Category.assoc]
      _ = a.hom ≫ ac.compl.hom ≫ γ.hom := by rw [γ.idem]
      _ = (a.hom ≫ ac.compl.hom) ≫ γ.hom := (Category.assoc _ _ _).symm
      _ = (0 : X ⟶ X) ≫ γ.hom := by rw [ac.meet_zero]
      _ = 0 := Limits.zero_comp
  have key : ∀ b : DomSemilattice X, γ.hom = b.hom ≫ γ.hom →
      γ.hom ≫ b.hom = γ.hom := by
    intro b hb
    calc γ.hom ≫ b.hom = (b.hom ≫ γ.hom) ≫ b.hom := by rw [← hb]
      _ = b.hom ≫ γ.hom ≫ b.hom := Category.assoc _ _ _
      _ = b.hom ≫ b.hom ≫ γ.hom := by rw [comm γ b]
      _ = (b.hom ≫ b.hom) ≫ γ.hom := (Category.assoc _ _ _).symm
      _ = b.hom ≫ γ.hom := by rw [b.idem]
      _ = γ.hom := hb.symm
  rcases hγ (meet a γ) (meet ac.compl γ) hjoin hmeet with h | h
  · right
    refine key ac.compl ?_
    have hx := hjoin
    rw [h, bot_join] at hx
    exact congrArg DomSemilattice.hom hx
  · left
    refine key a ?_
    have hx := hjoin
    rw [h, join_bot] at hx
    exact congrArg DomSemilattice.hom hx

/-! ### Factoring through a branch -/

omit [HasRanges C] in
/-- `λ = [ι₀, 0]`. -/
lemma leftBranch_eq_copair (Q : C) :
    (leftBranch Q).hom = copair (i0 Q Q) (0 : Q ⟶ coprod Q Q) := by
  rw [leftBranch_hom, HasCoproducts.coprod_map_eq_copair, Category.id_comp,
    Limits.zero_comp]

omit [HasRanges C] in
/-- `ρ = [0, ι₁]`. -/
lemma rightBranch_eq_copair (Q : C) :
    (rightBranch Q).hom = copair (0 : Q ⟶ coprod Q Q) (i1 Q Q) := by
  rw [rightBranch_hom, HasCoproducts.coprod_map_eq_copair, Category.id_comp,
    Limits.zero_comp]

omit [HasRanges C] in
/-- `ι₀ ∇ λ = λ`: the left branch is recovered from the codiagonal. -/
lemma leftBranch_codiag_i0 (Q : C) :
    (leftBranch Q).hom ≫ codiag Q ≫ i0 Q Q = (leftBranch Q).hom := by
  rw [leftBranch_eq_copair, HasCoproducts.copair_comp, Limits.zero_comp,
    ← Category.assoc, HasCoproducts.i0_codiag, Category.id_comp]

omit [HasRanges C] in
/-- `ι₁ ∇ ρ = ρ`. -/
lemma rightBranch_codiag_i1 (Q : C) :
    (rightBranch Q).hom ≫ codiag Q ≫ i1 Q Q = (rightBranch Q).hom := by
  rw [rightBranch_eq_copair, HasCoproducts.copair_comp, Limits.zero_comp,
    ← Category.assoc, HasCoproducts.i1_codiag, Category.id_comp]

/-- On a connected domain a total morphism into `Q + Q` factors through one of
the two injections. The two branch domains pull back to a complemented pair by
`complementedInvImage`, and connectedness selects a side. -/
lemma connected_branch
    (hdense : ∀ {Z : C} (e : DomSemilattice Z), IsDense e → e.hom = 𝟙 Z)
    {W Q : C} (u : W ⟶ coprod Q Q) (hu : rst u = 𝟙 W)
    {γ : DomSemilattice W} (hγ : γ.IsConnected) :
    γ.hom ≫ u = (γ.hom ≫ u ≫ codiag Q) ≫ i0 Q Q ∨
      γ.hom ≫ u = (γ.hom ≫ u ≫ codiag Q) ≫ i1 Q Q := by
  have hpast : ∀ b : DomSemilattice (coprod Q Q),
      (invImage u b).hom ≫ u = u ≫ b.hom := by
    intro b
    have hx := PCategory.rst_comp' u b.hom
    rwa [b.isDomain] at hx
  -- The complement of `complementedInvImage` is `invImage u ρ`; keeping the
  -- term inline lets that projection reduce.
  rcases IsConnected.le_or_le_compl
      (complementedInvImage u hu (fun e he => hdense e he)
        (complementedLeftBranch Q)) hγ with h | h
  · left
    have h' : γ.hom ≫ (invImage u (leftBranch Q)).hom = γ.hom := h
    have hb : γ.hom ≫ u ≫ (leftBranch Q).hom = γ.hom ≫ u := by
      rw [← hpast (leftBranch Q), ← Category.assoc, h']
    refine Eq.symm ?_
    calc (γ.hom ≫ u ≫ codiag Q) ≫ i0 Q Q
        = γ.hom ≫ u ≫ codiag Q ≫ i0 Q Q := by simp only [Category.assoc]
      _ = (γ.hom ≫ u ≫ (leftBranch Q).hom) ≫ codiag Q ≫ i0 Q Q := by
          rw [hb, Category.assoc]
      _ = γ.hom ≫ u ≫ (leftBranch Q).hom ≫ codiag Q ≫ i0 Q Q := by
          simp only [Category.assoc]
      _ = γ.hom ≫ u ≫ (leftBranch Q).hom := by rw [leftBranch_codiag_i0]
      _ = γ.hom ≫ u := hb
  · right
    -- `ac.compl` is `invImage u ρ`; the goal spells it out.
    have h' : γ.hom ≫ (invImage u (rightBranch Q)).hom = γ.hom := h
    have hb : γ.hom ≫ u ≫ (rightBranch Q).hom = γ.hom ≫ u := by
      rw [← hpast (rightBranch Q), ← Category.assoc, h']
    refine Eq.symm ?_
    calc (γ.hom ≫ u ≫ codiag Q) ≫ i1 Q Q
        = γ.hom ≫ u ≫ codiag Q ≫ i1 Q Q := by simp only [Category.assoc]
      _ = (γ.hom ≫ u ≫ (rightBranch Q).hom) ≫ codiag Q ≫ i1 Q Q := by
          rw [hb, Category.assoc]
      _ = γ.hom ≫ u ≫ (rightBranch Q).hom ≫ codiag Q ≫ i1 Q Q := by
          simp only [Category.assoc]
      _ = γ.hom ≫ u ≫ (rightBranch Q).hom := by rw [rightBranch_codiag_i1]
      _ = γ.hom ≫ u := hb

end DomSemilattice

/-- The category is locally connected: connected domains are jointly
epimorphic. -/
def LocallyConnected (C : Type u) [Category.{v} C] [PCategoryStruct C]
    [PCategory C] [HasRanges C] [CoprodStruct C] [HasCoproducts C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] : Prop :=
  ∀ {Q R : C} (f g : Q ⟶ R),
    (∀ d : DomSemilattice Q, d.IsConnected → d.hom ≫ f = d.hom ≫ g) → f = g

open DomSemilattice in
/-- Local connectedness supplies decisions: every complemented domain has one.
Uniqueness is `DomSemilattice.Decision.delta_eq`. The dense-totality hypothesis
is route (ii) of the manuscript's lemma on inverse images of complements; the
`rP`-plus-distributivity route is not formalized. -/
theorem existsDecision_of_locallyConnected [HasWeakChoice C]
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C)
    (hlc : LocallyConnected C)
    (hdense : ∀ {Z : C} (e : DomSemilattice Z), IsDense e → e.hom = 𝟙 Z)
    {Q : C} {d : DomSemilattice Q} (dc : Complemented d) :
    Nonempty (DomSemilattice.Decision dc) := by
  have hi0c : i0 Q Q ≫ decisionCollapse dc = dc.compl.hom := by
    dsimp only [decisionCollapse]; exact HasCoproducts.i0_copair _ _
  have hi1c : i1 Q Q ≫ decisionCollapse dc = d.hom := by
    dsimp only [decisionCollapse]; exact HasCoproducts.i1_copair _ _
  have hi0r : i0 Q Q ≫ rst (decisionCollapse dc) = dc.compl.hom ≫ i0 Q Q := by
    rw [rst_decisionCollapse, HasCoproducts.i0_coprod_map]
  have hi1r : i1 Q Q ≫ rst (decisionCollapse dc) = d.hom ≫ i1 Q Q := by
    rw [rst_decisionCollapse, HasCoproducts.i1_coprod_map]
  -- A morphism received by both `d` and `d⊥` is zero.
  have hzero : ∀ {W : C} (x y : W ⟶ Q), x ≫ dc.compl.hom = y ≫ d.hom →
      x ≫ dc.compl.hom = 0 := by
    intro W x y hxy
    have h1 : (x ≫ dc.compl.hom) ≫ dc.compl.hom = x ≫ dc.compl.hom := by
      rw [Category.assoc, dc.compl.idem]
    have h2 : (x ≫ dc.compl.hom) ≫ d.hom = x ≫ dc.compl.hom := by
      rw [hxy, Category.assoc, d.idem]
    calc x ≫ dc.compl.hom
        = ((x ≫ dc.compl.hom) ≫ d.hom) ≫ dc.compl.hom := by rw [h2, h1]
      _ = (x ≫ dc.compl.hom) ≫ d.hom ≫ dc.compl.hom := Category.assoc _ _ _
      _ = (x ≫ dc.compl.hom) ≫ 0 := by rw [dc.meet_zero]
      _ = 0 := Limits.comp_zero
  -- The three branch combinations, up to symmetry.
  have hsame0 : ∀ {W : C} (x y : W ⟶ Q),
      (x ≫ i0 Q Q) ≫ decisionCollapse dc = (y ≫ i0 Q Q) ≫ decisionCollapse dc →
      (x ≫ i0 Q Q) ≫ rst (decisionCollapse dc)
        = (y ≫ i0 Q Q) ≫ rst (decisionCollapse dc) := by
    intro W x y h
    rw [Category.assoc, hi0c, Category.assoc, hi0c] at h
    calc (x ≫ i0 Q Q) ≫ rst (decisionCollapse dc)
        = x ≫ i0 Q Q ≫ rst (decisionCollapse dc) := Category.assoc _ _ _
      _ = x ≫ dc.compl.hom ≫ i0 Q Q := by rw [hi0r]
      _ = (x ≫ dc.compl.hom) ≫ i0 Q Q := (Category.assoc _ _ _).symm
      _ = (y ≫ dc.compl.hom) ≫ i0 Q Q := by rw [h]
      _ = y ≫ dc.compl.hom ≫ i0 Q Q := Category.assoc _ _ _
      _ = y ≫ i0 Q Q ≫ rst (decisionCollapse dc) := by rw [hi0r]
      _ = (y ≫ i0 Q Q) ≫ rst (decisionCollapse dc) := (Category.assoc _ _ _).symm
  have hsame1 : ∀ {W : C} (x y : W ⟶ Q),
      (x ≫ i1 Q Q) ≫ decisionCollapse dc = (y ≫ i1 Q Q) ≫ decisionCollapse dc →
      (x ≫ i1 Q Q) ≫ rst (decisionCollapse dc)
        = (y ≫ i1 Q Q) ≫ rst (decisionCollapse dc) := by
    intro W x y h
    rw [Category.assoc, hi1c, Category.assoc, hi1c] at h
    calc (x ≫ i1 Q Q) ≫ rst (decisionCollapse dc)
        = x ≫ i1 Q Q ≫ rst (decisionCollapse dc) := Category.assoc _ _ _
      _ = x ≫ d.hom ≫ i1 Q Q := by rw [hi1r]
      _ = (x ≫ d.hom) ≫ i1 Q Q := (Category.assoc _ _ _).symm
      _ = (y ≫ d.hom) ≫ i1 Q Q := by rw [h]
      _ = y ≫ d.hom ≫ i1 Q Q := Category.assoc _ _ _
      _ = y ≫ i1 Q Q ≫ rst (decisionCollapse dc) := by rw [hi1r]
      _ = (y ≫ i1 Q Q) ≫ rst (decisionCollapse dc) := (Category.assoc _ _ _).symm
  have hcross : ∀ {W : C} (x y : W ⟶ Q),
      (x ≫ i0 Q Q) ≫ decisionCollapse dc = (y ≫ i1 Q Q) ≫ decisionCollapse dc →
      (x ≫ i0 Q Q) ≫ rst (decisionCollapse dc)
        = (y ≫ i1 Q Q) ≫ rst (decisionCollapse dc) := by
    intro W x y h
    rw [Category.assoc, hi0c, Category.assoc, hi1c] at h
    have hx0 : x ≫ dc.compl.hom = 0 := hzero x y h
    have hy0 : y ≫ d.hom = 0 := by rw [← h, hx0]
    calc (x ≫ i0 Q Q) ≫ rst (decisionCollapse dc)
        = x ≫ i0 Q Q ≫ rst (decisionCollapse dc) := Category.assoc _ _ _
      _ = x ≫ dc.compl.hom ≫ i0 Q Q := by rw [hi0r]
      _ = (x ≫ dc.compl.hom) ≫ i0 Q Q := (Category.assoc _ _ _).symm
      _ = (0 : W ⟶ Q) ≫ i0 Q Q := by rw [hx0]
      _ = 0 := Limits.zero_comp
      _ = (0 : W ⟶ Q) ≫ i1 Q Q := Limits.zero_comp.symm
      _ = (y ≫ d.hom) ≫ i1 Q Q := by rw [hy0]
      _ = y ≫ d.hom ≫ i1 Q Q := Category.assoc _ _ _
      _ = y ≫ i1 Q Q ≫ rst (decisionCollapse dc) := by rw [hi1r]
      _ = (y ≫ i1 Q Q) ≫ rst (decisionCollapse dc) := (Category.assoc _ _ _).symm
  -- Step 1: `c_d` is a partial monomorphism.
  have htest : ∀ {W : C} (f g : W ⟶ coprod Q Q), rst f = 𝟙 W → rst g = 𝟙 W →
      f ≫ decisionCollapse dc = g ≫ decisionCollapse dc →
      f ≫ rst (decisionCollapse dc) = g ≫ rst (decisionCollapse dc) := by
    intro W f g hf hg hfg
    refine hlc (f ≫ rst (decisionCollapse dc)) (g ≫ rst (decisionCollapse dc)) ?_
    intro γ hγ
    rw [← Category.assoc, ← Category.assoc]
    have hfgγ : (γ.hom ≫ f) ≫ decisionCollapse dc
        = (γ.hom ≫ g) ≫ decisionCollapse dc := by
      rw [Category.assoc, Category.assoc, hfg]
    rcases connected_branch hdense f hf hγ with hb | hb
    · rcases connected_branch hdense g hg hγ with hb' | hb'
      · rw [hb, hb'] at hfgγ ⊢
        exact hsame0 _ _ hfgγ
      · rw [hb, hb'] at hfgγ ⊢
        exact hcross _ _ hfgγ
    · rcases connected_branch hdense g hg hγ with hb' | hb'
      · rw [hb, hb'] at hfgγ ⊢
        exact (hcross _ _ hfgγ.symm).symm
      · rw [hb, hb'] at hfgγ ⊢
        exact hsame1 _ _ hfgγ
  have hmono : IsPartialMono (decisionCollapse dc) :=
    isPartialMono_of_total_test hjoint _ htest
  -- Step 2: weak choice supplies a section, total because `ran c_d = 1`.
  obtain ⟨δ, hδ⟩ := HasWeakChoice.exists_isSection (decisionCollapse dc) hmono
  have hjoinc : join dc.compl d = top Q := by
    have hswap : join dc.compl d = join d dc.compl :=
      le_antisymm (join_le (right_le_join d dc.compl) (left_le_join d dc.compl))
        (join_le (right_le_join dc.compl d) (left_le_join dc.compl d))
    rw [hswap]
    exact dc.join_top
  have hran : HasRanges.ran (decisionCollapse dc) = 𝟙 Q := by
    dsimp only [decisionCollapse]
    have h := congrArg DomSemilattice.hom hjoinc
    rwa [join_hom, top_hom] at h
  have hδtotal : rst δ = 𝟙 Q := by rw [hδ.rst_eq_ran, hran]
  have hδc : δ ≫ decisionCollapse dc = 𝟙 Q := by rw [hδ.comp_eq_rst, hδtotal]
  have hδrst : δ ≫ rst (decisionCollapse dc) = δ := by
    have h := PCategory.rst_comp' δ (decisionCollapse dc)
    rw [hδc, PCategory.rst_id, Category.id_comp] at h
    exact h.symm
  -- Step 3: the two branch equations.
  have hon_dom : d.hom ≫ δ = d.hom ≫ i1 Q Q := by
    have h1 : (d.hom ≫ δ) ≫ decisionCollapse dc
        = (d.hom ≫ i1 Q Q) ≫ decisionCollapse dc := by
      rw [Category.assoc, hδc, Category.comp_id, Category.assoc, hi1c, d.idem]
    have h2 := hmono (d.hom ≫ δ) (d.hom ≫ i1 Q Q) h1
    calc d.hom ≫ δ = d.hom ≫ δ ≫ rst (decisionCollapse dc) := by rw [hδrst]
      _ = (d.hom ≫ δ) ≫ rst (decisionCollapse dc) := (Category.assoc _ _ _).symm
      _ = (d.hom ≫ i1 Q Q) ≫ rst (decisionCollapse dc) := h2
      _ = d.hom ≫ i1 Q Q ≫ rst (decisionCollapse dc) := Category.assoc _ _ _
      _ = d.hom ≫ d.hom ≫ i1 Q Q := by rw [hi1r]
      _ = (d.hom ≫ d.hom) ≫ i1 Q Q := (Category.assoc _ _ _).symm
      _ = d.hom ≫ i1 Q Q := by rw [d.idem]
  have hon_compl : dc.compl.hom ≫ δ = dc.compl.hom ≫ i0 Q Q := by
    have h1 : (dc.compl.hom ≫ δ) ≫ decisionCollapse dc
        = (dc.compl.hom ≫ i0 Q Q) ≫ decisionCollapse dc := by
      rw [Category.assoc, hδc, Category.comp_id, Category.assoc, hi0c,
        dc.compl.idem]
    have h2 := hmono (dc.compl.hom ≫ δ) (dc.compl.hom ≫ i0 Q Q) h1
    calc dc.compl.hom ≫ δ
        = dc.compl.hom ≫ δ ≫ rst (decisionCollapse dc) := by rw [hδrst]
      _ = (dc.compl.hom ≫ δ) ≫ rst (decisionCollapse dc) :=
          (Category.assoc _ _ _).symm
      _ = (dc.compl.hom ≫ i0 Q Q) ≫ rst (decisionCollapse dc) := h2
      _ = dc.compl.hom ≫ i0 Q Q ≫ rst (decisionCollapse dc) :=
          Category.assoc _ _ _
      _ = dc.compl.hom ≫ dc.compl.hom ≫ i0 Q Q := by rw [hi0r]
      _ = (dc.compl.hom ≫ dc.compl.hom) ≫ i0 Q Q := (Category.assoc _ _ _).symm
      _ = dc.compl.hom ≫ i0 Q Q := by rw [dc.compl.idem]
  exact ⟨{ delta := δ
           delta_total := hδtotal
           on_dom := hon_dom
           on_compl := hon_compl }⟩

end Connected

end CategoryTheory
