/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Unions
public import RiceShapiro.Decisions

/-!
# The case-distinction laws

The manuscript's proposition "case-distinction laws" and its supporting
reindexing calculus.

The parameter morphism is `param a i k = ⟨⟨a, i⟩, k⟩ ⊠ 1_X`, the manuscript's
`t_{a,i,k}`, and `caseAt` is `Case_s(a,i,k) = Case_s t_{a,i,k}`. Reindexing
along `param` sends `α̂`, `ε̂`, `U` and `D` to `α_a`, `ε_i`, `U_k` and `d_a`, in
`param_alphaHat`, `param_evHat`, `param_restrU` and `caseDom_hom_eq`.

The three laws are `case_law_zero`, `case_law_entry` and `case_law_eq`. Each
takes the equation `d_a ∨ d_a⊥ = 1` as a hypothesis. `caseJoin_of_dense`
supplies it by route (ii), from totality of the parameter morphism and the
hypothesis that every dense domain on `Z ⊠ X` is total. Route (i), which
supplies the same equation in an `rP`-category with distributive binary
coproducts, is not formalized.

`case_law_entry` and `case_law_eq` do not assume `Prodominical`: they use the
join equation alone. `case_law_zero` assumes it, for `(u_k r) ⊠ 1_X = 0` and
for the meet equation of the complement.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open PCategoryStruct PCategory DomSemilattice

variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable [HasRanges C] [CoprodStruct C] [HasCoproducts C]
variable [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]

namespace ApproximationDatum

open DomSemilattice

variable {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)
variable {Z : C} (a : Z ⟶ 𝒜.A) (i k : Z ⟶ 𝒜.I)

/-- `t_{a,i,k} = ⟨⟨a, i⟩, k⟩ ⊠ 1_X`. -/
def param : nearProd Z X ⟶ 𝒜.caseQ :=
  nearProd_map (partialPairing (partialPairing a i) k) (𝟙 X)

/-! ### Reindexing calculus -/

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
lemma pairing_projA (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    partialPairing (partialPairing a i) k ≫ 𝒜.projA = a := by
  dsimp only [projA]
  rw [← Category.assoc, p0_partialPairing, hk, Category.id_comp,
    p0_partialPairing, hi, Category.id_comp]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
lemma pairing_projI (ha : rst a = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    partialPairing (partialPairing a i) k ≫ 𝒜.projI = i := by
  dsimp only [projI]
  rw [← Category.assoc, p0_partialPairing, hk, Category.id_comp,
    p1_partialPairing, ha, Category.id_comp]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
lemma pairing_projK (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) :
    partialPairing (partialPairing a i) k ≫ 𝒜.projK = k := by
  dsimp only [projK]
  rw [p1_partialPairing, rst_partialPairing, ha, hi, Category.comp_id,
    Category.id_comp]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
lemma param_total (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    rst (𝒜.param a i k) = 𝟙 (nearProd Z X) := by
  dsimp only [param]
  rw [PCategory.rst_nearProd_map, rst_partialPairing, rst_partialPairing,
    ha, hi, hk, Category.comp_id, Category.comp_id, PCategory.rst_id,
    PCategory.nearProd_id]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `α̂ t_{a,i,k} = α_a`. -/
lemma param_alphaHat (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    𝒜.param a i k ≫ 𝒜.alphaHat = evalAt 𝒜.approx a := by
  dsimp only [param, alphaHat, evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id,
    𝒜.pairing_projA a i k hi hk]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `ε̂ t_{a,i,k} = ε_i`. -/
lemma param_evHat (ha : rst a = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    𝒜.param a i k ≫ 𝒜.evHat = evalAt 𝒜.ev i := by
  dsimp only [param, evHat, evalAt]
  rw [← Category.assoc, PCategory.nearProd_comp, Category.comp_id,
    𝒜.pairing_projI a i k ha hk]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `U t_{a,i,k} = t_{a,i,k} U_k`. -/
lemma param_restrU (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) :
    𝒜.param a i k ≫ 𝒜.restrU s
      = nearProd_map (entry s k) (𝟙 X) ≫ 𝒜.param a i k := by
  have hx := comp_entry s (partialPairing (partialPairing a i) k) 𝒜.projK
  rw [𝒜.pairing_projK a i k ha hi] at hx
  dsimp only [param, restrU]
  rw [PCategory.nearProd_comp, PCategory.nearProd_comp, Category.comp_id, hx]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `ε̂ U t_{a,i,k} = ε_i U_k`. -/
lemma param_restrU_evHat (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z)
    (hk : rst k = 𝟙 Z) :
    𝒜.param a i k ≫ 𝒜.restrU s ≫ 𝒜.evHat
      = nearProd_map (entry s k) (𝟙 X) ≫ evalAt 𝒜.ev i := by
  rw [← Category.assoc, 𝒜.param_restrU s a i k ha hi, Category.assoc,
    𝒜.param_evHat a i k ha hk]

/-- `d_a = rst (D t_{a,i,k})`. -/
def caseDom : DomSemilattice (nearProd Z X) :=
  invImage (𝒜.param a i k) 𝒜.domD

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `d_a = rst α_a`. -/
lemma caseDom_hom_eq (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    (𝒜.caseDom a i k).hom = rst (evalAt 𝒜.approx a) := by
  dsimp only [caseDom, DomSemilattice.invImage, domD]
  rw [← rst_comp_rst_right', 𝒜.param_alphaHat a i k hi hk]

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
/-- `d_a t_{a,i,k} = t_{a,i,k} D`, the R4 identity used to reindex the first
branch equation. -/
lemma caseDom_comp_param :
    (𝒜.caseDom a i k).hom ≫ 𝒜.param a i k
      = 𝒜.param a i k ≫ 𝒜.domD.hom := by
  have hx := PCategory.rst_comp' (𝒜.param a i k) 𝒜.domD.hom
  rwa [𝒜.domD.isDomain] at hx

variable (cd : 𝒜.CaseData)

/-- `d_a⊥ = rst (D⊥ t_{a,i,k})`. -/
def caseCompl : DomSemilattice (nearProd Z X) :=
  invImage (𝒜.param a i k) cd.complemented.compl

omit [HasCoproducts C] [RecursionCategory.Prodominical C] in
lemma caseCompl_comp_param :
    (𝒜.caseCompl a i k cd).hom ≫ 𝒜.param a i k
      = 𝒜.param a i k ≫ cd.complemented.compl.hom := by
  have hx := PCategory.rst_comp' (𝒜.param a i k) cd.complemented.compl.hom
  rwa [cd.complemented.compl.isDomain] at hx

/-- `d_a` is complemented by `d_a⊥` once `d_a ∨ d_a⊥ = 1` is supplied. The
meet clause needs no further hypothesis. -/
def caseComplemented (ht : rst (𝒜.param a i k) = 𝟙 (nearProd Z X))
    (hjoin : join (𝒜.caseDom a i k) (𝒜.caseCompl a i k cd)
      = top (nearProd Z X)) : Complemented (𝒜.caseDom a i k) where
  compl := 𝒜.caseCompl a i k cd
  meet_zero :=
    (isQuasicomplement_invImage (𝒜.param a i k) ht
      cd.complemented.isQuasicomplement).1
  join_top := hjoin

/-! ### The reindexed branch equations -/

omit [RecursionCategory.Prodominical C] in
/-- `F d_a = α_a`. -/
lemma case_reindex_dom (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    (𝒜.caseDom a i k).hom ≫ (𝒜.param a i k ≫ 𝒜.Case s cd)
      = evalAt 𝒜.approx a := by
  rw [← Category.assoc, 𝒜.caseDom_comp_param a i k, Category.assoc,
    𝒜.case_on_domD s cd, 𝒜.param_alphaHat a i k hi hk]

omit [RecursionCategory.Prodominical C] in
/-- `F d_a⊥ = ε_i U_k d_a⊥`. -/
lemma case_reindex_compl (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z)
    (hk : rst k = 𝟙 Z) :
    (𝒜.caseCompl a i k cd).hom ≫ (𝒜.param a i k ≫ 𝒜.Case s cd)
      = (𝒜.caseCompl a i k cd).hom
        ≫ nearProd_map (entry s k) (𝟙 X) ≫ evalAt 𝒜.ev i := by
  rw [← Category.assoc, 𝒜.caseCompl_comp_param a i k cd, Category.assoc,
    𝒜.case_on_compl s cd, ← Category.assoc,
    ← 𝒜.caseCompl_comp_param a i k cd, Category.assoc,
    𝒜.param_restrU_evHat s a i k ha hi hk]

/-! ### The indexed case morphism -/

/-- `Case_s(a,i,k) = Case_s t_{a,i,k}`. -/
def caseAt : nearProd Z X ⟶ Y := 𝒜.param a i k ≫ 𝒜.Case s cd

/-- `U_k = u_k ⊠ 1_X` as a domain on `Z ⊠ X`. -/
def entryDom : DomSemilattice (nearProd Z X) :=
  (⟨entry s k, rst_entry s k⟩ : DomSemilattice Z).rightTimes X

omit [HasRanges C] [CoprodStruct C] [HasCoproducts C]
  [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C] in
@[simp] lemma entryDom_hom :
    (𝒜.entryDom s k : DomSemilattice (nearProd Z X)).hom
      = nearProd_map (entry s k) (𝟙 X) := rfl

omit [RecursionCategory.Prodominical C] in
lemma caseAt_dom (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    (𝒜.caseDom a i k).hom ≫ 𝒜.caseAt s a i k cd = evalAt 𝒜.approx a :=
  𝒜.case_reindex_dom s a i k cd hi hk

omit [RecursionCategory.Prodominical C] in
lemma caseAt_compl (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z) :
    (𝒜.caseCompl a i k cd).hom ≫ 𝒜.caseAt s a i k cd
      = (𝒜.caseCompl a i k cd).hom
        ≫ (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i :=
  𝒜.case_reindex_compl s a i k cd ha hi hk

/-! ### Route (ii) -/

/-- `d_a ∨ d_a⊥ = 1`, from totality of the parameter morphism and totality of
the dense domains on `Z ⊠ X`. -/
lemma caseJoin_of_dense (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z)
    (hk : rst k = 𝟙 Z)
    (hdense : ∀ h : DomSemilattice (nearProd Z X), IsDense h
      → h.hom = 𝟙 (nearProd Z X)) :
    join (𝒜.caseDom a i k) (𝒜.caseCompl a i k cd) = top (nearProd Z X) :=
  (complementedInvImage (𝒜.param a i k) (𝒜.param_total a i k ha hi hk) hdense
    cd.complemented).join_top

/-! ### The case-distinction laws -/

/-- Law (i): off the entry domain the case morphism agrees with the
approximant. -/
theorem case_law_zero (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z)
    (hjoin : join (𝒜.caseDom a i k) (𝒜.caseCompl a i k cd)
      = top (nearProd Z X)) (r : DomSemilattice Z)
    (hr : r.hom ≫ entry s k = 0) :
    (r.rightTimes X).hom ≫ 𝒜.caseAt s a i k cd
      = (r.rightTimes X).hom ≫ evalAt 𝒜.approx a := by
  have habs : (𝒜.caseDom a i k).hom ≫ evalAt 𝒜.approx a
      = evalAt 𝒜.approx a := by
    rw [𝒜.caseDom_hom_eq a i k hi hk]
    exact RestrictionCategory.rst_comp_self _
  have hzero : (r.rightTimes X).hom ≫ (𝒜.entryDom s k).hom = 0 := by
    change nearProd_map r.hom (𝟙 X) ≫ nearProd_map (entry s k) (𝟙 X) = 0
    rw [PCategory.nearProd_comp, hr, Category.comp_id,
      RecursionCategory.Prodominical.nearProd_zero_left]
  have hmeet : (𝒜.caseCompl a i k cd).hom ≫ (𝒜.caseDom a i k).hom = 0 := by
    have h0 : (𝒜.caseDom a i k).hom ≫ (𝒜.caseCompl a i k cd).hom = 0 :=
      (isQuasicomplement_invImage (𝒜.param a i k)
        (𝒜.param_total a i k ha hi hk) cd.complemented.isQuasicomplement).1
    rw [← DomSemilattice.comm]; exact h0
  have hcompApprox : (𝒜.caseCompl a i k cd).hom ≫ evalAt 𝒜.approx a = 0 := by
    calc (𝒜.caseCompl a i k cd).hom ≫ evalAt 𝒜.approx a
        = (𝒜.caseCompl a i k cd).hom
            ≫ (𝒜.caseDom a i k).hom ≫ evalAt 𝒜.approx a := by rw [habs]
      _ = 0 := by rw [← Category.assoc, hmeet, Limits.zero_comp]
  refine eq_of_agree_on_join_top hjoin ?_ ?_
  · rw [comm_comp, 𝒜.caseAt_dom s a i k cd hi hk, comm_comp, habs]
  · calc (𝒜.caseCompl a i k cd).hom
          ≫ (r.rightTimes X).hom ≫ 𝒜.caseAt s a i k cd
        = (r.rightTimes X).hom
          ≫ (𝒜.caseCompl a i k cd).hom ≫ 𝒜.caseAt s a i k cd := comm_comp _ _ _
      _ = (r.rightTimes X).hom ≫ (𝒜.caseCompl a i k cd).hom
          ≫ (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i := by
            rw [𝒜.caseAt_compl s a i k cd ha hi hk]
      _ = (r.rightTimes X).hom ≫ (𝒜.entryDom s k).hom
          ≫ (𝒜.caseCompl a i k cd).hom ≫ evalAt 𝒜.ev i := by
            simpa only [Category.assoc] using
              congrArg (fun q => (r.rightTimes X).hom ≫ q)
                (comm_comp (𝒜.caseCompl a i k cd) (𝒜.entryDom s k)
                  (evalAt 𝒜.ev i))
      _ = ((r.rightTimes X).hom ≫ (𝒜.entryDom s k).hom)
          ≫ (𝒜.caseCompl a i k cd).hom ≫ evalAt 𝒜.ev i :=
            (Category.assoc _ _ _).symm
      _ = 0 := by rw [hzero, Limits.zero_comp]
      _ = (𝒜.caseCompl a i k cd).hom
          ≫ (r.rightTimes X).hom ≫ evalAt 𝒜.approx a := by
            rw [comm_comp (𝒜.caseCompl a i k cd) (r.rightTimes X)
              (evalAt 𝒜.approx a), hcompApprox, Limits.comp_zero]

omit [RecursionCategory.Prodominical C] in
/-- Law (ii): on the entry domain an extension witness makes the case morphism
agree with the indexed morphism. -/
theorem case_law_entry (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z)
    (hjoin : join (𝒜.caseDom a i k) (𝒜.caseCompl a i k cd)
      = top (nearProd Z X)) (hExt : 𝒜.Extends a i) :
    (𝒜.entryDom s k).hom ≫ 𝒜.caseAt s a i k cd
      = (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i := by
  have hcompat : evalAt 𝒜.approx a
      = rst (evalAt 𝒜.approx a) ≫ evalAt 𝒜.ev i := (𝒜.compat a i ha hi).mp hExt
  have hdA : (𝒜.caseDom a i k).hom ≫ evalAt 𝒜.ev i = evalAt 𝒜.approx a := by
    rw [𝒜.caseDom_hom_eq a i k hi hk, ← hcompat]
  refine eq_of_agree_on_join_top hjoin ?_ ?_
  · rw [comm_comp, 𝒜.caseAt_dom s a i k cd hi hk, comm_comp, hdA]
  · calc (𝒜.caseCompl a i k cd).hom
          ≫ (𝒜.entryDom s k).hom ≫ 𝒜.caseAt s a i k cd
        = (𝒜.entryDom s k).hom
          ≫ (𝒜.caseCompl a i k cd).hom ≫ 𝒜.caseAt s a i k cd := comm_comp _ _ _
      _ = (𝒜.entryDom s k).hom ≫ (𝒜.caseCompl a i k cd).hom
          ≫ (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i := by
            rw [𝒜.caseAt_compl s a i k cd ha hi hk]
      _ = (𝒜.caseCompl a i k cd).hom ≫ (𝒜.entryDom s k).hom
          ≫ (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i := by
            simpa only [Category.assoc] using
              comm_comp (𝒜.entryDom s k) (𝒜.caseCompl a i k cd)
                ((𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i)
      _ = (𝒜.caseCompl a i k cd).hom
          ≫ (𝒜.entryDom s k).hom ≫ evalAt 𝒜.ev i := by
            simpa only [Category.assoc] using
              congrArg
                (fun q => (𝒜.caseCompl a i k cd).hom ≫ q ≫ evalAt 𝒜.ev i)
                (𝒜.entryDom s k).idem

omit [RecursionCategory.Prodominical C] in
/-- Law (iii): if `sk = k` the case morphism equals the indexed morphism. -/
theorem case_law_eq (ha : rst a = 𝟙 Z) (hi : rst i = 𝟙 Z) (hk : rst k = 𝟙 Z)
    (hjoin : join (𝒜.caseDom a i k) (𝒜.caseCompl a i k cd)
      = top (nearProd Z X)) (hExt : 𝒜.Extends a i) (hsk : k ≫ s.hom = k) :
    𝒜.caseAt s a i k cd = evalAt 𝒜.ev i := by
  have hentry : entry s k = 𝟙 Z := by
    dsimp only [entry]; rw [hsk, hk]
  have hU : (𝒜.entryDom s k).hom = 𝟙 (nearProd Z X) := by
    rw [𝒜.entryDom_hom s k, hentry, PCategory.nearProd_id]
  have hx := 𝒜.case_law_entry s a i k cd ha hi hk hjoin hExt
  rwa [hU, Category.id_comp, Category.id_comp] at hx

end ApproximationDatum

end CategoryTheory
