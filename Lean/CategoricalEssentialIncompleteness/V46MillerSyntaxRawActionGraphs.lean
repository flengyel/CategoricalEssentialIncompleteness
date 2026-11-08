/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerSyntaxRawAction

/-! # Exact numerical child graphs of the actual polynomial action

Every leaf uses the supplied family morphism on its actual numerical code.
Outer parameter equality, ordered product children, and literal sum tags
are derived from the constructed raw action and its Over equations.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P:Uniform.Family}

private theorem totalIso_forward_inverse {U V:Total.TotalCategory P} (e:U≅V) (x y:ℕ)
    (h:y∈Total.val e.hom.hom x) : x∈Total.val e.inv.hom y := by
  have hy := Total.val_target e.hom.hom x y h
  obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp ((Total.total_iff e.inv.hom).mp e.inv.property y hy)
  have hc : z∈Total.val (e.hom≫e.inv).hom x :=
    (Total.mem_val_comp e.hom.hom e.inv.hom x z).mpr ⟨y,h,hz⟩
  rw [e.hom_inv_id] at hc
  change z∈Total.supportIdentity U.obj.support x at hc
  have he := ((Total.mem_supportIdentity U.obj.support x z).mp hc).2
  exact he ▸ hz

theorem totalIso_graph_symm {U V:Total.TotalCategory P} (e:U≅V) (x y:ℕ) :
    y∈Total.val e.hom.hom x ↔ x∈Total.val e.inv.hom y :=
  ⟨totalIso_forward_inverse e x y,totalIso_forward_inverse e.symm y x⟩

variable (R:Total.TotalCategory P) (X Y X' Y':Over R)

theorem mapped_parameter (f:X⟶X') (u v r:ℕ)
    (hr:r∈Total.val X.hom.hom u) (hf:v∈Total.val f.left.hom u) :
    r∈Total.val X'.hom.hom v := by
  have he := congrArg (fun h => Total.val h.hom u) f.w
  change Total.val (f.left.hom ≫ X'.hom.hom) u=Total.val X.hom.hom u at he
  rw [Total.val_comp,Part.eq_some_iff.mpr hf,Part.bind_some] at he
  rw [he]
  exact hr

theorem rawMorphism_parameter {a b:SyntaxPolynomial (Total.TotalCategory P)}
    (f:object R X Y a⟶object R X' Y' b) (n m:ℕ)
    (hm:m∈Total.val f.left.hom n) : (Nat.unpair m).1=(Nat.unpair n).1 :=
  ((projection_graph R X Y a n _).mp (output_parameter R X' Y' f n m hm)).2

theorem termIso_hom_graph (n m:ℕ) :
    m∈Total.val (termIso R X Y).hom.left.hom n ↔
      (Nat.unpair n).1∈Total.val X.hom.hom (Nat.unpair n).2 ∧ m=(Nat.unpair n).2 := by
  change m∈Total.val (termForward R X Y).left.hom n ↔ _
  exact termForward_graph R X Y n m

theorem termIso_inv_graph (u n:ℕ) :
    n∈Total.val (termIso R X Y).inv.left.hom u ↔
      (Nat.unpair n).1∈Total.val X.hom.hom (Nat.unpair n).2 ∧ (Nat.unpair n).2=u := by
  have h := totalIso_graph_symm ((Over.forget R).mapIso (termIso R X Y)) n u
  change (u∈Total.val (termIso R X Y).hom.left.hom n ↔
    n∈Total.val (termIso R X Y).inv.left.hom u) at h
  exact h.symm.trans ((termIso_hom_graph R X Y n u).trans
    (and_congr_right (fun _ => eq_comm)))

def ActionGraph (f:X⟶X') (g:Y⟶Y') : SyntaxPolynomial (Total.TotalCategory P) → ℕ → ℕ → ℕ → Prop
  | .term,r,u,v => r∈Total.val X.hom.hom u ∧ v∈Total.val f.left.hom u
  | .formula,r,u,v => r∈Total.val Y.hom.hom u ∧ v∈Total.val g.left.hom u
  | .coefficient C,r,u,v => r∈R.obj.support ∧ u∈C.obj.support ∧ v=u
  | .unit,r,u,v => r∈R.obj.support ∧ u=0 ∧ v=u
  | .product a b,r,u,v => ActionGraph f g a r (Nat.unpair u).1 (Nat.unpair v).1 ∧
      ActionGraph f g b r (Nat.unpair u).2 (Nat.unpair v).2
  | .sum a b,r,u,v => ((Nat.unpair u).2=0 ∧ (Nat.unpair v).2=0 ∧
      ActionGraph f g a r (Nat.unpair u).1 (Nat.unpair v).1) ∨
      ((Nat.unpair u).2=1 ∧ (Nat.unpair v).2=1 ∧
      ActionGraph f g b r (Nat.unpair u).1 (Nat.unpair v).1)

theorem ActionGraph_source (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P))
    {r u v:ℕ} (h:ActionGraph R X Y X' Y' f g p r u v) : fiber R X Y p (r,u) := by
  induction p generalizing u v with
  | term => exact h.1
  | formula => exact h.1
  | coefficient C => exact ⟨h.1,h.2.1⟩
  | unit => exact ⟨h.1,h.2.1⟩
  | product a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | sum a b ia ib =>
    change ((Nat.unpair u).2=0 ∧ fiber R X Y a (r,(Nat.unpair u).1)) ∨
      ((Nat.unpair u).2=1 ∧ fiber R X Y b (r,(Nat.unpair u).1))
    exact h.elim (fun h => Or.inl ⟨h.1,ia h.2.2⟩)
      (fun h => Or.inr ⟨h.1,ib h.2.2⟩)

theorem ActionGraph_target (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P))
    {r u v:ℕ} (h:ActionGraph R X Y X' Y' f g p r u v) : fiber R X' Y' p (r,v) := by
  induction p generalizing u v with
  | term => exact mapped_parameter R X X' f _ _ _ h.1 h.2
  | formula => exact mapped_parameter R Y Y' g _ _ _ h.1 h.2
  | coefficient C => exact ⟨h.1,h.2.2.symm ▸ h.2.1⟩
  | unit => exact ⟨h.1,h.2.2.trans h.2.1⟩
  | product a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | sum a b ia ib =>
    change ((Nat.unpair v).2=0 ∧ fiber R X' Y' a (r,(Nat.unpair v).1)) ∨
      ((Nat.unpair v).2=1 ∧ fiber R X' Y' b (r,(Nat.unpair v).1))
    exact h.elim (fun h => Or.inl ⟨h.2.1,ia h.2.2⟩)
      (fun h => Or.inr ⟨h.2.1,ib h.2.2⟩)

private theorem rawAction_term_graph (f:X⟶X') (g:Y⟶Y') (r u v:ℕ) :
    Nat.pair r v∈Total.val (rawAction R X Y X' Y' f g .term).left.hom (Nat.pair r u) ↔
      r∈Total.val X.hom.hom u ∧ v∈Total.val f.left.hom u := by
  change Nat.pair r v∈Total.val ((termIso R X Y).hom.left.hom ≫ f.left.hom ≫
    (termIso R X' Y').inv.left.hom) (Nat.pair r u) ↔ _
  simp only [Total.mem_val_comp]
  constructor
  · rintro ⟨w,hw,z,hz,ho⟩
    have hw' := (termIso_hom_graph R X Y (Nat.pair r u) w).mp hw
    have hwu:w=u := by simpa only [Nat.unpair_pair] using hw'.2
    subst w
    have ho' := (termIso_inv_graph R X' Y' z (Nat.pair r v)).mp ho
    have hvz:v=z := by simpa only [Nat.unpair_pair] using ho'.2
    subst z
    exact ⟨by simpa only [Nat.unpair_pair] using hw'.1,hz⟩
  · rintro ⟨hr,hf⟩
    refine ⟨u,(termIso_hom_graph R X Y (Nat.pair r u) u).mpr ?_,v,hf,?_⟩
    · simpa only [Nat.unpair_pair] using And.intro hr (rfl:u=u)
    · apply (termIso_inv_graph R X' Y' v (Nat.pair r v)).mpr
      simpa only [Nat.unpair_pair] using
        And.intro (mapped_parameter R X X' f u v r hr hf) (rfl:v=v)

/-- The exact recursive graph on inputs and outputs with a shared parameter. -/
theorem rawAction_graph_same_parameter (f:X⟶X') (g:Y⟶Y')
    (p:SyntaxPolynomial (Total.TotalCategory P)) (r u v:ℕ) :
    Nat.pair r v∈Total.val (rawAction R X Y X' Y' f g p).left.hom (Nat.pair r u) ↔
      ActionGraph R X Y X' Y' f g p r u v := by
  induction p generalizing u v with
  | term => exact rawAction_term_graph R X Y X' Y' f g r u v
  | formula => exact rawAction_term_graph R Y X Y' X' g f r u v
  | coefficient C =>
    change Nat.pair r v∈Total.supportIdentity (fiberCarrier R X Y (.coefficient C)).support (Nat.pair r u) ↔ _
    rw [Total.mem_supportIdentity]
    change (fiber R X Y (.coefficient C) (Nat.unpair (Nat.pair r u)) ∧
      Nat.pair r v=Nat.pair r u) ↔ _
    rw [Nat.unpair_pair]
    change ((r∈R.obj.support ∧ u∈C.obj.support) ∧ Nat.pair r v=Nat.pair r u) ↔
      r∈R.obj.support ∧ u∈C.obj.support ∧ v=u
    constructor
    · rintro ⟨⟨hr,hu⟩,he⟩
      exact ⟨hr,hu,by simpa only [Nat.unpair_pair] using congrArg (fun n => (Nat.unpair n).2) he⟩
    · rintro ⟨hr,hu,rfl⟩
      exact ⟨⟨hr,hu⟩,rfl⟩
  | unit =>
    change Nat.pair r v∈Total.supportIdentity (fiberCarrier R X Y .unit).support (Nat.pair r u) ↔ _
    rw [Total.mem_supportIdentity]
    change (fiber R X Y .unit (Nat.unpair (Nat.pair r u)) ∧
      Nat.pair r v=Nat.pair r u) ↔ _
    rw [Nat.unpair_pair]
    change ((r∈R.obj.support ∧ u=0) ∧ Nat.pair r v=Nat.pair r u) ↔
      r∈R.obj.support ∧ u=0 ∧ v=u
    constructor
    · rintro ⟨⟨hr,hu⟩,he⟩
      exact ⟨hr,hu,by simpa only [Nat.unpair_pair] using congrArg (fun n => (Nat.unpair n).2) he⟩
    · rintro ⟨hr,hu,rfl⟩
      exact ⟨⟨hr,hu⟩,rfl⟩
  | product a b ia ib =>
    change Nat.pair r v∈Total.val (productLift R X' Y' a b
      (productFst R X Y a b ≫ rawAction R X Y X' Y' f g a)
      (productSnd R X Y a b ≫ rawAction R X Y X' Y' f g b)).left.hom (Nat.pair r u) ↔ _
    rw [productLift_graph]
    constructor
    · rintro ⟨wa,hwa,wb,hwb,hout⟩
      obtain ⟨za,hza,hwa⟩ := (Total.mem_val_comp _ _ _ _).mp hwa
      obtain ⟨zb,hzb,hwb⟩ := (Total.mem_val_comp _ _ _ _).mp hwb
      have hza' := (productFst_graph R X Y a b r (Nat.unpair u).1 (Nat.unpair u).2 za).mp
        (by simpa only [Nat.pair_unpair] using hza)
      have hzb' := (productSnd_graph R X Y a b r (Nat.unpair u).1 (Nat.unpair u).2 zb).mp
        (by simpa only [Nat.pair_unpair] using hzb)
      have hae:za=Nat.pair r (Nat.unpair u).1 := hza'.2.2
      have hbe:zb=Nat.pair r (Nat.unpair u).2 := hzb'.2.2
      subst za
      subst zb
      have hpa:(Nat.unpair wa).1=r := by
        simpa only [Nat.unpair_pair] using rawMorphism_parameter R X Y X' Y'
          (rawAction R X Y X' Y' f g a) _ _ hwa
      have hpb:(Nat.unpair wb).1=r := by
        simpa only [Nat.unpair_pair] using rawMorphism_parameter R X Y X' Y'
          (rawAction R X Y X' Y' f g b) _ _ hwb
      have hva : Nat.pair r (Nat.unpair wa).2∈
          Total.val (rawAction R X Y X' Y' f g a).left.hom (Nat.pair r (Nat.unpair u).1) := by
        simpa only [← hpa,Nat.pair_unpair] using hwa
      have hvb : Nat.pair r (Nat.unpair wb).2∈
          Total.val (rawAction R X Y X' Y' f g b).left.hom (Nat.pair r (Nat.unpair u).2) := by
        simpa only [← hpb,Nat.pair_unpair] using hwb
      have hve : v=Nat.pair (Nat.unpair wa).2 (Nat.unpair wb).2 := by
        have hh := congrArg (fun n => (Nat.unpair n).2) hout
        simpa only [productCode,Nat.unpair_pair] using hh.symm
      change ActionGraph R X Y X' Y' f g a r (Nat.unpair u).1 (Nat.unpair v).1 ∧
        ActionGraph R X Y X' Y' f g b r (Nat.unpair u).2 (Nat.unpair v).2
      rw [hve]
      simp only [Nat.unpair_pair]
      exact ⟨(ia _ _).mp hva,(ib _ _).mp hvb⟩
    · rintro ⟨ha,hb⟩
      have hsa := ActionGraph_source R X Y X' Y' f g a ha
      have hsb := ActionGraph_source R X Y X' Y' f g b hb
      have hva := (ia _ _).mpr ha
      have hvb := (ib _ _).mpr hb
      refine ⟨Nat.pair r (Nat.unpair v).1,?_,Nat.pair r (Nat.unpair v).2,?_,?_⟩
      · apply (Total.mem_val_comp _ _ _ _).mpr
        refine ⟨Nat.pair r (Nat.unpair u).1,?_,hva⟩
        simpa only [Nat.pair_unpair] using
          (productFst_graph R X Y a b r (Nat.unpair u).1 (Nat.unpair u).2 _).mpr ⟨hsa,hsb,rfl⟩
      · apply (Total.mem_val_comp _ _ _ _).mpr
        refine ⟨Nat.pair r (Nat.unpair u).2,?_,hvb⟩
        simpa only [Nat.pair_unpair] using
          (productSnd_graph R X Y a b r (Nat.unpair u).1 (Nat.unpair u).2 _).mpr ⟨hsa,hsb,rfl⟩
      · simp only [productCode,Nat.unpair_pair,Nat.pair_unpair]
  | sum a b ia ib =>
    change Nat.pair r v∈Total.val (sumCopair R X Y a b
      (rawAction R X Y X' Y' f g a ≫ sumInl R X' Y' a b)
      (rawAction R X Y X' Y' f g b ≫ sumInr R X' Y' a b)).left.hom (Nat.pair r u) ↔ _
    rw [sumCopair_graph]
    simp only [sumTag,sumChild,Nat.unpair_pair]
    constructor
    · rintro (⟨ht,hw⟩ | ⟨ht,hw⟩)
      · obtain ⟨w,hw,ho⟩ := (Total.mem_val_comp _ _ _ _).mp hw
        have hp:(Nat.unpair w).1=r := by
          simpa only [Nat.unpair_pair] using rawMorphism_parameter R X Y X' Y'
            (rawAction R X Y X' Y' f g a) _ _ hw
        have hw' : Nat.pair r (Nat.unpair w).2∈
            Total.val (rawAction R X Y X' Y' f g a).left.hom (Nat.pair r (Nat.unpair u).1) := by
          simpa only [← hp,Nat.pair_unpair] using hw
        have ho' := (sumInl_graph R X' Y' a b r (Nat.unpair w).2 (Nat.pair r v)).mp
          (by simpa only [← hp,Nat.pair_unpair] using ho)
        have hv : v=Nat.pair (Nat.unpair w).2 0 := by
          simpa only [Nat.unpair_pair] using congrArg (fun n => (Nat.unpair n).2) ho'.2
        exact Or.inl ⟨ht,by simp only [hv,Nat.unpair_pair],by
          simpa only [hv,Nat.unpair_pair] using (ia _ _).mp hw'⟩
      · obtain ⟨w,hw,ho⟩ := (Total.mem_val_comp _ _ _ _).mp hw
        have hp:(Nat.unpair w).1=r := by
          simpa only [Nat.unpair_pair] using rawMorphism_parameter R X Y X' Y'
            (rawAction R X Y X' Y' f g b) _ _ hw
        have hw' : Nat.pair r (Nat.unpair w).2∈
            Total.val (rawAction R X Y X' Y' f g b).left.hom (Nat.pair r (Nat.unpair u).1) := by
          simpa only [← hp,Nat.pair_unpair] using hw
        have ho' := (sumInr_graph R X' Y' a b r (Nat.unpair w).2 (Nat.pair r v)).mp
          (by simpa only [← hp,Nat.pair_unpair] using ho)
        have hv : v=Nat.pair (Nat.unpair w).2 1 := by
          simpa only [Nat.unpair_pair] using congrArg (fun n => (Nat.unpair n).2) ho'.2
        exact Or.inr ⟨ht,by simp only [hv,Nat.unpair_pair],by
          simpa only [hv,Nat.unpair_pair] using (ib _ _).mp hw'⟩
    · rintro (⟨ht,hv,h⟩ | ⟨ht,hv,h⟩)
      · have hm := (ia _ _).mpr h
        have hs := ActionGraph_target R X Y X' Y' f g a h
        refine Or.inl ⟨ht,(Total.mem_val_comp _ _ _ _).mpr ⟨Nat.pair r (Nat.unpair v).1,hm,?_⟩⟩
        apply (sumInl_graph R X' Y' a b r (Nat.unpair v).1 (Nat.pair r v)).mpr
        refine ⟨hs,?_⟩
        rw [← hv,Nat.pair_unpair]
      · have hm := (ib _ _).mpr h
        have hs := ActionGraph_target R X Y X' Y' f g b h
        refine Or.inr ⟨ht,(Total.mem_val_comp _ _ _ _).mpr ⟨Nat.pair r (Nat.unpair v).1,hm,?_⟩⟩
        apply (sumInr_graph R X' Y' a b r (Nat.unpair v).1 (Nat.pair r v)).mpr
        refine ⟨hs,?_⟩
        rw [← hv,Nat.pair_unpair]

theorem rawAction_graph (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) (r u s v:ℕ) :
    Nat.pair s v∈Total.val (rawAction R X Y X' Y' f g p).left.hom (Nat.pair r u) ↔
      s=r ∧ ActionGraph R X Y X' Y' f g p r u v := by
  constructor
  · intro h
    have hs:s=r := by
      simpa only [Nat.unpair_pair] using rawMorphism_parameter R X Y X' Y'
        (rawAction R X Y X' Y' f g p) _ _ h
    refine ⟨hs,?_⟩
    subst s
    exact (rawAction_graph_same_parameter R X Y X' Y' f g p r u v).mp h
  · rintro ⟨hs,h⟩
    subst s
    exact (rawAction_graph_same_parameter R X Y X' Y' f g p r u v).mpr h

/-- This is the actual chosen polynomial action conjugated by the proved
chart isomorphisms, not a newly supplied relation or comparison field. -/
theorem transportedAction_graph (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) (r u s v:ℕ) :
    Nat.pair s v∈Total.val (((comparison R X Y p).hom ≫
      (p.withParameters R).eval.map (f,g) ≫ (comparison R X' Y' p).inv).left.hom) (Nat.pair r u) ↔
      s=r ∧ ActionGraph R X Y X' Y' f g p r u v := by
  rw [← rawAction_eq_transported]
  exact rawAction_graph R X Y X' Y' f g p r u s v

theorem transportedAction_graph_all (f:X⟶X') (g:Y⟶Y') (p:SyntaxPolynomial (Total.TotalCategory P)) (n m:ℕ) :
    m∈Total.val (((comparison R X Y p).hom ≫ (p.withParameters R).eval.map (f,g) ≫
      (comparison R X' Y' p).inv).left.hom) n ↔
      (Nat.unpair m).1=(Nat.unpair n).1 ∧
        ActionGraph R X Y X' Y' f g p (Nat.unpair n).1 (Nat.unpair n).2 (Nat.unpair m).2 := by
  simpa only [Nat.pair_unpair] using transportedAction_graph R X Y X' Y' f g p
    (Nat.unpair n).1 (Nat.unpair n).2 (Nat.unpair m).1 (Nat.unpair m).2

theorem transportedAction_unit_graph (f:X⟶X') (g:Y⟶Y') (r u s v:ℕ) :
    Nat.pair s v∈Total.val (((comparison R X Y .unit).hom ≫
      ((SyntaxPolynomial.unit:SyntaxPolynomial (Total.TotalCategory P)).withParameters R).eval.map (f,g) ≫
      (comparison R X' Y' .unit).inv).left.hom) (Nat.pair r u) ↔
      s=r ∧ r∈R.obj.support ∧ u=0 ∧ v=u :=
  transportedAction_graph R X Y X' Y' f g .unit r u s v

/-- The term input to f is its actual family code. In a constant word
family that code is pair(r,word), not the bare word. -/
theorem transportedAction_coefficient_term_graph (f:X⟶X') (g:Y⟶Y')
    (C:Total.TotalCategory P) (r label word s label' value:ℕ) :
    Nat.pair s (Nat.pair label' value)∈Total.val (((comparison R X Y (.product (.coefficient C) .term)).hom ≫
      ((SyntaxPolynomial.product (.coefficient C) .term).withParameters R).eval.map (f,g) ≫
      (comparison R X' Y' (.product (.coefficient C) .term)).inv).left.hom)
      (Nat.pair r (Nat.pair label word)) ↔
      s=r ∧ (r∈R.obj.support ∧ label∈C.obj.support ∧ label'=label) ∧
        r∈Total.val X.hom.hom word ∧ value∈Total.val f.left.hom word := by
  simpa only [ActionGraph,Nat.unpair_pair] using transportedAction_graph R X Y X' Y' f g
    (.product (.coefficient C) .term) r (Nat.pair label word) s (Nat.pair label' value)

theorem transportedAction_coefficient_formula_graph (f:X⟶X') (g:Y⟶Y')
    (C:Total.TotalCategory P) (r label word s label' value:ℕ) :
    Nat.pair s (Nat.pair label' value)∈Total.val (((comparison R X Y (.product (.coefficient C) .formula)).hom ≫
      ((SyntaxPolynomial.product (.coefficient C) .formula).withParameters R).eval.map (f,g) ≫
      (comparison R X' Y' (.product (.coefficient C) .formula)).inv).left.hom)
      (Nat.pair r (Nat.pair label word)) ↔
      s=r ∧ (r∈R.obj.support ∧ label∈C.obj.support ∧ label'=label) ∧
        r∈Total.val Y.hom.hom word ∧ value∈Total.val g.left.hom word := by
  simpa only [ActionGraph,Nat.unpair_pair] using transportedAction_graph R X Y X' Y' f g
    (.product (.coefficient C) .formula) r (Nat.pair label word) s (Nat.pair label' value)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
