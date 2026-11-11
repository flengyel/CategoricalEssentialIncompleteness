/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # The actual ordered raw polynomial product in every parameter slice

An input carries the external parameter once and the two ordered children
separately. The lift uses the graphs of arbitrary supplied slice morphisms.
Their common parameter follows from their Over equations, rather than from
any equality condition on the child values themselves.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw

variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)
variable (a b : SyntaxPolynomial (Total.TotalCategory P))

/-- Combining two parameter-tagged child words retains their order. -/
def productCode (u v : ℕ) : ℕ :=
  Nat.pair (Nat.unpair u).1 (Nat.pair (Nat.unpair u).2 (Nat.unpair v).2)

theorem productCode_computable : Computable₂ productCode :=
  Primrec₂.natPair.to_comp.comp
    (Computable.fst.comp (Computable.unpair.comp Computable.fst))
    (Primrec₂.natPair.to_comp.comp
      (Computable.snd.comp (Computable.unpair.comp Computable.fst))
      (Computable.snd.comp (Computable.unpair.comp Computable.snd)))

/-- Every supplied slice morphism preserves its stored external parameter. -/
theorem output_parameter {Z : Over R} {p : SyntaxPolynomial (Total.TotalCategory P)}
    (f : Z ⟶ object R X Y p) (x u : ℕ)
    (hu : u ∈ Total.val f.left.hom x) :
    (Nat.unpair u).1 ∈ Total.val Z.hom.hom x := by
  have hs : fiber R X Y p (Nat.unpair u) := Total.val_target f.left.hom x u hu
  have hp : (Nat.unpair u).1 ∈ Total.val (projection R X Y p).hom u :=
    (projection_graph R X Y p u _).mpr ⟨hs,rfl⟩
  have hm : (Nat.unpair u).1 ∈
      Total.val (f.left ≫ (object R X Y p).hom).hom x :=
    (Total.mem_val_comp f.left.hom (projection R X Y p).hom x _).mpr ⟨u,hu,hp⟩
  rwa [Over.w f] at hm

theorem outputs_same_parameter {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) (x u v : ℕ)
    (hu : u ∈ Total.val f.left.hom x) (hv : v ∈ Total.val g.left.hom x) :
    (Nat.unpair u).1 = (Nat.unpair v).1 :=
  Part.mem_unique (output_parameter R X Y f x u hu) (output_parameter R X Y g x v hv)

theorem productCode_supported (u v : ℕ)
    (hu : fiber R X Y a (Nat.unpair u)) (hv : fiber R X Y b (Nat.unpair v))
    (he : (Nat.unpair u).1=(Nat.unpair v).1) :
    productCode u v ∈ (fiberCarrier R X Y (.product a b)).support := by
  change fiber R X Y (.product a b) (Nat.unpair (productCode u v))
  simp only [productCode,Nat.unpair_pair,fiber]
  exact ⟨hu,he.symm ▸ hv⟩

theorem productFst_at_code (u v : ℕ)
    (hu : fiber R X Y a (Nat.unpair u)) (hv : fiber R X Y b (Nat.unpair v))
    (he : (Nat.unpair u).1=(Nat.unpair v).1) :
    Total.val (productFst R X Y a b).left.hom (productCode u v)=Part.some u := by
  apply Part.eq_some_iff.mpr
  apply (productFst_graph R X Y a b (Nat.unpair u).1 (Nat.unpair u).2 (Nat.unpair v).2 u).mpr
  exact ⟨hu,he.symm ▸ hv,(Nat.pair_unpair u).symm⟩

theorem productSnd_at_code (u v : ℕ)
    (hu : fiber R X Y a (Nat.unpair u)) (hv : fiber R X Y b (Nat.unpair v))
    (he : (Nat.unpair u).1=(Nat.unpair v).1) :
    Total.val (productSnd R X Y a b).left.hom (productCode u v)=Part.some v := by
  apply Part.eq_some_iff.mpr
  apply (productSnd_graph R X Y a b (Nat.unpair u).1 (Nat.unpair u).2 (Nat.unpair v).2 v).mpr
  refine ⟨hu,he.symm ▸ hv,?_⟩
  rw [he]
  exact (Nat.pair_unpair v).symm

def productLiftValue {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) (x : ℕ) : Part ℕ :=
  (Total.val f.left.hom x).bind (fun u => (Total.val g.left.hom x).map (productCode u))

theorem productLiftValue_graph {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) (x m : ℕ) :
    m ∈ productLiftValue R X Y a b f g x ↔
      ∃ u,u ∈ Total.val f.left.hom x ∧
        ∃ v,v ∈ Total.val g.left.hom x ∧ productCode u v=m := by
  simp only [productLiftValue,Part.mem_bind_iff,Part.mem_map_iff]

theorem productLiftValue_represented {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    Uniform.Represented P .nat .nat (productLiftValue R X Y a b f g) := by
  have hp := Uniform.Represented.pair (Total.val_represented f.left.hom)
    (Total.val_represented g.left.hom)
  have hc : Uniform.Represented P (.product .nat .nat) .nat
      (fun t : ℕ × ℕ => Part.some (productCode t.1 t.2)) :=
    Uniform.Represented.of_partrec productCode_computable.partrec
  apply (Uniform.Represented.comp hp hc).of_eq
  intro x
  simp only [productLiftValue,Part.bind_assoc,Part.bind_map,Part.bind_some_eq_map]
  rfl

def productLiftTotal {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    Z.left ⟶ (object R X Y (.product a b)).left := by
  let k : Z.left.obj ⟶ (fiberCarrier R X Y (.product a b)) :=
    Total.arrow (productLiftValue R X Y a b f g)
      (productLiftValue_represented R X Y a b f g)
      (by
        intro x m hm
        obtain ⟨u,hu,v,_,_⟩ := (productLiftValue_graph R X Y a b f g x m).mp hm
        exact Total.val_source f.left.hom x u hu)
      (by
        intro x m hm
        obtain ⟨u,hu,v,hv,rfl⟩ := (productLiftValue_graph R X Y a b f g x m).mp hm
        exact productCode_supported R X Y a b u v
          (Total.val_target f.left.hom x u hu) (Total.val_target g.left.hom x v hv)
          (outputs_same_parameter R X Y a b f g x u v hu hv))
  refine ⟨k,(Total.total_iff k).mpr ?_⟩
  intro x hx
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.left.hom).mp f.left.property x hx)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff g.left.hom).mp g.left.property x hx)
  exact Part.dom_iff_mem.mpr ⟨productCode u v,
    (productLiftValue_graph R X Y a b f g x _).mpr ⟨u,hu,v,hv,rfl⟩⟩

@[simp] theorem productLiftTotal_value {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    Total.val (productLiftTotal R X Y a b f g).hom=productLiftValue R X Y a b f g := rfl

def productLift {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    Z ⟶ object R X Y (.product a b) :=
  Over.homMk (productLiftTotal R X Y a b f g) (by
    apply WideSubcategory.hom_ext
    apply Total.val_ext_on_source
    intro x hx
    obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.left.hom).mp f.left.property x hx)
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff g.left.hom).mp g.left.property x hx)
    have he := outputs_same_parameter R X Y a b f g x u v hu hv
    have hs := productCode_supported R X Y a b u v
      (Total.val_target f.left.hom x u hu) (Total.val_target g.left.hom x v hv) he
    have hk : Total.val (productLiftTotal R X Y a b f g).hom x=Part.some (productCode u v) :=
      Part.eq_some_iff.mpr ((productLiftValue_graph R X Y a b f g x _).mpr ⟨u,hu,v,hv,rfl⟩)
    have hp : Total.val (projection R X Y (.product a b)).hom (productCode u v)=
        Part.some (Nat.unpair u).1 :=
      Part.eq_some_iff.mpr ((projection_graph R X Y (.product a b) (productCode u v) _).mpr
        ⟨hs,by simp only [productCode,Nat.unpair_pair]⟩)
    have hz : Total.val Z.hom.hom x=Part.some (Nat.unpair u).1 :=
      Part.eq_some_iff.mpr (output_parameter R X Y f x u hu)
    change Total.val ((productLiftTotal R X Y a b f g).hom ≫
      (projection R X Y (.product a b)).hom) x=Total.val Z.hom.hom x
    rw [Total.val_comp,hk,Part.bind_some,hp,hz])

theorem productLift_graph {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) (x m : ℕ) :
    m ∈ Total.val (productLift R X Y a b f g).left.hom x ↔
      ∃ u,u ∈ Total.val f.left.hom x ∧
        ∃ v,v ∈ Total.val g.left.hom x ∧ productCode u v=m :=
  productLiftValue_graph R X Y a b f g x m

@[simp, reassoc] theorem productLift_fst {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    productLift R X Y a b f g ≫ productFst R X Y a b=f := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.left.hom).mp f.left.property x hx)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff g.left.hom).mp g.left.property x hx)
  have he := outputs_same_parameter R X Y a b f g x u v hu hv
  have hk : Total.val (productLift R X Y a b f g).left.hom x=Part.some (productCode u v) :=
    Part.eq_some_iff.mpr ((productLiftValue_graph R X Y a b f g x _).mpr ⟨u,hu,v,hv,rfl⟩)
  change Total.val ((productLift R X Y a b f g).left.hom ≫
    (productFst R X Y a b).left.hom) x=Total.val f.left.hom x
  rw [Total.val_comp,hk,Part.bind_some]
  exact (productFst_at_code R X Y a b u v
    (Total.val_target f.left.hom x u hu) (Total.val_target g.left.hom x v hv) he).trans
    (Part.eq_some_iff.mpr hu).symm

@[simp, reassoc] theorem productLift_snd {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b) :
    productLift R X Y a b f g ≫ productSnd R X Y a b=g := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨u,hu⟩ := Part.dom_iff_mem.mp ((Total.total_iff f.left.hom).mp f.left.property x hx)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((Total.total_iff g.left.hom).mp g.left.property x hx)
  have he := outputs_same_parameter R X Y a b f g x u v hu hv
  have hk : Total.val (productLift R X Y a b f g).left.hom x=Part.some (productCode u v) :=
    Part.eq_some_iff.mpr ((productLiftValue_graph R X Y a b f g x _).mpr ⟨u,hu,v,hv,rfl⟩)
  change Total.val ((productLift R X Y a b f g).left.hom ≫
    (productSnd R X Y a b).left.hom) x=Total.val g.left.hom x
  rw [Total.val_comp,hk,Part.bind_some]
  exact (productSnd_at_code R X Y a b u v
    (Total.val_target f.left.hom x u hu) (Total.val_target g.left.hom x v hv) he).trans
    (Part.eq_some_iff.mpr hv).symm

theorem productLift_unique {Z : Over R}
    (f : Z ⟶ object R X Y a) (g : Z ⟶ object R X Y b)
    (m : Z ⟶ object R X Y (.product a b))
    (hm₁ : m ≫ productFst R X Y a b=f) (hm₂ : m ≫ productSnd R X Y a b=g) :
    m=productLift R X Y a b f g := by
  apply Over.OverMorphism.ext
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro x hx
  obtain ⟨q,hq⟩ := Part.dom_iff_mem.mp ((Total.total_iff m.left.hom).mp m.left.property x hx)
  have hqfiber : fiber R X Y (.product a b) (Nat.unpair q) :=
    Total.val_target m.left.hom x q hq
  let r := (Nat.unpair q).1
  let u := (Nat.unpair (Nat.unpair q).2).1
  let v := (Nat.unpair (Nat.unpair q).2).2
  have hqcode : q=Nat.pair r (Nat.pair u v) := by
    dsimp only [r,u,v]
    rw [Nat.pair_unpair,Nat.pair_unpair]
  have hu : Nat.pair r u ∈ Total.val f.left.hom x := by
    have hp : Nat.pair r u ∈ Total.val (productFst R X Y a b).left.hom q := by
      rw [hqcode]
      exact (productFst_graph R X Y a b r u v _).mpr ⟨hqfiber.1,hqfiber.2,rfl⟩
    have hm : Nat.pair r u ∈ Total.val (m ≫ productFst R X Y a b).left.hom x :=
      (Total.mem_val_comp m.left.hom (productFst R X Y a b).left.hom x _).mpr
        ⟨q,hq,hp⟩
    rwa [hm₁] at hm
  have hv : Nat.pair r v ∈ Total.val g.left.hom x := by
    have hp : Nat.pair r v ∈ Total.val (productSnd R X Y a b).left.hom q := by
      rw [hqcode]
      exact (productSnd_graph R X Y a b r u v _).mpr ⟨hqfiber.1,hqfiber.2,rfl⟩
    have hm : Nat.pair r v ∈ Total.val (m ≫ productSnd R X Y a b).left.hom x :=
      (Total.mem_val_comp m.left.hom (productSnd R X Y a b).left.hom x _).mpr
        ⟨q,hq,hp⟩
    rwa [hm₂] at hm
  have hk : q ∈ Total.val (productLift R X Y a b f g).left.hom x :=
    (productLiftValue_graph R X Y a b f g x q).mpr
      ⟨Nat.pair r u,hu,Nat.pair r v,hv,by simp only [productCode,Nat.unpair_pair,← hqcode]⟩
  exact (Part.eq_some_iff.mpr hq).trans (Part.eq_some_iff.mpr hk).symm

def productIsLimit : IsLimit (BinaryFan.mk (productFst R X Y a b) (productSnd R X Y a b)) :=
  BinaryFan.isLimitMk (fun s => productLift R X Y a b s.fst s.snd)
    (fun s => productLift_fst R X Y a b s.fst s.snd)
    (fun s => productLift_snd R X Y a b s.fst s.snd)
    (fun s m hm₁ hm₂ => productLift_unique R X Y a b s.fst s.snd m hm₁ hm₂)

/-- The raw constructor input is compared with the chosen slice product
by its proved universal property, with both actual projection triangles. -/
def productIso : object R X Y (.product a b) ≅ object R X Y a ⨯ object R X Y b :=
  (productIsLimit R X Y a b).conePointUniqueUpToIso (limit.isLimit (Limits.pair (object R X Y a) (object R X Y b)))

@[simp, reassoc] theorem productIso_fst :
    (productIso R X Y a b).hom ≫ prod.fst=productFst R X Y a b :=
  IsLimit.conePointUniqueUpToIso_hom_comp (productIsLimit R X Y a b) (limit.isLimit (Limits.pair (object R X Y a) (object R X Y b))) ⟨.left⟩

@[simp, reassoc] theorem productIso_snd :
    (productIso R X Y a b).hom ≫ prod.snd=productSnd R X Y a b :=
  IsLimit.conePointUniqueUpToIso_hom_comp (productIsLimit R X Y a b) (limit.isLimit (Limits.pair (object R X Y a) (object R X Y b))) ⟨.right⟩

@[simp, reassoc] theorem productIso_inv_fst :
    (productIso R X Y a b).inv ≫ productFst R X Y a b=prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp (productIsLimit R X Y a b) (limit.isLimit (Limits.pair (object R X Y a) (object R X Y b))) ⟨.left⟩

@[simp, reassoc] theorem productIso_inv_snd :
    (productIso R X Y a b).inv ≫ productSnd R X Y a b=prod.snd :=
  IsLimit.conePointUniqueUpToIso_inv_comp (productIsLimit R X Y a b) (limit.isLimit (Limits.pair (object R X Y a) (object R X Y b))) ⟨.right⟩

theorem productIso_hom : (productIso R X Y a b).hom =
    prod.lift (productFst R X Y a b) (productSnd R X Y a b) := by
  apply prod.hom_ext <;> simp only [productIso_fst,productIso_snd,prod.lift_fst,prod.lift_snd]

theorem productIso_inv : (productIso R X Y a b).inv =
    productLift R X Y a b prod.fst prod.snd :=
  productLift_unique R X Y a b prod.fst prod.snd (productIso R X Y a b).inv
    (productIso_inv_fst R X Y a b) (productIso_inv_snd R X Y a b)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
