/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-! # Recursive-leaf, coefficient and unit slice comparisons

The graph carrier of a supplied family projection is isomorphic to that
family. Bijection reflection uses the already constructed uniform inverse
of an injective graph, not a section of an arbitrary surjection.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} (R : Total.TotalCategory P) (X Y : Over R)

theorem term_supported (n : ℕ)
    (hn : n ∈ (object R X Y .term).left.obj.support) :
    (Nat.unpair n).2 ∈ X.left.obj.support :=
  Total.val_source X.hom.hom (Nat.unpair n).2 (Nat.unpair n).1 hn

def termForward : object R X Y .term ⟶ X := by
  let f : (object R X Y .term).left ⟶ X.left :=
    ⟨Total.totalFromFunction (fun n => (Nat.unpair n).2)
      (Computable.snd.comp Computable.unpair)
      (term_supported R X Y),Total.totalFromFunction_total _ _ _⟩
  refine Over.homMk f ?_
  apply WideSubcategory.hom_ext
  apply Total.val_ext_on_source
  intro n hn
  have hx : (Nat.unpair n).1 ∈ Total.val X.hom.hom (Nat.unpair n).2 := hn
  have hf : Total.val f.hom n=Part.some (Nat.unpair n).2 :=
    Part.eq_some_iff.mpr ((Total.mem_totalFromFunction (fun n => (Nat.unpair n).2)
      (Computable.snd.comp Computable.unpair) (term_supported R X Y) n _).mpr ⟨hn,rfl⟩)
  have hp : Total.val (projection R X Y .term).hom n=Part.some (Nat.unpair n).1 :=
    Part.eq_some_iff.mpr ((projection_graph R X Y .term n _).mpr ⟨hn,rfl⟩)
  change Total.val (f.hom ≫ X.hom.hom) n=Total.val (projection R X Y .term).hom n
  rw [Total.val_comp,hf,Part.bind_some,Part.eq_some_iff.mpr hx,hp]

theorem termForward_graph (n u : ℕ) :
    u ∈ Total.val (termForward R X Y).left.hom n ↔
      n ∈ (object R X Y .term).left.obj.support ∧ u=(Nat.unpair n).2 :=
  Total.mem_totalFromFunction (fun n => (Nat.unpair n).2)
    (Computable.snd.comp Computable.unpair) (term_supported R X Y) n u

theorem termForward_value (x : Total.underlying.obj (object R X Y .term).left) :
    (Total.underlying.map (termForward R X Y).left x).val=(Nat.unpair x.val).2 := by
  exact ((termForward_graph R X Y x.val _).mp
    (Total.totalFunction_mem (termForward R X Y).left x)).2

theorem termForward_bijective : Function.Bijective (Total.underlying.map (termForward R X Y).left) := by
  constructor
  · intro n m he
    have hu : (Nat.unpair n.val).2=(Nat.unpair m.val).2 := by
      simpa only [termForward_value] using congrArg Subtype.val he
    have hn : (Nat.unpair n.val).1 ∈ Total.val X.hom.hom (Nat.unpair n.val).2 := n.property
    have hm : (Nat.unpair m.val).1 ∈ Total.val X.hom.hom (Nat.unpair m.val).2 := m.property
    rw [hu] at hn
    have hr := Part.mem_unique hn hm
    apply Subtype.ext
    calc
      n.val=Nat.pair (Nat.unpair n.val).1 (Nat.unpair n.val).2 := (Nat.pair_unpair n.val).symm
      _=Nat.pair (Nat.unpair m.val).1 (Nat.unpair m.val).2 := by rw [hr,hu]
      _=m.val := Nat.pair_unpair m.val
  · intro u
    obtain ⟨r,hr⟩ := Part.dom_iff_mem.mp
      ((Total.total_iff X.hom.hom).mp X.hom.property u.val u.property)
    let n : Total.underlying.obj (object R X Y .term).left :=
      ⟨Nat.pair r u.val,by
        change fiber R X Y .term (Nat.unpair (Nat.pair r u.val))
        simpa only [fiber,Nat.unpair_pair] using hr⟩
    refine ⟨n,?_⟩
    apply Subtype.ext
    rw [termForward_value]
    simp only [n,Nat.unpair_pair]

/-- The inverse is the uniform inverse constructed by isomorphism reflection. -/
def termIso : object R X Y .term ≅ X := by
  let f := termForward R X Y
  letI : IsIso (Total.underlying.map f.left) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (termForward_bijective R X Y)
  letI : IsIso f.left := isIso_of_reflects_iso f.left Total.underlying
  exact Over.isoMk (asIso f.left) f.w

def formulaIso : object R X Y .formula ≅ Y := termIso R Y X

/-- The ordinary explicit product uses exactly the raw coefficient code. -/
def coefficientExplicitIso (C : Total.TotalCategory P) :
    object R X Y (.coefficient C) ≅ Over.mk (Total.totalFst R C) := by
  let e : (object R X Y (.coefficient C)).left=Total.totalProduct R C := by rfl
  refine Over.isoMk (eqToIso e) ?_
  change (𝟙 (Total.totalProduct R C)) ≫ Total.totalFst R C=projection R X Y (.coefficient C)
  rw [Category.id_comp]
  apply WideSubcategory.hom_ext
  apply Total.val_injective
  funext n
  apply Part.ext
  intro r
  change r ∈ Total.val (Total.partialFst R.obj C.obj) n ↔
    r ∈ Total.val (projection R X Y (.coefficient C)).hom n
  rw [Total.mem_partialFst,projection_graph]
  change ((Nat.unpair n).1 ∈ R.obj.support ∧ (Nat.unpair n).2 ∈ C.obj.support) ∧
      (Nat.unpair n).1=r ↔
    ((Nat.unpair n).1 ∈ R.obj.support ∧ (Nat.unpair n).2 ∈ C.obj.support) ∧ r=(Nat.unpair n).1
  exact ⟨fun ⟨h,e⟩ => ⟨h,e.symm⟩,fun ⟨h,e⟩ => ⟨h,e.symm⟩⟩

def explicitProductIso (C : Total.TotalCategory P) : Total.totalProduct R C ≅ R ⨯ C :=
  (Total.productIsLimit R C).conePointUniqueUpToIso (limit.isLimit (Limits.pair R C))

theorem explicitProductIso_fst (C : Total.TotalCategory P) :
    (explicitProductIso R C).hom ≫ prod.fst=Total.totalFst R C :=
  (Total.productIsLimit R C).conePointUniqueUpToIso_hom_comp
    (limit.isLimit (Limits.pair R C)) ⟨WalkingPair.left⟩

def coefficientIso (C : Total.TotalCategory P) :
    object R X Y (.coefficient C) ≅ constantFamily R C :=
  coefficientExplicitIso R X Y C ≪≫ Over.isoMk (explicitProductIso R C) (explicitProductIso_fst R C)

/-- The identity family is terminal in the parameter slice, including an
empty parameter carrier. -/
def identityFamilyIsTerminal : IsTerminal (Over.mk (𝟙 R)) :=
  IsTerminal.ofUniqueHom (fun Z => Over.homMk Z.hom (by simp)) (by
    intro Z f
    apply Over.OverMorphism.ext
    simpa using f.w)

def unitForward : object R X Y .unit ⟶ Over.mk (𝟙 R) :=
  Over.homMk (projection R X Y .unit) (by
    change projection R X Y .unit ≫ 𝟙 R=projection R X Y .unit
    exact Category.comp_id _)

theorem unitForward_value (n : Total.underlying.obj (object R X Y .unit).left) :
    (Total.underlying.map (unitForward R X Y).left n).val=(Nat.unpair n.val).1 := by
  exact ((projection_graph R X Y .unit n.val _).mp
    (Total.totalFunction_mem (unitForward R X Y).left n)).2

theorem unitForward_bijective : Function.Bijective (Total.underlying.map (unitForward R X Y).left) := by
  constructor
  · intro n m he
    have hr : (Nat.unpair n.val).1=(Nat.unpair m.val).1 := by
      simpa only [unitForward_value] using congrArg Subtype.val he
    have hn : (Nat.unpair n.val).2=0 := n.property.2
    have hm : (Nat.unpair m.val).2=0 := m.property.2
    apply Subtype.ext
    calc
      n.val=Nat.pair (Nat.unpair n.val).1 (Nat.unpair n.val).2 := (Nat.pair_unpair n.val).symm
      _=Nat.pair (Nat.unpair m.val).1 (Nat.unpair m.val).2 := by rw [hr,hn,hm]
      _=m.val := Nat.pair_unpair m.val
  · intro r
    let n : Total.underlying.obj (object R X Y .unit).left :=
      ⟨Nat.pair r.val 0,by
        change fiber R X Y .unit (Nat.unpair (Nat.pair r.val 0))
        rw [Nat.unpair_pair]
        exact ⟨r.property,rfl⟩⟩
    refine ⟨n,?_⟩
    apply Subtype.ext
    rw [unitForward_value]
    simp only [n,Nat.unpair_pair]

def unitIso : object R X Y .unit ≅ ⊤_ (Over R) := by
  let f := unitForward R X Y
  letI : IsIso (Total.underlying.map f.left) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (unitForward_bijective R X Y)
  letI : IsIso f.left := isIso_of_reflects_iso f.left Total.underlying
  exact Over.isoMk (asIso f.left) f.w ≪≫
    (identityFamilyIsTerminal R).uniqueUpToIso terminalIsTerminal

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
