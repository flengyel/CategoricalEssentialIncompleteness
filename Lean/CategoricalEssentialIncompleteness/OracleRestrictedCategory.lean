/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.OracleDomainRecursion
import CategoricalEssentialIncompleteness.PartialFunctions

/-! # Formal numerical types and arrows restricted to oracle-c.e. domains -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation

inductive Ty where
  | nat
  | product : Ty → Ty → Ty
  | coproduct : Ty → Ty → Ty

@[implicit_reducible] def Ty.carrier : Ty → Type
  | .nat => ℕ
  | .product X Y => X.carrier × Y.carrier
  | .coproduct X Y => X.carrier ⊕ Y.carrier

@[implicit_reducible] def Ty.primcodable : (X : Ty) → Primcodable X.carrier
  | .nat => inferInstanceAs (Primcodable ℕ)
  | .product X Y => by
    letI := X.primcodable
    letI := Y.primcodable
    exact inferInstanceAs (Primcodable (X.carrier × Y.carrier))
  | .coproduct X Y => by
    letI := X.primcodable
    letI := Y.primcodable
    exact inferInstanceAs (Primcodable (X.carrier ⊕ Y.carrier))

instance (X : Ty) : Primcodable X.carrier := X.primcodable

theorem partrecGraph {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → Part β} (hf : Partrec f) : REPred (fun p : α × β => p.2 ∈ f p.1) := by
  have he : REPred (fun p : (α × β) × β => p.2=p.1.2) :=
    (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).computablePred.to_re
  have hk := ((hf.comp Computable.fst).bind he.to₂).dom_re
  apply hk.of_eq
  intro p
  rw [Part.bind_dom]
  change (∃ h : (f p.1).Dom,∃ _ : (f p.1).get h=p.2,True) ↔ p.2 ∈ f p.1
  constructor
  · rintro ⟨h,he,_⟩
    exact he ▸ Part.get_mem h
  · intro h
    exact ⟨h.1,h.2,trivial⟩

def Extends {α β : Type} (f₀ f : α → Part β) : Prop :=
  ∀ x y,y ∈ f x → y ∈ f₀ x

theorem Extends.mem_iff {α β : Type} {f₀ f : α → Part β} (h : Extends f₀ f) (x : α) (y : β) :
    y ∈ f x ↔ (f x).Dom ∧ y ∈ f₀ x := by
  constructor
  · intro hy
    exact ⟨hy.1,h x y hy⟩
  · rintro ⟨hx,hy⟩
    obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp hx
    have he : z=y := Part.mem_unique (h x z hz) hy
    exact he ▸ hz

theorem composite_domain {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {S : Set ℕ} {f f₀ : α → Part β} {g : β → Part γ}
    (hD : FiniteOracleRE S (fun x => (f x).Dom))
    (hE : FiniteOracleRE S (fun y => (g y).Dom)) (hf : Partrec f₀) (he : Extends f₀ f) :
    FiniteOracleRE S (fun x => ((f x).bind g).Dom) := by
  have h := ((hD.comp Computable.fst).and
    ((FiniteOracleRE.of_re (partrecGraph hf)).and (hE.comp Computable.snd))).projection
  apply h.of_eq
  intro x
  constructor
  · rintro ⟨y,hx,hy,hg⟩
    exact Part.dom_iff_mem.mpr ⟨(g y).get hg,
      Part.mem_bind_iff.mpr ⟨y,(he.mem_iff x y).mpr ⟨hx,hy⟩,Part.get_mem hg⟩⟩
  · intro h
    obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp h
    obtain ⟨y,hy,hg⟩ := Part.mem_bind_iff.mp hz
    exact ⟨y,hy.1,he x y hy,hg.1⟩

/-- The two arrow requirements are independent. The extension is allowed to
have a larger domain; equality of arrows is equality of actual partial graphs. -/
@[ext] structure Arrow (S : Set ℕ) (X Y : Ty) where
  val : X.carrier → Part Y.carrier
  domain : FiniteOracleRE S (fun x => (val x).Dom)
  extension : ∃ f₀ : X.carrier → Part Y.carrier,Partrec f₀ ∧ Extends f₀ val

namespace Arrow

variable {S : Set ℕ}

def identity (X : Ty) : Arrow S X X :=
  ⟨Part.some,FiniteOracleRE.of_re (REPred.const True),
    ⟨Part.some,Partrec.some,fun _ _ h => h⟩⟩

def compose {X Y Z : Ty} (f : Arrow S X Y) (g : Arrow S Y Z) : Arrow S X Z := by
  refine ⟨fun x => (f.val x).bind g.val,?_,?_⟩
  · obtain ⟨f₀,hf,he⟩ := f.extension
    exact composite_domain f.domain g.domain hf he
  · obtain ⟨f₀,hf,he⟩ := f.extension
    obtain ⟨g₀,hg,hge⟩ := g.extension
    refine ⟨fun x => (f₀ x).bind g₀,hf.bind (hg.comp Computable.snd).to₂,?_⟩
    intro x z hz
    obtain ⟨y,hy,hz⟩ := Part.mem_bind_iff.mp hz
    exact Part.mem_bind_iff.mpr ⟨y,he x y hy,hge y z hz⟩

end Arrow

/-- The oracle parameter is part of the category, while its objects retain
their formal product and coproduct expressions. -/
structure Restricted (S : Set ℕ) where
  type : Ty

namespace Restricted

variable (S : Set ℕ)

abbrev carrier (X : Restricted S) := X.type.carrier

instance (X : Restricted S) : Primcodable (carrier S X) := X.type.primcodable

instance : Category (Restricted S) where
  Hom X Y := Arrow S X.type Y.type
  id X := Arrow.identity X.type
  comp := Arrow.compose
  id_comp f := Arrow.ext (funext (fun x => Part.bind_some x f.val))
  comp_id f := Arrow.ext (funext (fun x => Part.bind_some_right (f.val x)))
  assoc f g h := Arrow.ext (funext (fun x => Part.bind_assoc (f.val x) g.val h.val))

def inclusion : Restricted S ⥤ PartialFunctions.Pfn where
  obj X := PartialFun.of (carrier S X)
  map f := f.val
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (inclusion S).Faithful where
  map_injective h := Arrow.ext h

end Restricted
end CategoricalEssentialIncompleteness.LocalConnectedness.OracleComputation
