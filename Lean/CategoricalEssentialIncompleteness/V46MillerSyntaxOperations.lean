/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxRaw

/-! # Positive graphs of actual operations on arbitrary parameter families

The operation is a supplied morphism from the constructed raw polynomial
fiber. Its uniform index, totality, and parameter equation follow from
that morphism. Neither its values nor the parameter projection need an
ordinary recursive extension.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
variable {P : Uniform.Family} {R : Total.TotalCategory P} {X Y Z : Over R}
variable {p : SyntaxPolynomial (Total.TotalCategory P)}

def operation (h : object R X Y p ⟶ Z) (a : ℕ × ℕ) : Part ℕ :=
  Total.val h.left.hom (Nat.pair a.1 a.2)

theorem operation_represented (h : object R X Y p ⟶ Z) :
    Uniform.Represented P (.product .nat .nat) .nat (operation h) := by
  have hc : Computable (fun a : ℕ × ℕ => Nat.pair a.1 a.2) :=
    Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd
  have hk : Uniform.Represented P (.product .nat .nat) .nat
      (fun a : ℕ × ℕ => Part.some (Nat.pair a.1 a.2)) :=
    Uniform.Represented.of_partrec hc.partrec
  apply (Uniform.Represented.comp hk (Total.val_represented h.left.hom)).of_eq
  intro a
  change (Part.some (Nat.pair a.1 a.2)).bind (Total.val h.left.hom) = _
  rw [Part.bind_some]
  rfl

theorem operation_enumerable (h : object R X Y p ⟶ Z) :
    Uniform.Enumerable P (fun a : (ℕ × ℕ) × ℕ => a.2 ∈ operation h a.1) :=
  (Uniform.represented_iff_graph_enumerable P (.product .nat .nat) .nat _).mp
    (operation_represented h)

theorem operation_exists (h : object R X Y p ⟶ Z) {r u : ℕ}
    (hu : fiber R X Y p (r,u)) : ∃ v,v ∈ operation h (r,u) := by
  exact Part.dom_iff_mem.mp ((Total.total_iff h.left.hom).mp h.left.property
    (Nat.pair r u) ((mem_fiberCarrier R X Y p r u).mpr hu))

theorem operation_functional (h : object R X Y p ⟶ Z) {r u v w : ℕ}
    (hv : v ∈ operation h (r,u)) (hw : w ∈ operation h (r,u)) : v=w :=
  Part.mem_unique hv hw

theorem operation_source (h : object R X Y p ⟶ Z) {r u v : ℕ}
    (hv : v ∈ operation h (r,u)) : fiber R X Y p (r,u) := by
  exact (mem_fiberCarrier R X Y p r u).mp (Total.val_source h.left.hom _ _ hv)

theorem operation_target (h : object R X Y p ⟶ Z) {r u v : ℕ}
    (hv : v ∈ operation h (r,u)) : v ∈ Z.left.obj.support :=
  Total.val_target h.left.hom _ _ hv

theorem operation_parameter (h : object R X Y p ⟶ Z) {r u v : ℕ}
    (hv : v ∈ operation h (r,u)) : r ∈ Total.val Z.hom.hom v := by
  obtain ⟨s,hs⟩ := Part.dom_iff_mem.mp
    ((Total.total_iff Z.hom.hom).mp Z.hom.property v (operation_target h hv))
  have hc : s ∈ Total.val (h.left.hom ≫ Z.hom.hom) (Nat.pair r u) :=
    (Total.mem_val_comp _ _ _ _).mpr ⟨v,hv,hs⟩
  have he : h.left.hom ≫ Z.hom.hom = (projection R X Y p).hom :=
    congrArg (fun k => k.hom) h.w
  rw [he] at hc
  have hsr : s=r := by
    simpa only [Nat.unpair_pair] using ((projection_graph R X Y p (Nat.pair r u) s).mp hc).2
  exact hsr ▸ hs

theorem operation_support (h : object R X Y p ⟶ Z) {r u v : ℕ}
    (hv : v ∈ operation h (r,u)) :
    fiber R X Y p (r,u) ∧ r ∈ Total.val Z.hom.hom v :=
  ⟨operation_source h hv,operation_parameter h hv⟩

theorem operation_existsUnique (h : object R X Y p ⟶ Z) {r u : ℕ}
    (hu : fiber R X Y p (r,u)) : ∃! v,v ∈ operation h (r,u) := by
  obtain ⟨v,hv⟩ := operation_exists h hu
  exact ⟨v,hv,fun w hw => operation_functional h hw hv⟩

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Raw
