/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import RiceShapiro

/-!
# Rice--Shapiro public API regression tests

Signature guards for the four public results. No mathematical content: each
`example` states the theorem's own conclusion from the theorem's own
hypotheses and discharges it by applying the theorem positionally, so the guard
fails to elaborate if an argument is added, removed, reordered, or moved
between explicit and implicit, or if the conclusion changes.

The `#check` lines print the full elaborated signatures into the build log,
where a diff of the log shows what moved. They are a record, not a test: a
`#check` succeeds whatever the signature has become, which is why each is
paired with an `example`.

`autoImplicit` is off, since `lake env lean` does not apply the package's
`leanOptions` and a mistyped name would otherwise be auto-bound and the guard
would pass vacuously.

Run by `scripts/syncpcats.sh`; outside `lake build`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open PCategoryStruct

#check @ApproximationDatum.existsExtensionWitness
#check @ApproximationDatum.pointwiseRiceShapiro
#check @ApproximationDatum.categoricalRiceShapiroRepresentation
#check @existsDecision_of_locallyConnected

/-! ### `ApproximationDatum.existsExtensionWitness` -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
    {X Y : C} {𝒜 : ApproximationDatum X Y} {s : DomSemilattice 𝒜.I}
    (D : 𝒜.WitnessSelection s)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    {Z : C} (i : Z ⟶ 𝒜.I) (hi : rst i = 𝟙 Z) (hsi : i ≫ s.hom = i)
    (hdenseZ : ∀ d : DomSemilattice Z, d.IsDense → d.hom = 𝟙 Z) :
    ∃ a : Z ⟶ 𝒜.A, rst a = 𝟙 Z ∧ a ≫ entry s q = a ∧ 𝒜.Extends a i :=
  ApproximationDatum.existsExtensionWitness D hImported hTuring q hq hs i hi hsi
    hdenseZ

/-! ### `ApproximationDatum.pointwiseRiceShapiro` -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
    [HasRanges C] [CoprodStruct C] [HasCoproducts C]
    {X Y : C} {𝒜 : ApproximationDatum X Y} {s : DomSemilattice 𝒜.I}
    (D : 𝒜.WitnessSelection s) (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hs : 𝒜.ExtensionalUnderRestriction s)
    {Z : C} (i : Z ⟶ 𝒜.I) (hi : rst i = 𝟙 Z)
    (hdenseZX : ∀ d : DomSemilattice (nearProd Z X),
      d.IsDense → d.hom = 𝟙 (nearProd Z X))
    (hdenseZ : ∀ d : DomSemilattice Z, d.IsDense → d.hom = 𝟙 Z) :
    i ≫ s.hom = i ↔
      ∃ a : Z ⟶ 𝒜.A, rst a = 𝟙 Z ∧ a ≫ entry s q = a ∧ 𝒜.Extends a i :=
  ApproximationDatum.pointwiseRiceShapiro D cd hImported hTuring q hq hs i hi
    hdenseZX hdenseZ

/-! ### `ApproximationDatum.categoricalRiceShapiroRepresentation` -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] [CoprodStruct C] [HasCoproducts C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
    {X Y : C} (𝒜 : ApproximationDatum X Y) (s : DomSemilattice 𝒜.I)
    (D : 𝒜.WitnessSelection s) (cd : 𝒜.CaseData)
    (hImported : HasImportedParameterizedRecursion 𝒜.ev)
    (hTuring : RecursionCategory.IsTuringMorphism 𝒜.ev)
    (q : 𝒜.A ⟶ 𝒜.I) (hq : 𝒜.IsUniformIndex q)
    (hext : Extensional 𝒜.ev s)
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C)
    (hdense : ∀ {Z : C} (d : DomSemilattice Z), d.IsDense → d.hom = 𝟙 Z)
    (hlift : HasTotalRangeLifting (𝒜.genHom (s.entryDomain q))) :
    s = 𝒜.gen (s.entryDomain q) :=
  ApproximationDatum.categoricalRiceShapiroRepresentation 𝒜 s D cd hImported
    hTuring q hq hext hjoint hdense hlift

/-! ### `existsDecision_of_locallyConnected` -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [HasRanges C] [CoprodStruct C] [HasCoproducts C]
    [Limits.HasZeroMorphisms C] [RecursionCategory.Prodominical C]
    [HasWeakChoice C]
    (hjoint : TotalMorphismsJointlyEpimorphicOnDomains C)
    (hlc : LocallyConnected C)
    (hdense : ∀ {Z : C} (e : DomSemilattice Z), e.IsDense → e.hom = 𝟙 Z)
    {Q : C} {d : DomSemilattice Q} (dc : d.Complemented) :
    Nonempty (DomSemilattice.Decision dc) :=
  existsDecision_of_locallyConnected hjoint hlc hdense dc

end CategoryTheory
