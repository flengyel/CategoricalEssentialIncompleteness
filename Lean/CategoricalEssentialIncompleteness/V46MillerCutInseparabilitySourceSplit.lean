import CategoricalEssentialIncompleteness.V46MillerCutApplications
import CategoricalEssentialIncompleteness.V46SplitCoproducts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual cut pair in the restriction splitting of the source

Every endomorphism of an included object retains its original arrow.
Consequently every complementary restriction-idempotent pair on that
object recovers a complementary pair in the full uniform source category.
This transfers the proved cut inseparability to the printed Split(E_a).
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.SourceSplit
attribute [instance 2000] Uniform.nativeRestriction

abbrev SplitSource (a : Point) := SplitObject (Uniform.PointObject a)

def inclusion (a : Point) : Uniform.PointObject a ⥤ SplitSource a := splittingInclusion

instance (a : Point) : (inclusion a).Faithful where
  map_injective h := congrArg SplitObject.Hom.hom h

instance (a : Point) : (inclusion a).Full where
  map_surjective f := ⟨f.hom,SplitObject.Hom.ext rfl⟩

private theorem comparison_hom (a : Point) (X Y : Uniform.PointObject a) :
    (coproductComparison (inclusion a) X Y).hom=𝟙 (coprod X Y) := by
  apply CategoryTheory.HasCoproducts.hom_ext
  · have h := congrArg SplitObject.Hom.hom
      (i0_copair ((inclusion a).map (i0 X Y)) ((inclusion a).map (i1 X Y)))
    simpa only [coproductComparison,inclusion,splittingInclusion,SplitObject.comp_hom,
      SplitObject.coproductInl_hom,Idem.top_hom,Category.id_comp,Category.comp_id] using h
  · have h := congrArg SplitObject.Hom.hom
      (i1_copair ((inclusion a).map (i0 X Y)) ((inclusion a).map (i1 X Y)))
    simpa only [coproductComparison,inclusion,splittingInclusion,SplitObject.comp_hom,
      SplitObject.coproductInr_hom,Idem.top_hom,Category.id_comp,Category.comp_id] using h

private def comparisonIso (a : Point) (X Y : Uniform.PointObject a) :
    coprod ((inclusion a).obj X) ((inclusion a).obj Y) ≅ (inclusion a).obj (coprod X Y) where
  hom := coproductComparison (inclusion a) X Y
  inv := ⟨𝟙 (coprod X Y),by
    change (𝟙 (coprod X Y)) ≫ 𝟙 (coprod X Y)=𝟙 (coprod X Y)
    exact Category.id_comp _,by
    change (𝟙 (coprod X Y)) ≫ coprod_map (𝟙 X) (𝟙 Y)=𝟙 (coprod X Y)
    rw [coprod_id,Category.id_comp]⟩
  hom_inv_id := SplitObject.Hom.ext (by
    change (coproductComparison (inclusion a) X Y).hom ≫ 𝟙 (coprod X Y)=
      coprod_map (𝟙 X) (𝟙 Y)
    rw [coprod_id]
    exact (congrArg (fun f:coprod X Y⟶coprod X Y => f ≫ 𝟙 (coprod X Y))
      (comparison_hom a X Y)).trans (Category.id_comp _))
  inv_hom_id := SplitObject.Hom.ext (by
    change (𝟙 (coprod X Y)) ≫ (coproductComparison (inclusion a) X Y).hom=
      𝟙 (coprod X Y)
    exact (congrArg (fun f:coprod X Y⟶coprod X Y => (𝟙 (coprod X Y)) ≫ f)
      (comparison_hom a X Y)).trans (Category.id_comp _))

/-- The fully faithful range inclusion of the full all-representation source. -/
def I (a : Point) : RangeFunctor (Uniform.PointObject a) (SplitSource a) where
  toFunctor := inclusion a
  map_restrict _f := SplitObject.Hom.ext rfl
  map_range _f := SplitObject.Hom.ext rfl
  map_zero _X _Y := SplitObject.Hom.ext rfl
  comparison_isIso X Y := (comparisonIso a X Y).isIso_hom

instance (a : Point) : (I a).toFunctor.Faithful := inferInstanceAs ((inclusion a).Faithful)
instance (a : Point) : (I a).toFunctor.Full := inferInstanceAs ((inclusion a).Full)

theorem I_arrow (a : Point) {X Y : Uniform.PointObject a} (f : X ⟶ Y) :
    ((I a).toFunctor.map f).hom=f := rfl

theorem I_value (a : Point) {X Y : Uniform.PointObject a} (f : X ⟶ Y) :
    ((I a).toFunctor.map f).hom.val=f.val := rfl

abbrev N (a : Point) : SplitSource a := (I a).toFunctor.obj (Uniform.N (Uniform.Family.ofPoint a))

theorem N_base (a : Point) : (N a).base=Uniform.N (Uniform.Family.ofPoint a) := rfl

theorem N_domain (a : Point) : (N a).domain=⊤ := rfl

theorem I_nonzero (a : Point) :
    (I a).toFunctor.map (𝟙 (Uniform.N (Uniform.Family.ofPoint a)))≠0 := by
  intro h
  have hh := congrArg (fun f => f.hom.val (0 : ℕ)) h
  change Part.some (0 : ℕ)=Part.none at hh
  have hm := Part.mem_some (0 : ℕ)
  rw [hh] at hm
  exact hm.1

/-- Fullness on the included object recovers every candidate idempotent. -/
def recoverIdem (a : Point) {X : Uniform.PointObject a}
    (c : Idem ((I a).toFunctor.obj X)) : Idem X := SplitObject.baseIdem c

theorem recover_included (a : Point) {X : Uniform.PointObject a} (c : Idem X) :
    recoverIdem a ((I a).mapIdem c)=c := rfl

theorem include_recovered (a : Point) {X : Uniform.PointObject a}
    (c : Idem ((I a).toFunctor.obj X)) : (I a).mapIdem (recoverIdem a c)=c := by
  apply Idem.ext
  apply SplitObject.Hom.ext
  rfl

theorem recover_inf (a : Point) {X : Uniform.PointObject a}
    (c d : Idem ((I a).toFunctor.obj X)) :
    recoverIdem a (c⊓d)=recoverIdem a c⊓recoverIdem a d := rfl

theorem recover_sup (a : Point) {X : Uniform.PointObject a}
    (c d : Idem ((I a).toFunctor.obj X)) :
    recoverIdem a (c⊔d)=recoverIdem a c⊔recoverIdem a d := rfl

theorem recover_bot (a : Point) {X : Uniform.PointObject a} :
    recoverIdem a (⊥ : Idem ((I a).toFunctor.obj X))=⊥ := rfl

theorem recover_top (a : Point) {X : Uniform.PointObject a} :
    recoverIdem a (⊤ : Idem ((I a).toFunctor.obj X))=⊤ := rfl

theorem recover_le_iff (a : Point) {X : Uniform.PointObject a}
    (c d : Idem ((I a).toFunctor.obj X)) :
    c≤d ↔ recoverIdem a c≤recoverIdem a d := SplitObject.le_iff_base c d

theorem recover_complementary (a : Point) {X : Uniform.PointObject a}
    {c d : Idem ((I a).toFunctor.obj X)} (h : Complementary c d) :
    Complementary (recoverIdem a c) (recoverIdem a d) := by
  constructor
  · have he := congrArg (recoverIdem a) h.disjoint
    exact he
  · have he := congrArg (recoverIdem a) h.cover
    exact he

theorem mapIdem_included (a : Point) {X : Uniform.PointObject a} (c : Idem X) :
    (I a).mapIdem c=SplitObject.includedIdem c := by
  apply Idem.ext
  apply SplitObject.Hom.ext
  rfl

/-- Every complementary pair in the splitting is included in this argument;
no syntactic or computability restriction is imposed on the candidate pair. -/
theorem map_inseparable (a : Point) {X : Uniform.PointObject a} {c d : Idem X}
    (h : Inseparable c d) : Inseparable ((I a).mapIdem c) ((I a).mapIdem d) := by
  rw [mapIdem_included,mapIdem_included]
  exact SplitObject.inclusion_inseparable h

def support (a : Point) (c : Idem (N a)) : Set ℕ := Uniform.support (recoverIdem a c)

theorem included_support (a : Point) (c : Idem (Uniform.N (Uniform.Family.ofPoint a))) :
    support a ((I a).mapIdem c)=Uniform.support c := rfl

theorem support_inf (a : Point) (c d : Idem (N a)) :
    support a (c⊓d)=support a c∩support a d := by
  change PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a c⊓recoverIdem a d))=
    PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a c))∩
      PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a d))
  rw [Uniform.toPfnIdem_inf,PartialFunctions.support_inf]

theorem support_sup (a : Point) (c d : Idem (N a)) :
    support a (c⊔d)=support a c∪support a d := by
  change PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a c⊔recoverIdem a d))=
    PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a c))∪
      PartialFunctions.support (Uniform.toPfnIdem (recoverIdem a d))
  rw [Uniform.toPfnIdem_sup,PartialFunctions.support_sup]

theorem support_le_iff (a : Point) (c d : Idem (N a)) :
    c≤d ↔ support a c⊆support a d :=
  (recover_le_iff a c d).trans (Uniform.support_le_iff (recoverIdem a c) (recoverIdem a d))

theorem support_bot (a : Point) : support a (⊥ : Idem (N a))=∅ := by
  change PartialFunctions.support (Uniform.toPfnIdem (⊥ :
    Idem (Uniform.N (Uniform.Family.ofPoint a))))=∅
  rw [Uniform.toPfnIdem_bot,PartialFunctions.support_bot]

theorem support_top (a : Point) : support a (⊤ : Idem (N a))=Set.univ := by
  change PartialFunctions.support (Uniform.toPfnIdem (⊤ :
    Idem (Uniform.N (Uniform.Family.ofPoint a))))=Set.univ
  rw [Uniform.toPfnIdem_top,PartialFunctions.support_top]

def lowerIdem (a : Point) : Idem (N a) := (I a).mapIdem (CutDigits.lowerIdem a)
def upperIdem (a : Point) : Idem (N a) := (I a).mapIdem (CutDigits.upperIdem a)

theorem lowerIdem_support (a : Point) : support a (lowerIdem a)=CutDigits.lowerCut a :=
  CutDigits.lowerIdem_support a

theorem upperIdem_support (a : Point) : support a (upperIdem a)=CutDigits.upperCut a :=
  CutDigits.upperIdem_support a

/-- The actual printed cut pair is inseparable in Split(E_a). -/
theorem printed_cut_inseparability (a : Point) (ha : IsMiller a) :
    Inseparable (lowerIdem a) (upperIdem a) :=
  map_inseparable a (Cut.printed_cut_inseparability a ha)

/-- The underlying parity-diagonal pair also transfers without a Miller hypothesis. -/
theorem source_diagonal_inseparable (a : Point) :
    Inseparable ((I a).mapIdem (CutInseparability.diagonal0 a))
      ((I a).mapIdem (CutInseparability.diagonal1 a)) :=
  map_inseparable a (CutInseparability.source_diagonal_inseparable a)

theorem diagonal0_support (a : Point) (e : ℕ) :
    e∈support a ((I a).mapIdem (CutInseparability.diagonal0 a)) ↔
      ∃ m,m∈Unanimity.tau a e e ∧ m%2=0 := CutInseparability.diagonal0_support a e

theorem diagonal1_support (a : Point) (e : ℕ) :
    e∈support a ((I a).mapIdem (CutInseparability.diagonal1 a)) ↔
      ∃ m,m∈Unanimity.tau a e e ∧ m%2=1 := CutInseparability.diagonal1_support a e

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability.SourceSplit
