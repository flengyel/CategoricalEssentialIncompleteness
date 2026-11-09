import CategoricalEssentialIncompleteness.V46MillerNamedProofImageData
import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSyntax
import CategoricalEssentialIncompleteness.V46MillerTotalSubobjectOrder

/-! # The actual ordered-field sentence morphisms

The numerical map is constructed before any external theory. Its value is
the sentence c_n < 1/2 in the fixed integer-coefficient convention. Chosen
sentence points retain their own coordinates throughout the comparison.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceMorphisms
variable (P : Uniform.Family)
local notation "σ" => OrderedFieldSyntax.functionSymbols
local notation "π" => OrderedFieldSyntax.relationSymbols
local notation "d" => OrderedFieldSyntax.bound
local notation "S" => NamedProofImage.syntaxData P σ π d
local notation "S₀" => NamedSyntaxComparison.sourceSyntax NamedPostfixEncoding.variableCarrier σ π d
local notation "F" => Syntax.predicateFunctor P

def numericalObject : Total.TotalCategory P := (F).obj NamedPostfixEncoding.variableCarrier

theorem numerical_support (n : ℕ) : n ∈ (numericalObject P).obj.support := by
  apply (AxiomSubobjects.mapped_support P NamedPostfixEncoding.variableCarrier n).mpr
  simp [NamedPostfixEncoding.variableCarrier]

def numericalPoint (n : ℕ) : Total.underlying.obj (numericalObject P) :=
  ⟨n,numerical_support P n⟩

theorem thetaFormula_supported (n : ℕ) :
    OrderedFieldSyntax.theta n ∈ ((F).obj (S₀).algebra.a.2).obj.support := by
  have hv : (NamedProofImage.sourceFormulaPoint P σ π d
      (OrderedFieldSyntax.thetaSentence n)).val=OrderedFieldSyntax.theta n :=
    SyntacticNamedHilbert.formulaPoint_value σ π d (OrderedFieldSyntax.thetaSentence n)
  exact hv ▸ (NamedProofImage.sourceFormulaPoint P σ π d
    (OrderedFieldSyntax.thetaSentence n)).property

def thetaFormulaMap : numericalObject P ⟶ (F).obj (S₀).algebra.a.2 :=
  ⟨Total.totalFromFunction OrderedFieldSyntax.theta OrderedFieldSyntax.theta_primrec.to_comp
      (fun n _ => thetaFormula_supported P n),Total.totalFromFunction_total _ _ _⟩

theorem thetaFormulaMap_graph (n w : ℕ) :
    w ∈ Total.val (thetaFormulaMap P).hom n ↔ w=OrderedFieldSyntax.theta n := by
  change w ∈ Total.val (Total.totalFromFunction OrderedFieldSyntax.theta
    OrderedFieldSyntax.theta_primrec.to_comp (fun n _ => thetaFormula_supported P n)) n ↔ _
  rw [Total.mem_totalFromFunction]
  exact ⟨fun h => h.2,fun h => ⟨numerical_support P n,h⟩⟩

theorem thetaFormula_image_sentence :
    Total.Subobjects.imageCodes (thetaFormulaMap P) ⊆
      Total.Subobjects.imageCodes (NamedProofImage.sentenceWord P σ π d) := by
  rintro w ⟨n,hn⟩
  have he : w=OrderedFieldSyntax.theta n := (thetaFormulaMap_graph P n w).mp hn
  subst w
  exact ⟨(NamedProofImage.sentencePoint P σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n)).val,
    NamedProofImage.sentencePoint_word P σ π d (OrderedFieldSyntax.thetaSentence n)
      (OrderedFieldSyntax.thetaSentence_closed n)⟩

/-- One total morphism, with no theory, proof or consistency parameter. -/
def theta : numericalObject P ⟶ (S).sentenceObject :=
  Total.Subobjects.factorThroughMono (thetaFormulaMap P)
    (NamedProofImage.sentenceWord P σ π d) (thetaFormula_image_sentence P)

theorem theta_word : theta P ≫ NamedProofImage.sentenceWord P σ π d=thetaFormulaMap P :=
  Total.Subobjects.factorThroughMono_fac _ _ _

theorem theta_graph (n s : ℕ) :
    s ∈ Total.val (theta P).hom n ↔
      OrderedFieldSyntax.theta n ∈ Total.val (NamedProofImage.sentenceWord P σ π d).hom s := by
  change s ∈ Total.val (Total.Subobjects.factorThroughMono (thetaFormulaMap P)
    (NamedProofImage.sentenceWord P σ π d) (thetaFormula_image_sentence P)).hom n ↔ _
  rw [Total.Subobjects.factorThroughMono_graph]
  constructor
  · rintro ⟨w,hw,hs⟩
    exact (thetaFormulaMap_graph P n w).mp hw ▸ hs
  · intro hs
    exact ⟨OrderedFieldSyntax.theta n,(thetaFormulaMap_graph P n _).mpr rfl,hs⟩

theorem theta_point (n : ℕ) :
    Total.underlying.map (theta P) (numericalPoint P n)=
      NamedProofImage.sentencePoint P σ π d (OrderedFieldSyntax.thetaSentence n)
        (OrderedFieldSyntax.thetaSentence_closed n) := by
  apply (Total.totalFunction_eq_iff _ _ _).mpr
  exact (theta_graph P n _).mpr (NamedProofImage.sentencePoint_word P σ π d
    (OrderedFieldSyntax.thetaSentence n) (OrderedFieldSyntax.thetaSentence_closed n))

def negation : (S).sentenceObject ⟶ (S).sentenceObject := (S).sentenceNegation

theorem sentence_point_ext (s t : Total.underlying.obj (S).sentenceObject)
    (h : Total.underlying.map (S).sentenceInclusion s=
      Total.underlying.map (S).sentenceInclusion t) : s=t := by
  apply Subtype.ext
  apply Total.injective_of_partialMono (S).sentenceInclusion.hom
    (PartialSpans.partialMono_of_mono (S).sentenceInclusion) s.val t.val
      (Total.totalFunction (S).sentenceInclusion s).val
  · exact Total.totalFunction_mem (S).sentenceInclusion s
  · exact (Total.totalFunction_eq_iff (S).sentenceInclusion t
      (Total.totalFunction (S).sentenceInclusion s)).mp h.symm

theorem negation_point (φ : OrderedFieldSyntax.Formula) (hc : φ.freeVariables=[]) :
    Total.underlying.map (negation P) (NamedProofImage.sentencePoint P σ π d φ hc)=
      NamedProofImage.sentencePoint P σ π d (.neg φ) hc := by
  apply sentence_point_ext P
  change Total.underlying.map (S).sentenceInclusion
    (Total.underlying.map (S).sentenceNegation _)=_
  rw [← CategoryTheory.Functor.map_comp_apply,CategoricalSyntax.sentenceNegation_inclusion,
    CategoryTheory.Functor.map_comp_apply,NamedProofImage.sentencePoint_inclusion,
    NamedProofImage.formulaPoint_negation,NamedProofImage.sentencePoint_inclusion]

theorem negation_theta_point (n : ℕ) :
    Total.underlying.map (theta P ≫ negation P) (numericalPoint P n)=
      NamedProofImage.sentencePoint P σ π d (.neg (OrderedFieldSyntax.thetaSentence n))
        (OrderedFieldSyntax.thetaSentence_closed n) := by
  rw [CategoryTheory.Functor.map_comp_apply,theta_point,negation_point]

end CategoricalEssentialIncompleteness.V46.Miller.TheorySentenceMorphisms
