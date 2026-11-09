import CategoricalEssentialIncompleteness.V46MillerNamedProofImageAbsenceReflection

/-! # All actual seven-scheme parameters yield finite native Γ proofs

The target success points prove both native FreeFor conditions and their
literal substitution results. The distribution parameter is reflected
through the actual false classifier and the PA false fiber. No logical
scheme coverage, source axiom admissibility or semantic validity premise
is supplied.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
namespace SchemeReflection
open NamedFiniteSyntax NamedPostfixEncoding
open Points
variable (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ) (Γ : Set ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "U" => Total.underlying (P:=P)
local notation "N" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V" => (variableCarrier : PredicateCategory 𝗣𝗔)
local notation "S₀" => NamedSyntaxComparison.sourceSyntax (V) σ π d
local notation "S" => syntaxData P σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d

theorem instantiation (p : (U).obj (S).instantiationParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertInstantiation p)) := by
  let base := (U).map (S).instantiationInclusion p
  let x := ((U).map prod.fst base).val
  let φ := decodeFormula P σ π d ((U).map prod.fst ((U).map prod.snd base))
  let t := decodeTerm P σ π d ((U).map prod.snd ((U).map prod.snd base))
  let a := (U).map (S).instantiationAdmissible p
  let ψ := decodeFormula P σ π d ((U).map (S).formulaSubstitution a)
  have hb : pairPoint (namePoint P x) (pairPoint (formulaPoint P σ π d φ) (termPoint P σ π d t))=base := by
    simp only [x,φ,t,namePoint_eta,formulaPoint_decode,termPoint_decode,pairPoint_eta]
  have hinput : (U).map (S).instantiationInput base=substitutionPoint P σ π d x φ t := by
    rw [← hb,instantiationInput_point]
  have hi : (U).map (S).admissibleInclusion a=substitutionPoint P σ π d x φ t := by
    have hc := congrArg (fun f => (U).map f p) (S).instantiation_admissible
    simp only [CategoryTheory.Functor.map_comp_apply] at hc
    exact hc.symm.trans hinput
  have hr : (U).map (S).formulaSubstitution a=formulaPoint P σ π d ψ :=
    (formulaPoint_decode P σ π d ((U).map (S).formulaSubstitution a)).symm
  obtain ⟨hff,hsub⟩ := substitution_reflects_native P σ π d a x φ t ψ hi hr
  have hv : (U).map (S).hilbertInstantiation p=formulaPoint P σ π d (.imp (.all x φ) ψ) := by
    dsimp only [CategoricalSyntax.hilbertInstantiation]
    apply implication_at P σ π d
    · apply quantifier_at P σ π d
      · rw [CategoryTheory.Functor.map_comp_apply]
        exact (namePoint_eta P ((U).map prod.fst base)).symm
      · rw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply]
        exact (formulaPoint_decode P σ π d ((U).map prod.fst ((U).map prod.snd base))).symm
    · rw [CategoryTheory.Functor.map_comp_apply]
      exact hr
  rw [hv,decode_formulaPoint]
  exact FiniteAxiomProof.instantiation σ π d x φ t ψ hff hsub

theorem distribution (p : (U).obj (S).distributionParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertDistribution p)) := by
  let base := (U).map (S).distributionInclusion p
  let x := ((U).map prod.fst base).val
  let φ := decodeFormula P σ π d ((U).map prod.fst ((U).map prod.snd base))
  let ψ := decodeFormula P σ π d ((U).map prod.snd ((U).map prod.snd base))
  have hb : (U).map (S).distributionInclusion p=
      pairPoint (namePoint P x) (pairPoint (formulaPoint P σ π d φ) (formulaPoint P σ π d ψ)) := by
    simp only [base,x,φ,ψ,namePoint_eta,formulaPoint_decode,pairPoint_eta]
  have hx : x∉φ.freeVariables := distribution_absent P σ π d p
  have hv : (U).map (S).hilbertDistribution p=
      formulaPoint P σ π d (.imp (.all x (.imp φ ψ)) (.imp φ (.all x ψ))) := by
    dsimp only [CategoricalSyntax.hilbertDistribution]
    rw [CategoryTheory.Functor.map_comp_apply,hb]
    apply implication_at P σ π d
    · apply quantifier_at P σ π d
      · exact pairPoint_fst _ _
      · exact ((U).map_comp_apply _ _ _).trans
          ((congrArg ((U).map (S).implicationConstructor) (pairPoint_snd _ _)).trans
            (implication_point P σ π d φ ψ))
    · apply implication_at P σ π d
      · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
      · apply quantifier_at P σ π d
        · exact pairPoint_fst _ _
        · erw [CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]
  rw [hv,decode_formulaPoint]
  exact FiniteAxiomProof.distribution σ π d x φ ψ hx

theorem equality (p : (U).obj (S).equalitySchemeParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (S).hilbertEquality p)) := by
  let base := (U).map (S).equalitySchemeInclusion p
  let x := ((U).map prod.fst ((U).map prod.fst base)).val
  let φ := decodeFormula P σ π d ((U).map prod.snd ((U).map prod.fst base))
  let u := decodeTerm P σ π d ((U).map prod.fst ((U).map prod.snd base))
  let t := decodeTerm P σ π d ((U).map prod.snd ((U).map prod.snd base))
  let au := (U).map (S).equalityFirstAdmissible p
  let at₀ := (U).map (S).equalitySecondAdmissible p
  let ψ := decodeFormula P σ π d ((U).map (S).formulaSubstitution au)
  let χ := decodeFormula P σ π d ((U).map (S).formulaSubstitution at₀)
  have hb : pairPoint (pairPoint (namePoint P x) (formulaPoint P σ π d φ))
      (pairPoint (termPoint P σ π d u) (termPoint P σ π d t))=base := by
    simp only [x,φ,u,t,namePoint_eta,formulaPoint_decode,termPoint_decode,pairPoint_eta]
  have hinputu : (U).map (S).equalityFirstInput base=substitutionPoint P σ π d x φ u := by
    rw [← hb]
    dsimp only [CategoricalSyntax.equalityFirstInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_fst]
  have hinputt : (U).map (S).equalitySecondInput base=substitutionPoint P σ π d x φ t := by
    rw [← hb]
    dsimp only [CategoricalSyntax.equalitySecondInput,substitutionPoint]
    erw [lift_point,lift_point]
    erw [CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_snd,
      CategoryTheory.Functor.map_comp_apply,pairPoint_fst,pairPoint_fst,
      CategoryTheory.Functor.map_comp_apply,pairPoint_snd,pairPoint_snd]
  have hiu : (U).map (S).admissibleInclusion au=substitutionPoint P σ π d x φ u := by
    have h := congrArg (fun f => (U).map f p) (S).equality_first_admissible
    simp only [CategoryTheory.Functor.map_comp_apply] at h
    exact h.symm.trans hinputu
  have hit : (U).map (S).admissibleInclusion at₀=substitutionPoint P σ π d x φ t := by
    have h := congrArg (fun f => (U).map f p) (S).equality_second_admissible
    simp only [CategoryTheory.Functor.map_comp_apply] at h
    exact h.symm.trans hinputt
  have hru : (U).map (S).formulaSubstitution au=formulaPoint P σ π d ψ :=
    (formulaPoint_decode P σ π d _).symm
  have hrt : (U).map (S).formulaSubstitution at₀=formulaPoint P σ π d χ :=
    (formulaPoint_decode P σ π d _).symm
  obtain ⟨hfu,hsu⟩ := substitution_reflects_native P σ π d au x φ u ψ hiu hru
  obtain ⟨hft,hst⟩ := substitution_reflects_native P σ π d at₀ x φ t χ hit hrt
  have hv : (U).map (S).hilbertEquality p=formulaPoint P σ π d (.imp (.equal u t) (.imp ψ χ)) := by
    dsimp only [CategoricalSyntax.hilbertEquality]
    apply implication_at P σ π d
    · rw [CategoryTheory.Functor.map_comp_apply,CategoryTheory.Functor.map_comp_apply]
      change (U).map (S).equalityConstructor ((U).map prod.snd base)=_
      rw [← hb,pairPoint_snd]
      exact equality_point P σ π d u t
    · apply implication_at P σ π d
      · rw [CategoryTheory.Functor.map_comp_apply]
        exact hru
      · rw [CategoryTheory.Functor.map_comp_apply]
        exact hrt
  rw [hv,decode_formulaPoint]
  exact FiniteAxiomProof.equality σ π d x φ u t ψ χ hfu hft hsu hst

/-- Finite coproduct decomposition uses the actual preserved injections;
no scalar parity convention for a chosen logical-parameter coproduct is imposed. -/
private theorem coproduct_point_cases {A B : Total.TotalCategory P} (p : (U).obj (A ⨿ B)) :
    (∃ a,(U).map (coprod.inl : A ⟶ A ⨿ B) a=p) ∨
      ∃ b,(U).map (coprod.inr : B ⟶ A ⨿ B) b=p :=
  Derivation.WordInduction.coprod_cases A B p

private theorem copair_finite {A B : Total.TotalCategory P}
    (f : A ⟶ (S).algebra.a.2) (g : B ⟶ (S).algebra.a.2)
    (hf : ∀ a,FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map f a)))
    (hg : ∀ b,FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map g b)))
    (p : (U).obj (A ⨿ B)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d ((U).map (coprod.desc f g) p)) := by
  rcases coproduct_point_cases P p with ⟨a,ha⟩ | ⟨b,hb⟩
  · rw [← ha,← CategoryTheory.Functor.map_comp_apply,coprod.inl_desc]
    exact hf a
  · rw [← hb,← CategoryTheory.Functor.map_comp_apply,coprod.inr_desc]
    exact hg b

end SchemeReflection

/-- Every point of the actual seven-scheme coproduct gives a finite native
proof; no extra Γ enumeration premise is needed for logical schemes. -/
theorem logical_parameter_finite (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
    (Γ : Set ℕ) (l : Total.underlying.obj (syntaxData P σ π d).logicalParameters) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d
      (Total.underlying.map (syntaxData P σ π d).logicalAxioms l)) := by
  dsimp only [CategoricalSyntax.logicalAxioms]
  apply SchemeReflection.copair_finite P σ π d Γ
  · intro p
    apply SchemeReflection.copair_finite P σ π d Γ
    · intro p
      apply SchemeReflection.copair_finite P σ π d Γ
      · intro p
        apply SchemeReflection.copair_finite P σ π d Γ
        · intro p
          apply SchemeReflection.copair_finite P σ π d Γ
          · intro p
            apply SchemeReflection.copair_finite P σ π d Γ
            · exact SchemeReflection.one P σ π d Γ
            · exact SchemeReflection.two P σ π d Γ
          · exact SchemeReflection.three P σ π d Γ
        · exact SchemeReflection.instantiation P σ π d Γ
      · exact SchemeReflection.distribution P σ π d Γ
    · exact SchemeReflection.reflexivity P σ π d Γ
  · exact SchemeReflection.equality P σ π d Γ

theorem logical_scheme_finite (P : Uniform.Family) (σ π : ℕ → Carrier) (d : ℕ)
    (Γ : Set ℕ) (i : Fin 7)
    (p : Total.underlying.obj (SyntacticFiniteNamedSchemes.schemeParameters (syntaxData P σ π d) i)) :
    FiniteAxiomProof σ π d Γ (decodeFormula P σ π d
      (Total.underlying.map (SyntacticFiniteNamedSchemes.schemeMorphism (syntaxData P σ π d) i) p)) := by
  have h := logical_parameter_finite P σ π d Γ
    (Total.underlying.map (SyntacticFiniteNamedSchemes.schemeInjection (syntaxData P σ π d) i) p)
  rw [← CategoryTheory.Functor.map_comp_apply,SyntacticFiniteNamedSchemes.schemeInjection_formula] at h
  exact h

end CategoricalEssentialIncompleteness.V46.Miller.NamedProofImage
