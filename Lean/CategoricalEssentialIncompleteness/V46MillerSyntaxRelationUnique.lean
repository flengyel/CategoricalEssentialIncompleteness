import CategoricalEssentialIncompleteness.V46MillerSyntaxWordInduction

/-! # Constructor laws imply uniqueness for arbitrary standard-word relations

Relations may be uniform-oracle graphs; no arithmetic definability is
required. The categorical application must derive each candidate's root
laws from its actual algebra-morphism equation. This is not an assumed
initiality or an inference from evaluator-output uniqueness.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Relations
open WordInduction

abbrev Relation := Bool → ℕ → ℕ → ℕ → Prop

/-- The literal ordered polynomial action on arbitrary child relations. -/
def map (Q : ℕ → Prop) (R : Relation) : RawPolynomial → ℕ → ℕ → ℕ → Prop
  | .term,p,u,v => R false p u v
  | .formula,p,u,v => R true p u v
  | .coefficient C,p,u,v => Q p ∧ C.val.Evalb (M := ℕ) ![u] ∧ v=u
  | .unit,p,u,v => Q p ∧ u=0 ∧ v=0
  | .product a b,p,u,v => map Q R a p (π₁ u) (π₁ v) ∧ map Q R b p (π₂ u) (π₂ v)
  | .sum a b,p,u,v =>
      (π₂ u=0 ∧ π₂ v=0 ∧ map Q R a p (π₁ u) (π₁ v)) ∨
        (π₂ u=1 ∧ π₂ v=1 ∧ map Q R b p (π₁ u) (π₁ v))

/-- The ordered child induction hypotheses determine the entire output tuple. -/
theorem map_compare (Q : ℕ → Prop) (R S : Relation) (q : RawPolynomial) (p u v w : ℕ)
    (hc : ChildHolds (fun sort child => ∀ r x y,R sort r child x → S sort r child y → x=y) q u)
    (hv : map Q R q p u v) (hw : map Q S q p u w) : v=w := by
  induction q generalizing u v w with
  | term => exact hc p v w hv hw
  | formula => exact hc p v w hv hw
  | coefficient _ => exact hv.2.2.trans hw.2.2.symm
  | unit => exact hv.2.2.trans hw.2.2.symm
  | product a b ia ib =>
      have hcv : ChildHolds (fun sort child => ∀ r x y,R sort r child x → S sort r child y → x=y) a (π₁ u) ∧
          ChildHolds (fun sort child => ∀ r x y,R sort r child x → S sort r child y → x=y) b (π₂ u) := hc
      have h1 := ia (π₁ u) (π₁ v) (π₁ w) hcv.1 hv.1 hw.1
      have h2 := ib (π₂ u) (π₂ v) (π₂ w) hcv.2 hv.2 hw.2
      calc
        v=⟪π₁ v,π₂ v⟫ := (pair_unpair v).symm
        _=⟪π₁ w,π₂ w⟫ := by rw [h1,h2]
        _=w := pair_unpair w
  | sum a b ia ib =>
      rcases hv with ⟨hu0,hv0,hv⟩ | ⟨hu1,hv1,hv⟩
      · rcases hw with ⟨_,hw0,hw⟩ | ⟨hu1,_,_⟩
        · have hca : ChildHolds (fun sort child => ∀ r x y,R sort r child x → S sort r child y → x=y) a (π₁ u) :=
            by simpa [ChildHolds,hu0] using hc
          have h1 := ia (π₁ u) (π₁ v) (π₁ w) hca hv hw
          calc
            v=⟪π₁ v,π₂ v⟫ := (pair_unpair v).symm
            _=⟪π₁ w,π₂ w⟫ := by rw [h1,hv0,hw0]
            _=w := pair_unpair w
        · omega
      · rcases hw with ⟨hu0,_,_⟩ | ⟨_,hw1,hw⟩
        · omega
        · have hcb : ChildHolds (fun sort child => ∀ r x y,R sort r child x → S sort r child y → x=y) b (π₁ u) :=
            by simpa [ChildHolds,hu1] using hc
          have h1 := ib (π₁ u) (π₁ v) (π₁ w) hcb hv hw
          calc
            v=⟪π₁ v,π₂ v⟫ := (pair_unpair v).symm
            _=⟪π₁ w,π₂ w⟫ := by rw [h1,hv1,hw1]
            _=w := pair_unpair w

/-- A forward root law is extracted from each actual algebra homomorphism.
It states constructor commutation; it contains no uniqueness conclusion. -/
def RootLaw (a b : RawPolynomial) (Q : ℕ → Prop) (op R : Relation) : Prop :=
  ∀ (formula : Bool) (p u value : ℕ),
    (rawCarrier (Postfix.carrier false a b) (Postfix.carrier true a b)
      (if formula then b else a)).val.Evalb (M := ℕ) ![u] →
    R formula p (constructor formula (if formula then b else a) u) value →
      ∃ v,map Q R (if formula then b else a) p u v ∧ op formula p v value

/-- Comparison covers ALL relations satisfying the actual constructor law,
so arbitrary categorical candidates are included once their law is derived. -/
theorem word_relation_unique (a b : RawPolynomial) (Q : ℕ → Prop) (op R S : Relation)
    (hOp : ∀ formula p u x y,op formula p u x → op formula p u y → x=y)
    (hR : RootLaw a b Q op R) (hS : RootLaw a b Q op S) :
    ∀ formula word,(Postfix.carrier formula a b).val.Evalb (M := ℕ) ![word] →
      ∀ p x y,R formula p word x → S formula p word y → x=y := by
  apply word_induction a b (fun formula word => ∀ p x y,R formula p word x → S formula p word y → x=y)
  intro formula u hu hc p x y hx hy
  obtain ⟨v,hv,hox⟩ := hR formula p u x hu hx
  obtain ⟨w,hw,hoy⟩ := hS formula p u y hu hy
  have he := map_compare Q R S (if formula then b else a) p u v w hc hv hw
  subst w
  exact hOp formula p v x y hox hoy

theorem plain_word_relation_unique (a b : RawPolynomial) (Q : ℕ → Prop) (op R S : Relation)
    (hOp : ∀ formula p u x y,op formula p u x → op formula p u y → x=y)
    (hR : RootLaw a b Q op R) (hS : RootLaw a b Q op S) :
    ∀ formula word,(Postfix.plainCarrier formula a b).val.Evalb (M := ℕ) ![word] →
      ∀ p x y,R formula p word x → S formula p word y → x=y := by
  intro formula word hw
  exact word_relation_unique a b Q op R S hOp hR hS formula word
    ((Postfix.carrier_plain_model formula a b word).mpr hw)

end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Relations
