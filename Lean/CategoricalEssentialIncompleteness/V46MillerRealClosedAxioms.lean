/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerOrderedFieldSyntax

/-! # An actual recursive ordered-field and real-closure axiom presentation

The finite axioms present a commutative field with strict linear order.
Positive square roots and every odd-degree polynomial-root scheme are
then included literally. Recognition computes the consecutive universal
constructor suffix and checks equality with the corresponding generated
word. The semantic real-closed-field comparison is a separate obligation.
-/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms
open OrderedFieldSyntax
open SyntacticSyntax SyntacticSyntax.Coding SyntacticSyntax.NatVectors
open NamedPostfixEncoding (allInput impInput pack_adjoin append_pack)

def conjunction (φ ψ : Formula) : Formula := negation (imp φ (negation ψ))
def disjunction (φ ψ : Formula) : Formula := imp (negation φ) ψ
def existential (name : ℕ) (φ : Formula) : Formula := negation (all name (negation φ))
def close (names : List ℕ) (φ : Formula) : Formula := names.foldr all φ

theorem closure_freeVariables (names : List ℕ) (φ : Formula) (x : ℕ) :
    x∈(close names φ).freeVariables ↔ x∈φ.freeVariables ∧ x∉names := by
  induction names with
  | nil => simp [close]
  | cons y names ih =>
      simp only [close,List.foldr_cons,all,NamedFiniteSyntax.Formula.freeVariables,List.mem_filter]
      change (x∈(close names φ).freeVariables ∧ (x != y)=true) ↔ x∈φ.freeVariables ∧ x∉y::names
      rw [ih]
      simp only [bne_iff_ne,List.mem_cons,not_or]
      tauto

theorem close_closed (names : List ℕ) (φ : Formula)
    (h : ∀ x,x∈φ.freeVariables → x∈names) : (close names φ).freeVariables=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  obtain ⟨hx,hn⟩ := (closure_freeVariables names φ x).mp hx
  exact hn (h x hx)

theorem existential_freeVariables (name : ℕ) (φ : Formula) (x : ℕ) :
    x∈(existential name φ).freeVariables ↔ x∈φ.freeVariables ∧ x≠name := by
  simp [existential,negation,all,NamedFiniteSyntax.Formula.freeVariables,bne_iff_ne]

/-- Every coefficient variable occurs in this finite ordered Horner term.
The final zero is a literal zero term, not an additional coefficient. -/
def hornerList (root : ℕ) (indices : List ℕ) : Term :=
  indices.foldr (fun i previous => add (var i) (mul (var root) previous)) zero

def horner (degree root : ℕ) : Term := hornerList root (List.range (degree+1))

theorem hornerList_freeVariables (root : ℕ) (indices : List ℕ) (x : ℕ)
    (h : x∈(hornerList root indices).freeVariables) : x∈indices ∨ x=root := by
  induction indices with
  | nil => simp [hornerList] at h
  | cons i indices ih =>
      have hx : x=i ∨ x=root ∨ x∈(hornerList root indices).freeVariables := by
        simpa [hornerList,var,NamedFiniteSyntax.Term.freeVariables] using h
      rcases hx with hx | hx | hx
      · exact Or.inl (List.mem_cons.mpr (Or.inl hx))
      · exact Or.inr hx
      · exact (ih hx).elim (fun hi => Or.inl (List.mem_cons_of_mem i hi)) Or.inr

theorem horner_freeVariables (degree root x : ℕ) (h : x∈(horner degree root).freeVariables) :
    x<degree+1 ∨ x=root := by
  rcases hornerList_freeVariables root (List.range (degree+1)) x h with hx | hx
  · exact Or.inl (List.mem_range.mp hx)
  · exact Or.inr hx

def oddBody (degree : ℕ) : Formula :=
  imp (negation (.equal (var degree) zero))
    (existential (degree+1) (.equal (horner degree (degree+1)) zero))

def oddSentence (n : ℕ) : Formula :=
  close (List.range (2*n+2)) (oddBody (2*n+1))

theorem oddBody_freeVariables (degree x : ℕ) (h : x∈(oddBody degree).freeVariables) :
    x<degree+1 := by
  have hx : x=degree ∨ x∈(existential (degree+1)
      (.equal (horner degree (degree+1)) zero)).freeVariables := by
    simpa [oddBody,imp,negation,var,NamedFiniteSyntax.Formula.freeVariables,
      NamedFiniteSyntax.Term.freeVariables] using h
  rcases hx with rfl | hx
  · omega
  · obtain ⟨hx,hn⟩ := (existential_freeVariables (degree+1) _ x).mp hx
    have hh : x∈(horner degree (degree+1)).freeVariables := by
      simpa only [NamedFiniteSyntax.Formula.freeVariables,zero_freeVariables,List.append_nil] using hx
    exact (horner_freeVariables degree (degree+1) x hh).elim id (fun he => False.elim (hn he))

theorem oddSentence_closed (n : ℕ) : (oddSentence n).freeVariables=[] := by
  apply close_closed
  intro x hx
  exact List.mem_range.mpr (by simpa only [Nat.add_assoc] using oddBody_freeVariables (2*n+1) x hx)

/-- Ring, inverse, and strict-linear-order matrices, on literal names 0,1,2. -/
def finiteMatrices : List Formula := [
  .equal (add (add (var 0) (var 1)) (var 2)) (add (var 0) (add (var 1) (var 2))),
  .equal (add (var 0) (var 1)) (add (var 1) (var 0)),
  .equal (add (var 0) zero) (var 0),
  .equal (add (var 0) (neg (var 0))) zero,
  .equal (mul (mul (var 0) (var 1)) (var 2)) (mul (var 0) (mul (var 1) (var 2))),
  .equal (mul (var 0) (var 1)) (mul (var 1) (var 0)),
  .equal (mul (var 0) one) (var 0),
  .equal (mul (var 0) (add (var 1) (var 2)))
    (add (mul (var 0) (var 1)) (mul (var 0) (var 2))),
  negation (.equal zero one),
  imp (negation (.equal (var 0) zero))
    (existential 1 (.equal (mul (var 0) (var 1)) one)),
  negation (lt (var 0) (var 0)),
  imp (conjunction (lt (var 0) (var 1)) (lt (var 1) (var 2))) (lt (var 0) (var 2)),
  disjunction (lt (var 0) (var 1))
    (disjunction (.equal (var 0) (var 1)) (lt (var 1) (var 0))),
  imp (lt (var 0) (var 1)) (lt (add (var 0) (var 2)) (add (var 1) (var 2))),
  imp (conjunction (lt zero (var 0)) (lt zero (var 1))) (lt zero (mul (var 0) (var 1))),
  lt zero one]

def positiveSquare : Formula := all 0
  (imp (lt zero (var 0)) (existential 1 (.equal (mul (var 1) (var 1)) (var 0))))

def finiteSentences : List Formula := finiteMatrices.map (close [0,1,2]) ++
  [asymmetrySentence,positiveSquare]

theorem positiveSquare_closed : positiveSquare.freeVariables=[] := by
  simp [positiveSquare,existential,all,imp,negation,var,
    NamedFiniteSyntax.Formula.freeVariables,NamedFiniteSyntax.Term.freeVariables]

theorem finiteSentences_closed : ∀ φ∈finiteSentences,φ.freeVariables=[] := by
  simp [finiteSentences,finiteMatrices,close,conjunction,disjunction,existential,all,imp,negation,
    var,NamedFiniteSyntax.Formula.freeVariables,NamedFiniteSyntax.Term.freeVariables,
    asymmetrySentence_closed,positiveSquare_closed]

def hornerWord (degree root : ℕ) : ℕ := (List.range (degree+1)).foldr
  (fun i previous => binaryWord 0 (varWord i) (binaryWord 1 (varWord root) previous)) (nullaryWord 0)

def closeWord (names : List ℕ) (body : ℕ) : ℕ := names.foldr allWord body

theorem formulaCode_close (names : List ℕ) (φ : Formula) :
    formulaCode (close names φ)=closeWord names (formulaCode φ) := by
  induction names with
  | nil => rfl
  | cons i names ih =>
      change formulaCode (all i (close names φ))=allWord i (closeWord names (formulaCode φ))
      rw [formulaCode_all,ih]

theorem termCode_hornerList (root : ℕ) (indices : List ℕ) :
    termCode (hornerList root indices)=indices.foldr
      (fun i previous => binaryWord 0 (varWord i) (binaryWord 1 (varWord root) previous)) (nullaryWord 0) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
      change termCode (add (var i) (mul (var root) (hornerList root indices))) =
        binaryWord 0 (varWord i) (binaryWord 1 (varWord root)
          (indices.foldr (fun j previous => binaryWord 0 (varWord j)
            (binaryWord 1 (varWord root) previous)) (nullaryWord 0)))
      simp only [termCode_add,termCode_var,termCode_mul,ih]

theorem termCode_horner (degree root : ℕ) : termCode (horner degree root)=hornerWord degree root :=
  termCode_hornerList root (List.range (degree+1))

def oddWord (n : ℕ) : ℕ := closeWord (List.range (2*n+2))
  (impWord (negationWord (equalWord (varWord (2*n+1)) (nullaryWord 0)))
    (negationWord (allWord (2*n+2)
      (negationWord (equalWord (hornerWord (2*n+1) (2*n+2)) (nullaryWord 0))))))

theorem formulaCode_oddSentence (n : ℕ) : formulaCode (oddSentence n)=oddWord n := by
  simp only [oddSentence,formulaCode_close,oddBody,existential,termCode_horner,
    oddWord,formulaCode_imp,formulaCode_negation,formulaCode_all,formulaCode_equal,
    termCode_var,termCode_zero,Nat.add_assoc]

theorem hornerWord_primrec : Primrec₂ hornerWord := by
  have hs : Primrec₂ (fun x : ℕ × ℕ => fun t : ℕ × ℕ =>
      binaryWord 0 (varWord t.1) (binaryWord 1 (varWord x.2) t.2)) :=
    ((binaryWord_primrec 0).comp
      (varWord_primrec.comp (Primrec.fst.comp Primrec.snd))
      ((binaryWord_primrec 1).comp
        (varWord_primrec.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂
  exact Primrec.list_foldr
    (Primrec.list_range.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)))
    (Primrec.const (nullaryWord 0)) hs

theorem closeWord_primrec : Primrec₂ closeWord :=
  Primrec.list_foldr Primrec.fst Primrec.snd
    ((allWord_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

theorem oddWord_primrec : Primrec oddWord := by
  have hd : Primrec (fun n : ℕ => 2*n+1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)
  have hr : Primrec (fun n : ℕ => 2*n+2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 2)
  have hn := negationWord_primrec.comp
    (equalWord_primrec.comp (varWord_primrec.comp hd) (Primrec.const (nullaryWord 0)))
  have he := negationWord_primrec.comp
    (allWord_primrec.comp hr (negationWord_primrec.comp
      (equalWord_primrec.comp (hornerWord_primrec.comp hd hr) (Primrec.const (nullaryWord 0)))))
  exact closeWord_primrec.comp (Primrec.list_range.comp hr) (impWord_primrec.comp hn he)

/-- Only the literal formula-sort bit and the outer ALL tag are inspected.
Final equality with a generated word checks all other labels and nodes. -/
def allTag (record : ℕ) : Bool := decide ((Nat.unpair record).2=1 ∧
  (Nat.unpair (Nat.unpair record).1).2=1)
def allRecord (name : ℕ) : ℕ := Arithmetic.pair (allInput name 0) 1
def impRecord : ℕ := Arithmetic.pair (impInput 0 0) 1
def allSuffix (word : ℕ) : ℕ := ((Nat.natToList word).reverse.takeWhile allTag).length

theorem allTag_allRecord (name : ℕ) : allTag (allRecord name)=true := by
  simp [allTag,allRecord,allInput,nat_pair_eq]
theorem allTag_impRecord : allTag impRecord=false := by
  simp [allTag,impRecord,impInput,nat_pair_eq]

theorem allWord_concat (name word : ℕ) : allWord name word=concat word (allRecord name) := by
  simp [allWord,Coding.constructor,formulaPolynomial,NamedPostfixEncoding.formulaPolynomial,
    SyntaxPolynomial.formulaExpression,allInput,Coding.shape,Coding.childrenWord,allRecord]

theorem impWord_concat (left right : ℕ) :
    impWord left right=concat (Words.append left right) impRecord := by
  simp [impWord,Coding.constructor,formulaPolynomial,NamedPostfixEncoding.formulaPolynomial,
    SyntaxPolynomial.formulaExpression,SyntaxPolynomial.power,impInput,Coding.shape,
    Coding.childrenWord,impRecord]

theorem natToList_concat (word record : ℕ) :
    Nat.natToList (concat word record)=Nat.natToList word++[record] := by
  calc
    Nat.natToList (concat word record)=Nat.natToList
        (Words.append (pack (Nat.natToList word)) (pack [record])) := by
      rw [pack_natToList,pack_adjoin,pack_nil,Words.append_singleton]
    _ = Nat.natToList word++[record] := by rw [append_pack,natToList_pack]

theorem allSuffix_allWord (name word : ℕ) : allSuffix (allWord name word)=allSuffix word+1 := by
  simp [allSuffix,allWord_concat,natToList_concat,allTag_allRecord]
theorem allSuffix_impWord (left right : ℕ) : allSuffix (impWord left right)=0 := by
  simp [allSuffix,impWord_concat,natToList_concat,allTag_impRecord]

theorem closeWord_suffix (names : List ℕ) (word : ℕ) :
    allSuffix (closeWord names word)=allSuffix word+names.length := by
  induction names with
  | nil => simp [closeWord]
  | cons i names ih =>
      change allSuffix (allWord i (closeWord names word))=allSuffix word+(i::names).length
      rw [allSuffix_allWord,ih,List.length_cons]
      omega

theorem oddWord_suffix (n : ℕ) : allSuffix (oddWord n)=2*n+2 := by
  rw [oddWord,closeWord_suffix,allSuffix_impWord,List.length_range]
  omega

theorem allTag_primrec : Primrec allTag :=
  ((Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1)).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.const 1))).decide

theorem allSuffix_primrec : Primrec allSuffix :=
  Primrec.list_length.comp ((Primrec.list_takeWhile allTag_primrec).comp
    (Primrec.list_reverse.comp Primrec.nat_natToList))

def oddIndex (word : ℕ) : ℕ := (allSuffix word-2)/2
def OddAxiomWord (word : ℕ) : Prop :=
  2≤allSuffix word ∧ allSuffix word%2=0 ∧ word=oddWord (oddIndex word)

theorem odd_generator_iff (word : ℕ) : OddAxiomWord word ↔ ∃ n,word=oddWord n := by
  constructor
  · intro h
    exact ⟨oddIndex word,h.2.2⟩
  · rintro ⟨n,rfl⟩
    have hi : oddIndex (oddWord n)=n := by rw [oddIndex,oddWord_suffix]; omega
    refine ⟨?_,?_,?_⟩
    · rw [oddWord_suffix]; omega
    · rw [oddWord_suffix]; omega
    · rw [hi]

theorem oddAxiomWord_primrec : PrimrecPred OddAxiomWord := by
  have hi : Primrec oddIndex := Primrec.nat_div.comp
    (Primrec.nat_sub.comp allSuffix_primrec (Primrec.const 2)) (Primrec.const 2)
  exact (Primrec.nat_le.comp (Primrec.const 2) allSuffix_primrec).and
    ((Primrec.eq.comp (Primrec.nat_mod.comp allSuffix_primrec (Primrec.const 2)) (Primrec.const 0)).and
      (Primrec.eq.comp Primrec.id (oddWord_primrec.comp hi)))

def finiteWords : List ℕ := finiteSentences.map formulaCode
def RCFAxiomWords : Set ℕ := {word | word∈finiteWords ∨ OddAxiomWord word}

theorem rcf_generator_iff (word : ℕ) : word∈RCFAxiomWords ↔
    (∃ φ∈finiteSentences,formulaCode φ=word) ∨ ∃ n,word=oddWord n := by
  simp only [RCFAxiomWords,Set.mem_ofPred_eq,finiteWords,List.mem_map,odd_generator_iff]

theorem rcfAxiomWords_primrec : PrimrecPred (·∈RCFAxiomWords) := by
  have hf : PrimrecPred (fun word : ℕ => word∈finiteWords) :=
    ((Primrec.eq (α := ℕ)).exists_mem_list.comp (Primrec.const finiteWords) Primrec.id).of_eq
      (fun word => by simp)
  exact hf.or oddAxiomWord_primrec

theorem rcfAxiomWords_sentences (word : ℕ) (h : word∈RCFAxiomWords) :
    sentencePredicate.val.Evalb ![word] := by
  rcases (rcf_generator_iff word).mp h with ⟨φ,hφ,rfl⟩ | ⟨n,rfl⟩
  · exact (sentence_formulaCode φ).mpr (finiteSentences_closed φ hφ)
  · rw [← formulaCode_oddSentence]
    exact (sentence_formulaCode (oddSentence n)).mpr (oddSentence_closed n)

theorem asymmetry_mem : asymmetryWord∈RCFAxiomWords := by
  apply Or.inl
  exact List.mem_map.mpr ⟨asymmetrySentence,by simp [finiteSentences],rfl⟩
theorem positiveSquare_mem : formulaCode positiveSquare∈RCFAxiomWords := by
  apply Or.inl
  exact List.mem_map.mpr ⟨positiveSquare,by simp [finiteSentences],rfl⟩
theorem oddSentence_mem (n : ℕ) : formulaCode (oddSentence n)∈RCFAxiomWords := by
  apply Or.inr
  apply (odd_generator_iff _).mpr
  exact ⟨n,formulaCode_oddSentence n⟩

/-- The actual word axiom set requested for the point a. -/
def theoryAxioms (a : Point) : Set ℕ := RCFAxiomWords∪cutAxioms a

theorem theoryAxioms_enumerable (a : Point) :
    Uniform.Enumerable (Uniform.Family.ofPoint a) (·∈theoryAxioms a) :=
  (Uniform.Enumerable.of_re rcfAxiomWords_primrec.computablePred.to_re).or (cutAxioms_enumerable a)

theorem theoryAxioms_sentences (a : Point) (word : ℕ) (h : word∈theoryAxioms a) :
    sentencePredicate.val.Evalb ![word] :=
  h.elim (rcfAxiomWords_sentences word) (cutAxioms_sentences a word)

theorem theory_asymmetry_mem (a : Point) : asymmetryWord∈theoryAxioms a := Or.inl asymmetry_mem
theorem theory_lower_cut_axiom (a : Point) (n : ℕ) (h : (a n : ℝ)<1/2) :
    theta n∈theoryAxioms a := Or.inr (lower_cut_axiom a n h)
theorem theory_upper_cut_axiom (a : Point) (n : ℕ) (h : 1/2<(a n : ℝ)) :
    formulaCode (lt one (mul (natural 2) (c n)))∈theoryAxioms a := Or.inr (upper_cut_axiom a n h)

end CategoricalEssentialIncompleteness.V46.Miller.RealClosedAxioms
