# Other theories and precomplete equivalence relations

The existence of a compatible categorical presentation is sufficient for an
essential-incompleteness theorem about the theories admitting it. Such a
theorem need not construct presentations from every recursion category.
This record gives applications beyond PA in its original language and
identifies precompleteness as relevant established structure.

## 1. The existence theorem has a relative scope

Fix a computational category with domains and finite domain joins. Suppose
each consistent extension T of B has selected domains I_T,Z_T on the same
object P, arising as the identity and zero fibers of its presentation.
A computational separator is a pair c,d of domains on P with cd=0,
c join d=1_P, I_T≤c and Z_T≤d. Inseparability means that no such pair exists.
Suppose the actual extension maps give I_B≤I_T and Z_B≤Z_T, consistency
gives I_T Z_T=0, and completeness would give a computational separator
of I_T,Z_T. If I_B,Z_B are inseparable, every such T is incomplete: any
separator of the enlarged pair also separates the base pair.

This is the established pair-transport argument. Once base inseparability
and the compatible presentations exist, constructing a derivation object
anew in every application is unnecessary. A full backwards functor on all
arrows is also unnecessary. The theorem is about this class of presentations;
it does not assert that an arbitrary equivalence relation has these properties.

## 2. Inverse images of theories under effective translations

Identify a theory with its set of theorems, using a c.e. axiom presentation
when enumerating proofs. Let T be a consistent c.e. theory. Let theta send arithmetic sentences
effectively to sentences in T's language. Require the following translation
properties: PA theorems translate to T theorems; finite classical deductions
from arithmetic premises translate to deductions from their translations;
and theta commutes with negation and falsum up to equivalence provable in T.
Ordinary effective relative interpretations of PA satisfy these requirements.
The negative translation considered below does too.

Define the arithmetic theory

\[
 T^\theta=\{\varphi\in\operatorname{Sent}(L_{\mathrm{PA}}):
                   T\vdash\varphi^\theta\}.
\]

**Proposition.** T^theta is a consistent c.e. extension of PA, closed under
classical deduction. Completeness of T implies completeness of T^theta.

**Proof.** Dovetail over arithmetic sentences and finite T-proofs to enumerate
membership in T^theta. This works even when there is no effective inverse
to the translation. The theorem-translation property gives PA⊆T^theta.
Translation of finite deductions gives deductive closure. If T^theta proved
falsum, translating that deduction would make T inconsistent. Finally, for
each arithmetic sentence phi, completeness of T supplies a proof of phi^theta
or its negation. The negation clause puts phi or not-phi in T^theta. No
soundness assumption is used. QED.

Consequently define

\[
 S_{T,\theta}:=S_{T^\theta}.
\]

This uses the already-valid unprimed construction. Objects are the same
formal numerical types; arrows are the same typed program representatives,
with equality

\[
 [e]=[f]\quad\Longleftrightarrow\quad
 T\vdash\operatorname{Eq}(e,f)^\theta.
\]

Here Eq is the single uniformly quantified graph-equality sentence. The
composition, restriction, range and Turing-morphism results for S_B apply
because B=T^theta is a consistent c.e. extension of PA. No new pointwise
quotient or new proof of those categorical laws is needed.

For T⊆T', use the same translation, now into T'. Then T^theta⊆(T')^theta,
and the actual covariant quotient functor is

\[
 S_{T^\theta}\longrightarrow S_{(T')^\theta},
 \qquad X\longmapsto X,\qquad[e]\longmapsto[e].
\]

It preserves the chosen Turing morphism and the fixed structural operations.
Its identity and zero fibers contain the fixed PA fibers and remain
disjoint. The earlier inseparability proof therefore applies. Alternatively,
completeness of T would make T^theta a complete consistent c.e. extension
of PA, contradicting that proof.

For a source category, take pairs (T,theta) as objects and effective
deduction-preserving sentence translations j:T→T' as arrows. They must
preserve provable equivalence and satisfy
\[
 T'\vdash(\varphi^\theta)^j\leftrightarrow\varphi^{\theta'}
 \quad\text{for every arithmetic sentence }\varphi.
\]
Use actual translation functions, with identity functions and function
composition; proof preservation makes the compatibility condition closed
under composition. Ordinary effective interpretations give examples of
these arrows. For any such arrow, T^theta⊆(T')^theta'. Hence
(T,theta)↦S_(T^theta), with j sent to the displayed quotient functor,
defines a covariant functor into Cat. Its identity and composition laws
hold on the unchanged program representatives. This is not a claim that
all of the target theory's structure is represented by its arithmetic part.

## 3. Checked applications

1. **Second-order arithmetic.** For ACA_0, use the inclusion of first-order
   arithmetic. Simpson, Remark I.3.3, proves that PA is exactly its
   first-order part. Thus (ACA_0)^theta=PA and the associated category here
   is S_PA. Every consistent c.e. extension of ACA_0 gives the corresponding
   quotient category. The use of second-order notation does not assume full
   second-order semantic consequence; the deductive system is effective.
2. **Finite set theory.** Kaye and Wong, Definition 7 and Theorem 8, give
   an effective interpretation o:PA→ZF_{-inf} through ordinals. Their exact
   theory is EST + Power Set + Foundation + not-Infinity, with EST comprising
   Extensionality, Empty Set, Pair Set, Union, Separation and Replacement.
   Therefore S_{T^o} exists for every consistent c.e. extension T of this
   theory. Transitive containment is not required for this direction;
   stronger inverse/bi-interpretation claims require separate care.
3. **Intuitionistic arithmetic.** Let N be the Goedel--Gentzen negative
   translation. It translates PA deductions into HA deductions and commutes
   with implication, conjunction and negation up to intuitionistically
   provable equivalence. Thus T^N is a consistent c.e. classical extension
   of PA for every consistent c.e. intuitionistic extension T of HA. In
   fact HA^N=PA: one inclusion is negative translation; for the other, PA
   contains HA's theorems and classically proves phi^N equivalent to phi.
   The category at the base is again S_PA. Completeness here means deciding
   every sentence by a proof of it or its negation; it is not the schema
   of excluded middle.

These are constructions using existing arithmetic translations. They do not
claim intrinsically nonnumerical computability. PRA, I-Sigma_1, RCA_0 and Q
are not listed as verified instances of the entire S_T construction here:
their uniform program-equation requirements need a separate weak-base check.

## 4. Precompleteness supplies a standard structural hypothesis

For an equivalence relation R on natural-number codes, precompleteness
means that every partial recursive psi has a total recursive h such that

\[
 \psi(n)\mathord\downarrow\quad\Longrightarrow\quad h(n)\ R\ \psi(n).
\]

In a restriction category the corresponding condition on an equivalence
domain rho on P×P is: for every partial psi:X⇀P there exists a total
h:X→P with

\[
 \overline{\rho\langle\psi,h\rangle}=\bar\psi.
\]

The pairing is partial, with restriction bar(psi); the displayed equation
says that the relation test imposes no additional restriction there.
If rho≤rho' and rho' is an equivalence domain, the same h witnesses
precompleteness of rho': the restriction of rho'<psi,h> is bounded above
by bar(psi) and below by the displayed restriction for rho.

This is established terminology, not a new proposed definition. Bernardi
(1986), Definition 1, formulates it in dominical categories. His Section 3,
Theorem 2 proves inseparability of two nonempty disjoint unions of classes
under the stated c-plus-dominical recursion-category hypotheses. Those
hypotheses are not silently transferred to nondominical S_T or to arbitrary
Heller-1990 categories. The elementary numerical argument below is enough
for the applications in this record.

**Lemma.** Any two distinct classes of a precomplete equivalence relation
on natural-number codes are recursively inseparable.

**Proof.** Fix the usual recursively inseparable c.e. sets A,B and two
inequivalent codes u,v. A partial recursive psi outputs u when a witness
for n∈A is found and v when a witness for n∈B is found, using dovetailing.
Disjointness makes this well-defined. Precompleteness supplies a total h
with h(A)⊆[u]_R and h(B)⊆[v]_R. Pulling back a recursive separator along
h would separate A,B. QED. If R is c.e., its two classes are c.e. domains
in the classical recursion category.

Define the uniform PA program-equivalence relation by
\[
 e\ R_{\mathrm{PA}}\ f\quad\Longleftrightarrow\quad
 \mathrm{PA}\vdash\operatorname{Eq}(e,f).
\]
This relation is precomplete. Given partial
recursive psi, the parameter theorem supplies a total recursive h for the
family that, on input x, first computes psi(n)=k and then runs program k
on x. Whenever psi(n)=k terminates, PA verifies that finite trace and proves
the uniform graph equality Eq(h(n),k). Thus h(n) R_PA psi(n). This uses
the same PA-verified program specifications as the existing S_T proof.
Every extension R_T⊇R_PA remains precomplete. Identity and zero are two
distinct classes when T is consistent. Bernardi explicitly records this
program-equivalence example; the calculation above reconstructs it.

Program equivalence must not be confused with unrestricted provable
equivalence of arithmetic sentences. The latter has the computable
fixed-point-free negation operation and is not precomplete; see
Barendregt--Terwijn, Section 2.

## 5. A different deductive example: lambda theories

Let T be a consistent c.e. lambda theory containing beta conversion. Use
an effective numbering M_n of closed lambda terms and put

\[
 n\ R_T\ m\quad\Longleftrightarrow\quad T\vdash M_n=M_m.
\]

Closed lambda terms modulo beta conversion form a precomplete numbering
(Barendregt--Terwijn, Section 2, p.3). Enlarging this relation to R_T
preserves precompleteness. Let K=lambda x y.x and K_*=lambda x y.y, and
fix their indices k,k_*. Their classes must be distinct: equating these
terms and applying to arbitrary M,N would equate M and N. Thus

\[
 A_T=\{n:T\vdash M_n=K\},\qquad
 B_T=\{n:T\vdash M_n=K_*\}
\]

are disjoint c.e. and recursively inseparable. Theory extension enlarges
both classes; the identity on term codes gives the forward pair reduction,
and separators pull back in the opposite direction.

This yields an equational completeness statement without introducing a
negation connective. No consistent c.e. lambda theory T is maximal
consistent. Otherwise, for any closed M, search in parallel for a proof
of T⊢M=K and a proof of T+(M=K)⊢K=K_*. Consistency makes the outcomes
exclusive, and maximality ensures that one occurs. This would decide the
K-class, contradicting its inseparability from the K_*-class. Therefore
every consistent c.e. lambda theory has a proper consistent extension;
one can choose an extension obtained by adjoining one equation, so it is
again c.e.

The ambient computational category for this application is classical Rec;
this argument does not construct a new Heller recursion category out of a
lambda theory. K and K_* are the two distinguished classes, not categorical
identity and zero. No such interpretation of those two terms is asserted.

## Sources and limits

- Bernardi, *Precomplete Equivalence Relations in Dominical Categories*,
  Proc. AMS 98 (1986), 124--134,
  [DOI](https://doi.org/10.1090/S0002-9939-1986-0848889-9).
  [Author-uploaded text](https://www.researchgate.net/publication/243062671_Precomplete_Equivalence_Relations_in_Dominical_Categories).
  Relevant locations: pp.125--126 (program example and Definition 1),
  p.128 (Theorem 2). The extracted author text was read; the publisher
  scan was inaccessible. The categorical formula and upward-closure law
  are type-checked above. The stronger dominical theorem is attributed,
  not used as an unverified substitute for the numerical proof.
- Barendregt and Terwijn, *Fixed point theorems for precomplete numberings*,
  [author PDF](https://www.math.ru.nl/~terwijn/publications/fixthm-addition.pdf),
  Section 2, pp.2--3; Section 3, p.4. This supplies the lambda example's
  precompleteness. The inseparability and maximality arguments above are
  reconstructed from that property.
- Simpson, *Subsystems of Second Order Arithmetic*,
  [author PDF](https://sgslogic.net/t20/sosoa/chapter1.pdf), Remark I.3.3,
  printed p.8 (PDF page index 16).
- Kaye and Wong, *On interpretations of arithmetic and set theory*,
  [author PDF](https://cpb-us-w2.wpmucdn.com/blog.nus.edu.sg/dist/4/10956/files/2019/01/finitesettheory-1i2tx5t.pdf),
  Sections 2--4, especially Definition 7 and Theorem 8.
- Avigad and Feferman, *Goedel's Functional (Dialectica) Interpretation*,
  [author PDF](https://www.andrew.cmu.edu/user/avigad/Papers/dialect.pdf),
  Section 2.1, Corollary 2.1.2 and proof, printed p.6.

The existence and interpretation results above are sufficient for the
specified classes. Realizing further classes in nonnumerical recursion
categories remains a separate extension of the theorem's scope, not a
prerequisite to these applications. No new Lean formalization is claimed.
