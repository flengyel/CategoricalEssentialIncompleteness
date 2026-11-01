from pathlib import Path
import json, csv

ROOT=Path('tmp/scope26')
data=json.loads((ROOT/'inventory.json').read_text())
# These are mathematical interfaces used to assess scope, not a Lean dependency audit.
rows=[
('3.1','Diagonal comparison for a lifted partial conditional','§2 recursion, ranges, coproduct comparison; Turing parameterization','Keep','Central comparison theorem'),
('3.2','Exclude lifted complementary separators','3.1','Keep','Used in arithmetic recursive inseparability and 3.5'),
('3.3','A connected test selects a coproduct summand','§2 connectedness and inverse-image laws','Keep','Preparation for locally connected target theorem'),
('3.4','Construct the unique partial reversed conditional','3.3; splitness and weak choice','Keep','Target construction for 3.5'),
('3.5','Derive source inseparability under section lifting','3.2; 3.4; range-functor operations','Keep','Independent general endpoint, with instance 6.3 retained'),
('3.6','Sufficient source join condition for section lifting','3.4; disjoint arrow joins','Keep','Useful sufficient-condition endpoint; no later proof citation required'),
('4.1','Interpret theorem ranges and infer target consistency from validity','A.6; A.7; unnumbered chosen-splitting extension in §4.1','Keep','Interface from categorical consequence objects to soundness'),
('4.2','Derive source and interpreted incompleteness from semantic consistency','3.1; §4.1 splitting extension and join preservation','Keep','Abstract route to 7.3'),
('4.3','Transfer an inseparable pair into every consistent theorem extension','§2 idempotent order and total inverse images; an inseparable source pair','Keep','Numerical route retained; also exported to companion applications'),
('5.1','PA-provable evaluation, composition and parameterization equations','§5 fixed computation coding and numerical type encodings','Keep','Required computational presentation'),
('5.2','Represent a Sigma1 relation by exact-domain witness search','§5 computation coding; PA least-number search','Keep','Shared search lemma; later uses should cite it'),
('5.3','Predicate equivalence, regularity and monomorphism partial inverses','5.2; §5 syntactic quotient','Keep','Ambient total category for the syntactic realization'),
('5.4','Combine finitely many Sigma1 tests on coded sequences','§5.2 finite sequence coding and PA induction','Keep','Necessary for syntactic carriers and folds'),
('5.5','Syntax initiality with arbitrary parameters in B_T','5.3; 5.4; 5.2; A.1 and K; numerical tree coding','Keep','Universal property uses T-provable graph equality'),
('5.6','List initiality with parameters in B_T','5.3; 5.4; 5.2; A.1 list functor','Keep','Supports free variables and substitution'),
('5.7','Realize free-variable and admissible substitution folds','5.5; 5.6; A.3 and Appendix A constructor equations','Keep','Preserve all variable/quantifier and option-valued distinctions'),
('5.8','Initial finite derivations for arbitrary finite rule data in B_T','5.3; 5.4; 5.2; §A.4 inference functor','Keep','Needed for individual and indexed theory objects'),
('5.9','Realize first-order theories in the total syntactic splitting','5.3; 5.5–5.8; A.6; A.7','Keep','Representation theorem for the main syntactic setting'),
('6.1','Construct the model range functor','5.1; graph quotient and recursive carrier interpretations','Keep','Used by standard and ultrapower code interpretations'),
('6.2','Lift source-complementary conditionals with one program','§5 computation coding; source complementarity; 6.1','Keep as comparison instance','Not a premise of 7.3; may move with D only if this endpoint is dropped'),
('6.3','Apply local-connectedness lifting to S_T in one model','6.1; 6.2; 3.5','Keep as comparison instance','Retains a concrete main-paper use of 3.5 if examples move'),
('6.4','Total model interpretation preserves finite limits and images','5.3; 6.1; §4 splitting extension','Keep','Preservation of regular structure does not imply initiality preservation'),
('6.5','Semantic substitution for the coded syntax','5.7; first-order evaluation in a model','Keep','Soundness induction prerequisite'),
('6.6','Soundness factorization on standard proof codes','5.8; 5.7; 6.5; logical schemes of Appendix A.5','Keep','One model of axioms; no standard-model soundness assumption'),
('6.7','Ultrapower functor preserves the required finite structure','Set-theoretic choice; proper ultrafilter on a nonempty index set','Keep','Separate mathematical extension, not repetition of standard soundness'),
('6.8','Natural comparison between ultrapowered and interpreted codes','5.3; 6.7; 6.4 for image consequences; Los theorem','Keep','Necessary to cover the entire nonstandard interpreted proof object'),
('6.9','Soundness factorization for the full ultrapower proof carrier','6.6; 6.7; 6.8; 6.4; 4.1','Keep','Required for the explicit ultrapower clause of 7.3'),
('7.1','Represent diagonal domains by numeral substitution','5.7; 5.9; fixed diagonal program and finite PA computation proofs','Keep','Common reduction for syntactic and numerical arithmetic'),
('7.2','Construct a partial proof-search lift','5.2; 6.1 interpreted graphs; fixed provability predicate','Keep','Different from the complementary-source switch 6.2'),
('7.3','Internal arithmetic incompleteness and interpreted witnesses','7.1; 7.2; 6.6; 4.1; 4.2; 6.9 only for ultrapower clause','Keep','Main arithmetic endpoint'),
('7.4','Recursive inseparability and essential incompleteness of c.e. PA extensions','3.2; 7.1; usual syntactic consistency; proof enumeration','Keep','Main numerical observation endpoint of the syntactic argument'),
('7.5','Identify numeral fibers of the indexed derivation family','5.3; 5.8; 5.9; A.5; preceding unnumbered family construction','Keep','Explicit slice/algebra comparisons are necessary'),
('7.6','A total uniform assignment of independent sentences','7.5; 5.1; 5.2; 7.1; 6.6; proof-search computation','Keep','Independent main endpoint; does not require ultrapowers or 3.5'),
('7.7','Numerical total and partial equivalences, syntax and derivation realization','§5 numerical algorithms; A.1–A.7; 6.1 and 6.4 for code comparisons','Keep','Extensional category; arbitrary folds require its own proof, unlike B_PA'),
('8.1','Uniform computation of unanimous outputs across representations','§8 representation space, compactness and fixed oracle numbering','Move with Miller','Application prerequisite, not empty setup'),
('8.2','Construct the representation-independent recursion category','8.1; §8 chosen oracle operations','Move with Miller','Changes source computability class'),
('8.3','Reduce the diagonal pair to the cuts of the Miller sequence','8.2; Miller index property; diagonal program','Move with Miller','Required for the field-theory incompleteness endpoint'),
('8.4','Cut inseparability and separation for a fixed representation','8.2; 8.3; 3.5; fixed-representation observations','Move with Miller','Keep both sides of the representation distinction'),
('8.5','Realize first-order syntax and theories in the Miller total category','8.2; A.1; A.3; A.6; numerical coding and uniform folds','Move with Miller','Different ambient category; its fold proof is not removable as repetition'),
('8.6','Essential incompleteness of the associated real closed field theory','8.4; 8.5; 4.3; A.6; A.7; real-field model','Move with Miller','Terminal application, not unused result'),
('9.1','Evaluation functors preserve the structure and endpoint Turing maps','B.7; §9 fork and numerical target constructions','Move with cosheaf','Retain typed evaluation comparisons in companion'),
('9.2','Initial propositional syntax in the fork total category','B.2; §A.6 propositional recipe; §9 atom and constructor data','Move with cosheaf','No decidable equality of universal fork is assumed'),
('9.3','Initial derivation algebra in the fork slice','9.2; B.2; §§A.4 and A.6 inference/propositional constructions','Move with cosheaf','Prove folds and naturality in this category'),
('9.4','Least generated theorem range and componentwise consistency','9.3; A.5; A.7; signed atoms and finite valuations','Move with cosheaf','Supports endpoint incompleteness'),
('9.5','Internal and observed inseparability of theory extensions','9.4; 9.1; 3.5 through §9.1; 4.3; Pair(Rec) definition in §7.6','Move with cosheaf','Pair category is a hidden migration dependency'),
('9.6','Endpoint theories are essentially incomplete','9.5; compatible extension construction','Move with cosheaf','Terminal application, not unused result'),
('A.1','Define parameter-stable categorical syntax and lists','§A.1 hypotheses; displayed K functor','Keep','Foundational definition with explicit ambient category'),
('A.2','Define the sentence subobject by the free-variable pullback','A.1; free-variable folds in §A.2','Keep','Used by all first-order realization claims'),
('A.3','Construct admissible categorical substitution','A.1; decidable variable equality and parameterized folds','Keep','Preserve quantifier branches and admissibility data'),
('A.4','Define deductive closure as an inference-algebra subobject','§A.4 rule functor; regular category and finite coproducts','Keep','General closure definition, independent of incompleteness'),
('A.5','Image of an initial derivation algebra is the least closed subobject','A.4 inference functor; regular factorization','Keep','Central generic consequence-object theorem'),
('A.6','Apply the generic image construction to first-order theories','A.1; A.2; A.3; A.5; seven logical scheme maps','Keep','The appendix applies its own categorical constructions'),
('A.7','Identify regular images with ranges when the mono has a partial inverse','Restriction ranges; regular image; typed partial inverse','Keep','Necessary bridge for main theory objects'),
('B.1','Equivalence between three-point cosheaves and fork diagrams','§9 topology; Set coproduct coequalizers and pushouts','Move with cosheaf','Companion must retain this actual topology comparison'),
('B.2','Regular extensive total fork category and component images','Numerical base regularity reproved in §B.1; componentwise limits; finite probes (can cite 7.7 after consolidation)','Move with cosheaf','Consolidate repeated numerical base proof if kept in same paper'),
('B.3','Partial fork maps, ranges, products and weak choice','B.2; partial-map spans and effective inverse graphs','Move with cosheaf','Retain naturality/domain closure proofs'),
('B.4','Local connectedness of the partial fork category','B.3; explicit finite connected probes','Move with cosheaf','Keep full proof once; main §9.1 may cite it'),
('B.5','Construct the universal fork embedding and partial inverse','§9 explicit universal fork; B.3 morphism class','Move with cosheaf','Necessary for recursion subcategory and splitting equivalence'),
('B.6','Construct product, coproduct and nonempty-word frames','§9 universal fork; recursive tuple/word coding','Move with cosheaf','Word part is a scope choice, not a deletion without changing the category'),
('B.7','Construct the coherent fork Turing morphism','§9 universal fork; ordinary evaluation and parameterization','Move with cosheaf','Retain equality of partial domains, not only values'),
('B.8','Generated recursion category and its restriction splitting','B.3; B.5; B.6; B.7','Move with cosheaf','Defines the nonnumerical recursion category used by §9'),
('B.9','Karoubi envelope has the same partial fork realization','B.8; explicit splitting of general idempotents','Move with cosheaf','Optional narrower completion claim only by explicit scope change'),
('B.10','Distinguish from ordinary recursion and exclude decidable equality on V','B.2; B.8; unnumbered Q_num equivalence in §B.5 (same claim as 7.7); terminal subobjects','Move with cosheaf','Key representation distinction; keep in the companion'),
('C.1','Counterexample when section lifting is omitted','3.5 hypotheses; ordinary/oracle computation and halting set','Keep','Supports sharpness of the advertised lifting hypothesis'),
('D.1','Faithful family of all countable model interpretations','6.1; completeness and downward Lowenheim–Skolem','Move with faithful-family comparison','Not needed for one-model soundness'),
('D.2','Source inseparability and compatibility under ambient theory extension','D.1; 6.2; 3.5; quotient functors and coordinate projections','Move with faithful-family comparison','Retain extension functors with the result; no reflection-of-consistency claim'),
]
annotations={num:dict(mathematical_job=job,semantic_prerequisites=deps,
    proposed_action=action,placement_reason=reason) for num,job,deps,action,reason in rows}
annotations['3.5']['placement_reason']='General comparison theorem used by retained cosheaf and other applications'
annotations['4.3']['placement_reason']='Used by numerical, Miller and retained cosheaf applications'
annotations['7.7']['placement_reason']='Retain structural and first-order claims; separate their statements and combine the strongest numerical foundation arguments once'
for num,ann in annotations.items():
    if num.startswith('9.') or num.startswith('B.'):
        ann['placement_reason']=ann['placement_reason'].replace('companion','main paper')
        ann['placement_reason']=ann['placement_reason'].replace('Key representation distinction; keep in the main paper','Key categorical representation distinction; retain with the construction')
annotations['9.5']['placement_reason']='Retain the common Pair(Rec) and J_rec interfaces'
annotations['B.1']['placement_reason']='Retain the topology comparison supporting the main cosheaf construction'
annotations['B.2']['placement_reason']='Consolidate the repeated numerical base proof with the shared foundation; retain the fork-specific proof'
assert set(annotations)=={r['number'] for r in data['results']}
result_by_label={r['label']:r for r in data['results']}
def refs(labels):
    return '; '.join((result_by_label[x]['number']+' '+x) if x in result_by_label else x for x in labels)
out=[]
for r in data['results']:
    ann=annotations[r['number']]
    ann.pop('proposed_action')
    ann['recommended_action']='Keep'
    ann['consolidation_or_scope_note']='Retain complete proof and interfaces'
    if r['number'].startswith('8.'):
        ann['recommended_action']='Keep complete Miller application'
        ann['consolidation_or_scope_note']='Retain complete Miller application under the author\'s scope instruction'
    if r['number'].startswith('9.') or r['number'].startswith('B.'):
        ann['recommended_action']='Keep complete cosheaf construction'
        ann['consolidation_or_scope_note']='Retain cosheaf construction; consolidate only repeated numerical and structural proofs'
    if r['number'] in ['6.2','6.3','D.1','D.2']:
        ann['recommended_action']='Keep'
        ann['consolidation_or_scope_note']='Optional future relocation only as complete faithful-family package; no selected cut'
        if r['number'] in ['6.2','6.3']:
            ann['placement_reason']='Optional source-complementarity comparison; neither direct arithmetic, uniform independence nor cosheaves needs it'
    if r['number']=='7.7':
        ann['consolidation_or_scope_note']='Separate structural and first-order propositions; retain both; prove shared numerical foundations once'
    incoming=r['incoming_reference_locations']
    locations=sorted(set(x['file']+':'+str(x['line'])+' (§'+x['source_section']+')' for x in incoming))
    out.append({'number':r['number'],'kind':r['kind'],'label':r['label'],
        'page':r['page'],'section':r['section'],'source_file':r['file'],'source_line':r['line'],
        **ann,'literal_result_prerequisites':refs(r['explicit_result_dependencies']),
        'literal_result_consumers':refs(r['incoming_result_references']),
        'all_literal_citation_locations':'; '.join(locations)})
dest=Path('output/scope_audit_v26/result_dependencies_v26.csv')
dest.parent.mkdir(exist_ok=True)
with dest.open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=list(out[0]));writer.writeheader();writer.writerows(out)
(ROOT/'annotated_inventory.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print('Annotated',len(out),'results/definitions.')
print('Recommended main keeps',sum(x['recommended_action'].startswith('Keep') for x in out),'moves',sum(x['recommended_action'].startswith('Move') for x in out))
