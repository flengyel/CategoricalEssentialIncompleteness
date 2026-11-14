# Lemma 6.1 composition: v58 Lean impact audit

The existing Lean proof establishes the displayed uniform PA composition identity for the same evaluator. The v58 proof rewrite does not require a new Lean proof of the unchanged lemma statement. Lean uses a different, proved implementation of the existentially chosen composition builder; it does not formalize the new paragraph's literal equation between the selected `comp` and `s`, or its two named primitive-recursive trace transformations.

Pinned source: `flengyel/CategoricalEssentialIncompleteness` at `df66b19853e6b243170725619bfabb71f4741065`. The current correspondence row is `FORMALIZATION_STATUS_V58.md`, Lemma 6.1, label `lem:arithmetized-evaluation`. This audit read that remote row, the actual producer and Checks modules, and the relevant definitions below. It did not rerun Lean or recompute the transitive axiom audit. The inspected source files are retrievable at the pinned commit under `Lean/CategoricalEssentialIncompleteness/`.

## Exact result and check

All names in this section are in `CategoricalEssentialIncompleteness.V46.UniformTrace` unless otherwise stated.

`V46UniformTraceBuilders.lean:200` defines the closed arithmetic sentence

```lean
def compositionSentence : ArithmeticSentence :=
  let C := compositionGraph
  let G := graph
  “∀ f e p x z, !C.val p f e →
    (!G.val p x z ↔ ∃ y, !G.val e x y ∧ !G.val f y z)”
```

At line 205, `composition_PA : 𝗣𝗔 ⊢ compositionSentence` is proved using first-order completeness. Its model argument takes **arbitrary** `f e p x z : M`, for every `M` with `[ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]`. It rewrites the proved builder graph `compositionGraph` to `p = compose f e`, then applies `compose_eval` (line 171):

```lean
theorem compose_eval (f e input output : M) :
  graph.val.Evalb ![compose f e, input, output] ↔
    ∃ middle : M, graph.val.Evalb ![e, input, middle] ∧
      graph.val.Evalb ![f, middle, output]
```

`compositionGraph_eval` (line 125) proves that the graph used in the sentence is exactly the function `compose`. `builders_totality_PA` (line 223) proves unique totality of this graph, universally in `f,e`. Thus the premise using `C` is the ordinary graph expansion of the manuscript's primitive-recursive function abbreviation, not an extra hypothesis about programs.

`V46UniformTraceBuildersChecks.lean` checks both the all-model equation and the PA theorem. `V46UniformTraceArithmeticChecks.lean:28` independently contains the exact check:

```lean
example : 𝗣𝗔 ⊢ compositionSentence := composition_PA
```

`V46UniformTraceArithmetic.lean:23`, theorem `arithmetized_evaluation`, packages this theorem together with native primitive recursion of `compose` and `specialize`, PA unique totality of their graphs, functionality, universal evaluation, trace comparison and fixed-standard-index specializer sections. `CurrentStatementAudit.lean` imports `V46UniformTraceBuildersChecks` at line 571 and `V46UniformTraceArithmeticChecks` at line 599. `CurrentAxiomAudit.lean` imports the producer modules, including Arithmetic, Builders, Composition, PrimitiveBuilders and Templates.

## Same evaluator and actual construction

| Layer | Actual definition or theorem | Consequence |
| --- | --- | --- |
| Evaluator | `V46UniformTrace.lean:26`: `graph := canonicalPartrecGraphFormula` | Every occurrence of `G` in `compositionSentence` is this same three-place graph. |
| Literal trace presentation | `V46UniformTraceCoding.lean:33`, `traceFormula`, records the least successful stage and its output; `out t := π₂ t`. `graph_iff_trace` and `trace_comparison_PA` identify this trace presentation with `graph` for all internal `e,x,y`. | The result is about the manuscript's trace-defined graph as represented in this implementation, not a second unrelated evaluation relation. |
| Primitive trace check | `V46UniformTraceProgram` proves `traceProgram_eval_one`, `graph_iff_program_trace`, `traceProgram_comparison_PA`, `primitive_trace_graph_PA`, and the check program's PA totality. `V46UniformTracePrimitiveCoding` proves `traceCheck_primrec`, `trace_primrec`, `traceCheck_natPrimrec`. | The trace predicate and native primitive-recursive implementation have a proved all-model graph comparison. Native primitive recursion alone is not being used to infer PA correctness. |
| Closed composition template | `V46UniformTraceBuilders.lean:34` defines `compositionTemplateGraph` by a relational composite of two occurrences of `graph`; `compositionTemplateIndex := SyntacticSearch.searchIndex compositionTemplateGraph` at line 91. | The closed template index is chosen once, before all model-valued `f,e,x`. |
| Genuine parameter compiler | `V46UniformTraceTemplates.lean:80`: `templateIndex v a := compIndex (v : M) (pairIndex (constantIndex a) identityIndex)`. `templateIndex_graph` proves its parameter equation for fixed standard `v : ℕ` and arbitrary internal `a,input,output : M`. | The dynamically supplied component indices are data, not secretly required to be standard. |
| Composition builder | `V46UniformTraceBuilders.lean:102`: `compose f e := templateIndex compositionTemplateIndex ⟪f,e⟫`. | This gives the same uniform conclusion as the new paragraph, by a selected functional-search template and a proved parameter compiler. |
| Native primitive recursion | `V46UniformTracePrimitiveBuilders.lean:24`, `compose_primrec`, and line 31, `compose_natPrimrec`, derive the certificate from `templateIndex_primrec` and native pairing. | The lemma's primitive-recursive builder claim is proved, despite the model-level definitions being declared `noncomputable`. |

The intermediate functional-search theorem is `V46.SyntacticSearch.search_uniform_of_functional`. It takes a proof of functionality of the supplied graph. For the composition template this input is **discharged** by `compositionTemplateGraph_functional`, using the already proved functionality of `graph`; it is not a caller-supplied assumption in `composition_PA` or `arithmetized_evaluation`.

## Assumptions, uniformity and encodings

The model lemmas assume only a model of PA in the ordered-ring language. Local `IΣ₁`, `IOpen`, or `PA⁻` instances are obtained by subtheory from PA. There is no consistency, soundness-in-ℕ, standardness of `f,e`, extra evaluator-correctness field, or arbitrary-index persistence premise in the composition theorem. Its final type is a closed PA proof, not merely a theorem about partial functions on external natural numbers.

Fixed-standard-index persistence is used inside `templateIndex_graph` only at the closed template `v : ℕ`. The actual dynamic raw-composition theorem, `composition_stage_iff`, works with arbitrary internal component indices at one common stage. In the reverse direction, `templateIndex_graph` raises fuel for the fixed template and constructs the constant/pair/composition stages. It does not promote the fixed-index persistence theorem to an arbitrary internal program index.

There are two pairings. The template and program syntax use the internal canonical pairing `⟪a,b⟫` with `pairDef` and `π₁,π₂`; the public specialization and universal-evaluation equations use `ExponentialPairing.code a b = 2^a(2b+1)-1`, through the separate PA graph of that pairing. `specializationTemplateGraph` explicitly converts the public exponential input into the fixed-template setting. The trace itself is the canonical pair of first-success stage and output. The manuscript's object product coding and these implementation pairings should therefore not be identified as literal equal definitions.

`compose_production_PA (f e : ℕ)` in `V46UniformTraceComparison.lean:75` is a separate comparison with the older production `canonicalPartrecCompIndex`. That theorem fixes external component indices but compares graphs uniformly over every model-valued input/output. It is **not** the basis for the stronger all-internal-indices claim: `compose_eval` and `composition_PA` already prove that claim directly. Reading only `compose_production_PA` would understate the formal result.

## Impact decision

**No Lean theorem or proof update is needed for Lemma 6.1's unchanged statement.** The existing producer and Checks establish its required same-evaluator uniform PA identity and primitive-recursive builder. This is an existing equivalent proof with different choices of program indices and parameter coding.

The new proof paragraph should not be described as literally replayed by Lean. No inspected declaration proves the specific syntactic equality

```text
compose(f,e) = specialize(c, ExponentialPairing.code(f,e))
```

for the already selected `compose` and `specialize`, and no inspected declaration defines the paragraph's two primitive-recursive trace-combining/extracting functions. Those are details of the manuscript's alternate proof, not additional conclusions in the lemma statement. If exact proof-implementation correspondence is required, document the alternate template construction or add those extra comparisons; the existing proved status of the lemma does not depend on doing so.

No manuscript, Lean producer, Checks, manifest, or correspondence file was edited in this audit.
