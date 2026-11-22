# Palomar verification of PALOMAR-2026-11-22-000009, version 2

Palomar registered Florian Lengyel’s *Logical consequence and essential incompleteness in recursion categories* from commit `cd08f0a42a6e8e182805db84396e40fdddc1b2ca`. [Version 2](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-22-000009&version=2) · [Registry record](https://data.palomar-registry.org/entries/PALOMAR-2026-11-22-000009-v2.json)

| Check | Result | Evidence |
| --- | --- | --- |
| Full repository preflight | Pass | [Run 45013292400](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/45013292400) · [Report](preflight-report.json) |
| Palomar mechanical verification | Pass | [Run 45016908510](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45016908510) · [Report](mechanical-report.json) |
| Challenge rendering | Pass | [Run 45018230569](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/45018230569) |

The public record gives SHA-256 `6a676cd08c3ae5a2bba6653e82f395ca98dde6dd1e7929b5694ab82d910a33ea` for the mechanical verification report. Both reports identify project `Lean`, configuration `Lean/comparator.json` and metadata `Lean/formalization.yaml`.

Comparator checked `CEIPalomar.essential_incomplete_iff_inseparable`, `CEIPalomar.boolean_assignment`, `CEIPalomar.exists_inseparable_example` and the definition `CEIPalomar.IsNullaryCalculus`. The existence theorem quantifies over the calculus and the pair of subobjects. Its proof uses the PA diagonal pair. [Lean solution](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/cd08f0a42a6e8e182805db84396e40fdddc1b2ca/Lean/CEIPalomar/Solution.lean)
