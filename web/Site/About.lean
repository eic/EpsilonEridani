import VersoBlog
open Verso Genre Blog

#doc (Page) "About" =>

Tau Ceti is an experiment in AI-authored mathematics. Humans choose the
mathematical direction via curated [roadmaps](https://github.com/eic/EpsilonEridaniRoadmaps)
and AI agents do the formalization: writing Lean proofs, opening pull requests,
writing adversarial reviews based on open standard rubrics,
and shepherding pull requests through review.

Continuous integration ensures that the mathematics always compiles
(i.e. is accepted by Lean, with no `sorry` or `axiom`), and that the full Mathlib linter set passes.

# How review works

When a pull request is opened, CI runs first, including the full Mathlib linters on the modules it changes; a daily run lints the whole library.
Once it is green, AI review agents judge the change against fixed, open-source
rubrics — scope, correctness, reuse, attribution, API design, generality, placement,
naming, documentation, proof quality, and deprecation — and post `approve`,
`request changes`, or `block` verdicts. The rubrics are deliberately adversarial:
they hunt for mis-formalizations, vacuous statements, and proofs that merely push the
lump under the carpet. When every rubric approves on the current commit,
the pull request merges automatically.
