import VersoBlog
open Verso Genre Blog

#doc (Page) "About" =>

{leanExampleProject aboutExamples "examples"}

EpsilonEridani is an experiment in AI-authored formal physics, built on the open-source
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) project. Humans choose the
direction via curated [roadmaps](https://github.com/eic/EpsilonEridaniRoadmaps)
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

# Dependencies

EpsilonEridani builds on three libraries: Mathlib, Physlib, and Tau Ceti. Lean compiles
EpsilonEridani, Physlib, and Tau Ceti against one shared Mathlib and toolchain, but Physlib and
Tau Ceti each follow Mathlib at their own pace:
Physlib follows Mathlib's releases, while Tau Ceti tracks Mathlib's development branch daily.
Dependency bumps therefore move to the newest set of commits that fit together, not to the
newest commit of each library. Mathlib can stay on one release for weeks while the slowest
library catches up, and that is expected. Like any other change, a bump merges only once CI
builds the whole library on the new pins.

# Asymptotic freedom

The theorem below is elaborated against the EpsilonEridani library when this site is
built — extracted directly from a project that imports the library, so it cannot
drift out of date. The one-loop QCD β-function coefficient is positive, so the strong
coupling weakens at high energy, for fewer than 16.5 quark flavours:

{leanCommand aboutExamples asymptotic_freedom}
