# EpsilonEridani

EpsilonEridani is a repository of formal physics with human-directed and human-reviewed roadmaps,
implemented and maintained by AI contributors, subject to adversarial review.

**EpsilonEridani is built on top of the open-source [Tau Ceti](https://github.com/TauCetiProject/TauCeti) project**, extending Tau Ceti's AI-driven formalization and review machinery to phenomenological physics.

Our goal is to formalize as much physics as we can in a collaborative, coherent library,
at the highest quality we can, subject to the constraint that everything is written by AIs. It's an experiment, and could use your help!

We hope that by building EpsilonEridani we can ensure that a significant part of AI formalization work is performed in an open-source, human directed library. EpsilonEridani will be built for reuse and generality. EpsilonEridani is a community resource, licensed under the Apache licence, that everyone can build on top of.

We've long dreamt about formalizing all the "basic material" in physics.
While we're explicitly **not** aiming here at curating and digesting physical knowledge in the way that a human authored library like [Mathlib](https://leanprover-community.github.io/) can,
we hope that we can efficiently build a reusable library at significant scale. With EpsilonEridani built, we'll be closer to the point where computers can genuinely help us explore the physical universe:
* the Lean kernel verifies
* the Lean language and user tactics provide automation in proof construction
* AIs assist with proof exploration
* and Mathlib, EpsilonEridani, and other libraries provide the knowledge necessary so that humans can work at the research frontier.

Humans own the roadmap for EpsilonEridani, which lives in the
[EpsilonEridaniRoadmaps](https://github.com/eic/EpsilonEridaniRoadmaps) repository (mostly in the form of markdown files, together with a
small amount of Lean); changes are made via human-reviewed pull requests there.
Roadmap authors and reviewers can use AI assistance; see the
[contribution guide](https://github.com/eic/EpsilonEridaniRoadmaps/blob/main/CONTRIBUTING.md).

AIs own the code in this repository, initiating pull requests and shepherding them through an
AI-driven review process.

Humans can raise issues against the code, and leave implementation (and review) to AIs.

## The three repositories

- **EpsilonEridani** (this repository) — the AI-authored Lean physics.
- **[EpsilonEridaniRoadmaps](https://github.com/eic/EpsilonEridaniRoadmaps)** — the human-controlled
  roadmaps that direct the work.
- **[EpsilonEridaniReview](https://github.com/eic/EpsilonEridaniReview)** — the review rubrics and
  the machinery that runs review.

## Relationship to Lean Pool

EpsilonEridani and [Lean Pool](https://github.com/Vilin97/lean-pool) are complementary. Lean Pool is
an arXiv/AfP-like archive of independent formalization projects, whether human- or AI-written.
EpsilonEridani is an integrated, AI-built mathematical library whose contents follow human-audited
roadmaps and undergo review for coherence, reuse, and compatibility with Mathlib.

## Review

Review of implementation PRs is entirely driven by AIs. These operate according to a fixed open source rubric. Humans write the rubric, and update it as the project evolves.

When a PR is opened, we first let CI run, including the full Mathlib linter set on the modules the PR changes; a daily run lints the whole library and opens a repair PR if a change broke lint elsewhere. Once CI passes, a review can be run against the rubrics; its verdicts are posted as "block", "changes requested", or "approval".

PR contributors can push further commits, or respond to review comments, in order to solicit updated reviews.

We've built the infrastructure to fire these reviews automatically on each PR (and on a `/review` comment), but it is currently switched off. For now, reviews are run from the command line.

You can also run the same review yourself from the command line, on your own Claude and/or Codex subscription instead of the project's metered API budget, using the `epsiloneridani-review` tool in [EpsilonEridaniReview](https://github.com/eic/EpsilonEridaniReview). With [uv](https://docs.astral.sh/uv/):

```bash
# print the verdicts for PR #42, posting nothing:
uvx --from git+https://github.com/eic/EpsilonEridaniReview epsiloneridani-review 42
# add --post to publish the scoreboard and per-rubric threads, as you:
uvx --from git+https://github.com/eic/EpsilonEridaniReview epsiloneridani-review 42 --post
```

It runs the identical engine and rubrics CI uses, in a clean room that ignores your personal editor configuration so the review stays reproducible. See [REVIEWING.md](https://github.com/eic/EpsilonEridaniReview/blob/main/REVIEWING.md) for prerequisites, flags, and the contest/re-review flow.

The rubrics are **adversarial**, including instructions to find mis-formalizations, vacuous statements, and "pushing around the lump in the carpet". There are rubrics for many different aspects of review — scope, correctness, reuse, attribution, API design, generality, placement, naming, documentation, proof quality, and deprecation; see [the rubrics directory](https://github.com/eic/EpsilonEridaniReview/tree/main/rubrics). We'll update these as we see what is most useful!

We also have prototype systems for "meta review", using human and AI judges to do A/B testing of reviews, so that we can quantitatively evaluate review quality, and how models and rubrics feed into this quality.

## Mathlib dependency

Although EpsilonEridani and [Mathlib](https://leanprover-community.github.io/) differ both in the review mechanisms and in design standards, and while they target different mathematical goals, we envision a strong synergy between the two libraries. We hope to build overlapping communities around both libraries.

EpsilonEridani depends on Mathlib's `master` branch, and always defers to design decisions made in Mathlib.
AIs are encouraged to make PRs to EpsilonEridani that bump the pin to new commits on Mathlib's `master` branch, and fix any resulting problems in EpsilonEridani.

We won't push material upstream from EpsilonEridani to Mathlib. Mathlib contributors are welcome to adopt, curate, and modify material from EpsilonEridani, while preparing PRs to Mathlib. Everything here is [Apache licensed](http://www.apache.org/licenses/).

## What EpsilonEridani is, and is not

> The product of physics is clarity and understanding. Not theorems, by themselves. ... There is no way to run out of ideas in need of clarification. The question of who is the first person to ever set foot on some square meter of land is really secondary. --- Bill Thurston

There are many reasons to work on formalizing physics, and everyone involved in formalization comes with different reasons. Here are some:

1. To enjoy the satisfying feeling of the :tada: emoji when the computer accepts your proof.
2. To build a modern Bourbaki, digesting and curating physical knowledge into a coherent and general form, usable in interactive theorem provers.
3. To collectively learn how to make best use of, and improve, interactive theorem provers, such as the Lean language.
4. To participate in a community of like-minded researchers on a common project.
5. To strengthen trust in the existing mathematical literature, through a combination of audited definitions and theorem statements, and machine verified proofs.
6. To build a reusable and open library of formal physics, that others can freely build on top of.

**EpsilonEridani is focused primarily on the last point: building an open library, at a quality level sufficient that others can reuse and build on top of it, and at a large enough scale that building on top of it allows downstream projects to reach the research frontier across many areas of physics** (though, as we discuss below, points 4 and 5 matter to us too).

EpsilonEridani is not particularly relevant if you're most interested in :tada:, Bourbaki, and learning how to use and improve Lean itself.
Particularly on the Bourbaki front, EpsilonEridani is not trying to improve the state of the art for curation, clarity, and understanding: those are explicitly human activities, and should happen in libraries like Mathlib and other human-curated downstream libraries. This is what Mathlib excels at, and is rightly proud of its achievements. Similarly, it seems unlikely that we'll learn much about using and improving Lean while working on EpsilonEridani besides, hopefully, some scaling problems! EpsilonEridani explicitly sets out to follow Mathlib decisions regarding design and use of language features, because these decisions are hard earned through years of expert usage in formalizing physics. We think it's essential that as this knowledge evolves in Mathlib and other libraries, EpsilonEridani follows and adapts to these lessons.

We do hope that EpsilonEridani will provide a home for many researchers who want to participate in an active and engaging community. It will be a very different process than contributing to libraries like Mathlib. Primarily, the work is to do high level design: learning to write effective and thorough roadmaps, which efficiently lay out the plans to formalize large areas of physics well. We'll need deep mathematical expertise in every subject area, and there's a lot of learning to do about how to write roadmaps that produce the best AI output. We're already getting started on these experiments, and EpsilonEridani is an opportunity to build a *new community* around a new kind of formalization work.

Similarly, we expect that EpsilonEridani will help build trust in the existing informal literature. Of course, AI formalized definitions are, a priori, untrustworthy, and a big part of the success criteria for EpsilonEridani will be in establishing trust from an initially untrustworthy base. We're working on projects to help rapidly audit deep definition chains. Just as in informal physics, trust in results isn't really achieved during initial review. We know that results are true only after they've been integrated into a deeper web of physics: we've proved more theorems on top of the definitions, and connected the theory to other parts of physics. Our hope is that the scale of EpsilonEridani will help us achieve that here, and allow the rapid validation of results *by building the theory downstream as well*.

## Collaboration

It's really important we have a good collaboration model with other repositories. We want to make sure that we build rapidly, so that we provide the foundations for people working on frontier research as quickly as possible. But we don't want to get in the way of frontier research, or detract from those efforts.

This will be an evolving process, and community input is welcome.
To begin with, our plan is to use the "intentions registration" mechanism from [`leanprover-community/intentions`](https://github.com/leanprover-community/intentions),
and the shared public registry of intentions at [`leanprover-community/project-intentions`](https://github.com/leanprover-community/project-intentions).

We already use this mechanism internally so contributors to EpsilonEridani can indicate they are actively working on and preparing pull requests for parts of a EpsilonEridani roadmap. These intentions are then automatically fed to agents using the `./epsiloneridani` worker exemplar from [`eic/EpsilonEridaniWorker`](https://github.com/eic/EpsilonEridaniWorker), instructing them to avoid working on roadmap items claimed by others. We hope that contributors implementing their own workers will also use this mechanism.

We're working now on extending this mechanism to respect recorded intentions at the public `project-intentions` registry. Hopefully in future there will also be a federated system of registrations collected from individual downstream projects that EpsilonEridani can hook into.

(The underlying tooling here was written for earlier projects, but the reusable GitHub Action and the public registry are nice early community benefits from work on EpsilonEridani!)

We do want to make some important clarifications about registered intentions, along two axes: frontier vs foundational physics, and student projects.

There is so much "frontier physics" (roughly, research papers from the last few years, and those still to come) that EpsilonEridani can simply disavow interest here. EpsilonEridani wants to build a foundational library, so if someone registers a credible intention to work on a frontier project, EpsilonEridani can make sure the relevant results are not included in its roadmaps (or removed if they are already there). This isn't to say that people working on these frontier projects shouldn't simultaneously be contributing to EpsilonEridani: we hope they'll direct their AIs to send the foundational material they build to EpsilonEridani, and then announce the "research result" as an independent downstream project. Indeed, we anticipate that many people working on frontier projects may actually submit EpsilonEridani roadmaps for them! On the other hand, for "foundational physics" (roughly, anything you might expect graduate students at a subject-specific conference to be aware of), we don't intend to wait or remove material from roadmaps. It's important that this gets done, and per the discussion above about what EpsilonEridani is and is not, we believe that EpsilonEridani "getting there first" (reaching the minimal bar of "correct, formal, and reusable") does not detract from others curating, digesting, and subsequently incorporating this material into libraries with more ambitious goals.

There's a special bar for student projects. It's really important that students are "left to work in peace" to the extent possible. We hope that for the most part students are now able to work on frontier projects, and the distinction above does most of the work. But if there are students working on formalizing known physics, and it is important to them or their supervisors that no other formalizations exist, we'll try to accommodate. We want to flag for all EpsilonEridani contributors that student projects come first: if there's any indication that roadmaps or contributions make use of partially published or announced work by students, or don't respect the registered intentions of student projects, we'll happily just delete material from roadmaps, pull requests, or the main library to make room for students. Common sense will be required here (a student project "I'm going to do Sobolev spaces" or "differential geometry" obviously isn't going to stop progress at EpsilonEridani), and we invite the wider community to participate in getting this right. We recommend using [leanprover-community/project-intentions](https://leanprover-community/project-intentions) to register projects. We would like to encourage everyone to decide that formalizations at the "reusable only" level that EpsilonEridani aims at are simply not an obstacle to working concurrently on a higher level formalization. But if there are projects where a student would prefer that there are no other formalizations of any kind, we ask that they note this in the intentions registration, or contact us in the Zulip channel for EpsilonEridani, and we'll take appropriate action.

## Financial model
We're aware that training and running powerful AIs come at a significant financial and environmental cost. We're also aware that at present the most capable agents are commercial offerings, and consider the question of bridging industrial and academic practices very seriously.

For the time being, we will run initial CI and reviews for individual contributors and experiments (we don't really have a budget even for this, but will scrape something together), and expect that contributors will cover the costs of generating the code included in their PRs.

It is essential that EpsilonEridani remains an open source project, and however inference for generation or review is paid for, the outputs will always be free (as in both speech and beer), protected by the Apache licence.

We intend to move to a system where review agents' inference costs are covered by the large scale contributors to the library. This may be in the form of donations (in money or tokens) to the umbrella organizations, or by in-kind inference using sufficiently capable in-house models. We anticipate that individual contributions can be reviewed "for free" out of this pool.

Finally, we understand that participating in AI-assisted physics research requires the ability to pay for inference costs, potentially adding a further barrier to entry on top of the existing societal/financial privilege implicit in holding a research position. We're not sure how to respond to this. Possibilities include advocacy for public and private funding, advocacy for capability limitations, and technical capability work on open weight models and cheaper models. Each of these are difficult, have potential adverse effects, and unknown consequences. We hope that everyone involved in EpsilonEridani will think hard about these questions, and contribute to meaningful and beneficial solutions.

## Documentation

Generated API documentation for every declaration in EpsilonEridani, hyperlinked into its Mathlib
dependencies, is published at
[epsiloneridaniproject.github.io/EpsilonEridani/docs](https://epsiloneridaniproject.github.io/EpsilonEridani/docs/). It is
scheduled for regeneration every three hours from `main` with
[`doc-gen4`](https://github.com/leanprover/doc-gen4), alongside the
[project website](https://epsiloneridaniproject.github.io/EpsilonEridani/).

The moving `docgen` branch points at the mainline commit whose generated API documentation is
currently published — not necessarily the newest, since a deployment that serves older
documentation moves the branch back to match it. Every successful deployment from `main` attempts
that correction, in either direction, so the branch heals rather than drifting indefinitely.

It is best-effort rather than exact. Publishing to Pages and updating a git ref cannot be done
atomically, so between the two the branch names documentation that has already been replaced; and
if the update fails, or the deployment came from a manually dispatched run on another branch, the
branch stays wrong — in either direction — until the next deployment from `main`. Anything that
needs certainty should instead read
[`/docs/SOURCE_SHA`](https://epsiloneridaniproject.github.io/EpsilonEridani/docs/SOURCE_SHA), which is published
inside the documentation itself and therefore states, at the moment it is read, exactly which commit
the live documentation describes.

## Building

```bash
lake exe cache get Mathlib Physlib TauCeti                 # Mathlib's oleans
bash scripts/lake-cache-get.sh .   # EpsilonEridani's own oleans
lake build
```

Both fetches matter, and they come from different places. `lake exe cache get Mathlib Physlib TauCeti` is Mathlib's own
cache and covers only Mathlib. EpsilonEridani's oleans live in a separate public cache that
`scripts/lake-cache-get.sh` reads, anonymously and with no setup; without that second line
`lake build` compiles the whole library from source, which takes hours. A miss is never fatal: the
script discards a partial fetch and leaves you exactly where a from-scratch build would.

The cache stores each revision's outputs under the toolchain that built them, and the script looks
back through ancestors of your checkout to find the nearest published one. So expect a full rebuild
right after a `lean-toolchain` bump, when no ancestor has been published under the new toolchain
yet, and expect a hit at other times.

## Roadmaps

The roadmaps live in the [EpsilonEridaniRoadmaps](https://github.com/eic/EpsilonEridaniRoadmaps)
repo: universal covers, the Jacobian challenge, reductive algebraic groups, partial
differential equations, Heegaard Floer and knot Floer homology, and multiquadratic fields and
genus theory. When asked to work here, read the roadmap first (see `AGENTS.md`).

Before starting a substantial piece of roadmap work, register and claim your intention so you
don't collide with others; see [Coordinating work: intentions and claims](https://github.com/eic/EpsilonEridaniRoadmaps#coordinating-work-intentions-and-claims).

## Contributing with the worker CLI

The reviews above can be run one PR at a time, but most contribution here happens through a
*worker*. A single round picks one piece of work, does it, and stops; `--loop` runs rounds
repeatedly until you interrupt it. The exemplar is
[`eic/EpsilonEridaniWorker`](https://github.com/eic/EpsilonEridaniWorker). With
[uv](https://docs.astral.sh/uv/):

```bash
uv tool install git+https://github.com/eic/EpsilonEridaniWorker
gh auth login     # the worker acts as this account, and tends its PRs
epsiloneridani doctor    # checklist of everything it needs
```

`epsiloneridani doctor` is the place to start: it prints a row per prerequisite and tells you what is
missing. You need `gh`, `git`, `uv/uvx`, `jq`, an authenticated `gh`, and `lake`, plus
credentials for whichever agent you run (Codex or Claude). The `bubble`, `incus`, `pi` and
`kiro` rows can stay missing unless you want the sandbox or an alternative agent.

By default, agents run with unrestricted host access; see
[sandboxing with `--bubble`](https://github.com/eic/EpsilonEridaniWorker/blob/main/docs/sandbox.md)
for isolation.

Then survey before you act:

```bash
epsiloneridani status    # read-only: what work is available, and your quota
epsiloneridani work      # ONE unit of work, then exit
epsiloneridani work --loop
```

Run a bare `epsiloneridani work` before ever using `--loop`, so you see one complete round end to end.

Each round prioritizes maintenance and review before new formalization work; see
[the cascade](https://github.com/eic/EpsilonEridaniWorker#what-a-round-does).
`epsiloneridani work --dry-run` shows what a round would pick without acting.

Subscription pacing can be controlled via
[`--pace`](https://github.com/eic/EpsilonEridaniWorker#pacing-against-quota).
For running several workers, see
[the worker documentation](https://github.com/eic/EpsilonEridaniWorker#persistent-workers).

### Only review

If you would rather review than author:

```bash
epsiloneridani work --loop --only review
```

`--skip roadmap` is "everything except opening new formalization PRs" — a good setting if you
want to help existing work land.

### Only one roadmap area

Roadmap rounds pick a random area each time unless you say otherwise. To steer to one:

```bash
epsiloneridani work --roadmap-only ReductiveGroups
```

This keeps maintenance and review enabled. We discourage `--only roadmap`: it skips both,
leaving existing PRs untended while opening new ones.

The area is a subdirectory of the [EpsilonEridaniRoadmaps](https://github.com/eic/EpsilonEridaniRoadmaps)
repo. Conversely `--roadmap-skip AREA[,AREA...]` excludes areas, which is how concurrent workers
divide the roadmap between them. Before starting substantial roadmap work, register your
intention so you do not collide with others — the worker reads the intentions board and avoids
claimed targets by default.

Finally: merging, abandoning and de-duplicating PRs is the repo's CI, not the worker. Your job
ends when a PR is green and reviewed.

---

<p align="center">
  <img src="assets/epsiloneridani-collaboration.jpg" alt="A hexapus reaching out to touch an AI's hand across a tide pool, beneath twin suns and a ringed planet." width="900">
</p>
