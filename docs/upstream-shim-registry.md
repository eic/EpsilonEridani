# Upstream shim registry

`EpsilonEridani/upstream-shims.json` records Tau Ceti source that is temporary pending a
replacement in an upstream library. The replacement may land in any direct dependency: Mathlib,
Physlib (including the PhyslibAlpha and QuantumInfo libraries of the Physlib package) or TauCeti.
It is AI-owned data: a source-only migration PR may update the registry in the same commit as the
Lean files it changes. The checker itself (`scripts/check-expired-upstream-shims.py`) and its CI
wiring under `scripts/` and `.github/` remain human-owned.

Each JSON object has these fields:

- `sources` (required): unique repository-relative `EpsilonEridani/*.lean` paths sharing the same
  upstream triggers.
- `declarations`: fully qualified Lean declaration names to look up in the pinned dependencies.
- `modules`: fully qualified module names (`Mathlib.*`, `Physlib.*`, `PhyslibAlpha.*`,
  `TauCeti.*`, ...) to look up in the pinned dependencies' source trees. A module name is
  `Library.Path`, and the library may be any one a required package provides; `EpsilonEridani.*` is
  rejected. At least one declaration or module is required.
- `note`: durable migration context and attribution. For vendored or ported material, retain the
  upstream project or PR, author, and URL here even if temporary process prose is later removed
  from a module docstring.
- `speculative` (optional, default `false`): the target name or path is only a guess. A match asks
  for an audit but cannot identify a deterministic migration.
- `landing_sentinel` (optional, default `false`): the target signals that an upstream body of work
  landed, but does not claim every declaration in the listed sources has an exact counterpart.

An entry with neither `speculative` nor `landing_sentinel` is exact. Under
`--fail-on-available`, any matching exact declaration or module exits 3 and makes the required
`build` status red. The active Bump or Fix-CI worker must migrate the superseded surface, preserve
or re-home source-only API, update the registry, and return that PR to green. Speculative and
landing-sentinel matches are warnings only.

## What the probe can see

A module target is found by its source file under `.lake/packages/`, in whichever package provides
the library (`PhyslibAlpha.Relativity.Foo` resolves to
`.lake/packages/Physlib/PhyslibAlpha/Relativity/Foo.lean`). That needs no build.

A declaration target is found by `env.contains` in a Lean environment that imports all of Mathlib
(its cache is complete) and every *built* module of the other direct dependencies, read from their
`.olean` outputs. `lake env lean` builds nothing, and a build of EpsilonEridani compiles only the
upstream modules it imports, so a declaration is visible when it lives in Mathlib or in an upstream
module EpsilonEridani already uses. That is where a shim's replacement is expected to land (an
`*Extensions.lean` module imports the Physlib module it extends). For a replacement expected in a
module EpsilonEridani does not import yet, name that module as well: its arrival is itself a
trigger, and a bump that pins it then makes the declaration visible on the next probe once the
module is imported.

## Ratchet

The registry deliberately does not copy each file's declaration list. When checking a PR, CI
loads the registry and source files from that PR's merge base, derives their command-level Lean
declarations, and ratchets inherited probes while that surface remains. Deleting a fully migrated
source discharges the obligation. Moving declarations is also allowed when the new registered
source preserves the inherited probes. Merely deleting probes, or changing an exact entry into an
audit-only sentinel while its inherited surface remains, is rejected.

The prose scan is one-way. A source that calls itself a temporary shim, or says its surface should
be deleted or refactored onto future upstream API (naming Mathlib, Physlib, PhyslibAlpha,
QuantumInfo or TauCeti), must be registered. Removing that process narrative does not remove an
existing registry obligation. Keep the entry and its note synchronized with the source's actual
upstream relationship; attribution in either location is not disposable process prose. Saying that
material is "not yet upstreamed" is not a self-declaration: it marks PhyslibAlpha-eligible
material (see `AGENTS.md`), which becomes an obligation only once an entry names the replacement to
watch for.

## Exit codes

- `0`: registry and environment are valid; no blocking exact replacement was found.
- `2`: malformed metadata, a weakened inherited obligation, or an unavailable inspection
  environment.
- `3`: `--fail-on-available` found at least one exact replacement.

The default command is report-only. Dependency bump PRs probe the full registry in strict mode.
Ordinary feature PRs compare with their merge-base registry and probe only entries they add or
change, so old shim backlog cannot make an unrelated feature PR red.
