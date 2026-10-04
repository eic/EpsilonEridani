# Dependency bumps

EpsilonEridani requires three libraries (`lakefile.toml`): **mathlib**, **Physlib** and
**TauCeti**. Lake builds all of them against one mathlib and one Lean toolchain, the ones
pinned in this repository's `lake-manifest.json` and `lean-toolchain`. Each dependency also
pins its own mathlib and toolchain, and the three move at different speeds:

| library | follows | updates |
|---|---|---|
| mathlib | `master` (and release tags on `stable`) | continuously |
| Physlib | mathlib **release tags** (`inputRev` is the latest tag) | weekly, with `lean-update` |
| TauCeti | mathlib **master** | daily |

So the newest commit of everything is usually not a set that builds together, and the
mathlib pin can stay put for weeks while a slower dependency catches up. That is normal.
The job of a bump is to move to the **newest mutually compatible** set, and the job of its
reporting is to tell "nothing newer fits" (fine) apart from "something newer fits and is
not landing" (stuck).

## Choosing the set: `scripts/resolve_deps.py`

The resolver reads upstream metadata through `gh api` and runs nothing. No dependency is
special; whichever is most conservative ends up setting the pace.

**Candidate mathlib commits** are the current pin, mathlib master's newest commit with a
published cache, and every mathlib commit that a candidate commit of a dependency pins. A
candidate must move forward: a descendant of the current pin, or, with a strictly newer
toolchain, a mathlib release tag (patch releases such as `v4.34.1` live on mathlib's `stable`
branch, not on master) or a commit on master (the way back from a patch release). Those two
may diverge from the pin and leave out commits it has; on 2026-10-03 the move to `v4.34.1`
left out one. The report counts them (`dropped_commits`) and the summary says so.
`check-bump.sh` accepts exactly these moves (see below).

A new candidate is only offered once mathlib's **cache is published** for it: a successful
master-push `build.yml` run (as `check-bump.sh` step 2b requires), or, for a release tag off
master, a successful `release_cache.yml` run, which mathlib uses to publish patch releases to
the same cache. A tag on master gets no cache from that run (its `gate` job skips the build but the
run still succeeds), so only the master-push build counts for it. `scripts/mathlib_cache.py` holds
this question for both the resolver and `check-bump.sh`. Without one, the candidate is blocked by
`cache` and the next one is offered. The toolchain is always mathlib's own at the chosen commit.

**Candidate dependency commits** are the branch tip, the last commit before each change to
the dependency's `lean-toolchain` or `lake-manifest.json`, and the current pin. All are at or
after the pin: a dependency never moves backward.

A dependency commit **fits** a mathlib commit M when

- `exact`: it pins mathlib at M itself, so its own CI built that pairing; or
- `near`: its toolchain is on M's Lean line (same major.minor) and no newer than M's, and
  its mathlib is an ancestor of M, or has diverged from M and M is a release tag on that
  line. The release-tag case is the weakest: a dependency built on master after the release
  branched may use API the tag lacks, and only the build will tell. A dependency commit whose
  manifest pins no mathlib fits on the toolchain line alone.

For each M every dependency takes its newest fitting commit. A dependency with none may stay
on its current pin (`carried`) only while M stays on the Lean line main is already on: main
builds that pin today. A carried pin is not checked against M; it may already pin a newer
toolchain or mathlib. Otherwise M is **blocked** by that dependency. The chosen set is the
feasible one with the newest M (toolchain, then date). Carried pins only break exact ties:
ranking them higher would let one dependency that fits nothing stall mathlib on an older
commit.

These rules only predict. The bump PR's build is the arbiter. A set whose build fails inside
a dependency (not something EpsilonEridani can fix) is meant to be passed back with
`--exclude` so the next feasible set is tried; today only the flag exists, and the worker
`bump` stage and `update.yml` job that would use it are in the Status table below.

### Example: 2026-10-03

| pin | main | chosen | fit |
|---|---|---|---|
| Lean | v4.34.0 | v4.34.1 | |
| mathlib | `db1c574` | `d13f23b` (`v4.34.1`) | release |
| Physlib | `35d1bb4` | `d86d07d` (tip) | exact |
| TauCeti | `a1fff14` | `a1fff14` | carried |

Mathlib master was already on Lean v4.35.0-rc3, and no Physlib commit was on that line, so
Physlib held mathlib at its `v4.34.1` tag. TauCeti's pin `a1fff14` already pins v4.35.0-rc3
and its newer commits move further along that line, so none fits; it stays on the pin main
builds today. This run is the regression fixture
`scripts/resolve_deps_fixtures/2026-10-03.json`.

### Running it

    python3 scripts/resolve_deps.py              # Markdown summary of the chosen set
    python3 scripts/resolve_deps.py --json       # pins, fits, lags, holds, all candidate sets
    python3 scripts/resolve_deps.py --record f.json   # also save upstream answers as a fixture

It needs Python 3.11+ (`tomllib`) and an authenticated `gh`.

## Validating a bump: `scripts/check-bump.sh`

The resolver only proposes. What lets a bump PR build and merge without a human is the bump
guard, which reads the PR's `lake-manifest.json` and `lean-toolchain`, queries the upstreams
through `gh api`, and runs nothing from the PR. It accepts a pin change only when:

1. `lakefile.toml` is unchanged and declares mathlib as its last `require` (the premise of
   rule 3: Lake takes the pins of the last require); the direct dependencies are base's
   non-inherited packages, each keeping its url and nominated branch (`inputRev`).
2. Each direct dependency's rev stays put or moves forward: a descendant on its nominated
   branch. Mathlib alone may also diverge onto a strictly newer toolchain, at a release tag
   (only `v4.*` tags: they are release-manager-only and immutable upstream) or on master. A new
   mathlib rev must have a published cache: a master-push build, or for a tag off master a
   `release_cache.yml` run.
3. Every other entry is derived from the direct dependencies' own manifests at their new revs
   (`scripts/bump_manifest.py`): the package set is their union, and a package several of them
   pin is the entry of the one `lakefile.toml` requires **last**, because Lake takes the pins of
   the last require that pins a package. The lakefile requires Physlib, TauCeti, mathlib, so a
   package mathlib pins is mathlib's (its cache was built against it) and one only Physlib and
   TauCeti pin is TauCeti's. The rule is established by the real `lake update` outputs before and
   after commit 2a2b8dc moved mathlib to the bottom (see
   `scripts/bump_manifest_fixtures/mathlib_first/README.md`), and the guard reads the order from
   base's lakefile rather than assuming it (and requires mathlib to be last).
4. `lean-toolchain` moves forward and equals mathlib's at its new rev.

Moving Physlib or TauCeti forward on its branch can therefore merge without a human, as
moving mathlib forward on master always could. That extends the trust the project already
places in those branches (main builds them today) to their future commits; every build still
runs sandboxed. `scripts/test_check_bump.py` runs the guard end to end against a fake `gh`.

## Reporting: held back is not stuck

The resolver reports, for every pin, how far it is behind its branch tip and what holds it
there (for mathlib: which dependencies block the newer candidates). Those **holds** are
expected and are reported informationally, never as stuck automation. Alerts are meant for:

- a feasible newer set that has not landed on main within a few days;
- a bump PR whose build stays red on EpsilonEridani's own code;
- every feasible set failing inside a dependency's build (upstream blocked, low priority);
- a dependency held far behind its tip for a long time (upstream lag, low priority);
- the bump job itself failing or not running.

## Status

| step | state |
|---|---|
| resolver (`scripts/resolve_deps.py`) and its tests | done |
| bump-guard (`scripts/check-bump.sh`, `scripts/bump_manifest.py`) accepts each direct dependency moving forward, mathlib's newer-toolchain release tags and master commits (cache signal for a tag: `release_cache.yml`), and the inherited packages Lake derives from all three | done |
| `update.yml` runs the resolver (dry run first), opens one rolling `bump-mathlib/` PR, records failed sets | planned |
| `scripts/pr_status/stuck_alerts.py`: `stale-pin` replaced by "a feasible set is not landing"; holds reported as information | planned |
| EpsilonEridaniWorker's `bump` stage hands back a PR whose build fails inside a dependency | planned |
