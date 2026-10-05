#!/usr/bin/env python3
"""Choose the newest mutually compatible pins for EpsilonEridani's direct dependencies.

EpsilonEridani requires mathlib, Physlib and TauCeti (lakefile.toml), and Lake builds all of
them against ONE mathlib and ONE Lean toolchain: the root manifest's. Each dependency also pins
its own mathlib and toolchain, and they move at different speeds. Physlib follows mathlib's
release tags and updates weekly; TauCeti follows mathlib master and updates daily. So "bump
everything to its branch tip" is usually not a set that builds, and "bump mathlib to master"
can leave a dependency compiling against a mathlib it has never seen.

This script picks the set to move to. It reads only upstream metadata through `gh api` and
runs nothing; the bump PR's build is still what decides whether the set really builds.

## The rule

No dependency is special. Every candidate mathlib commit M comes from somewhere concrete:

  * the current pin;
  * mathlib master's newest commit with a successful master-push build (its cache is
    published; the same signal scripts/check-bump.sh step 2b requires);
  * every mathlib commit that a candidate commit of a dependency pins.

M must be a forward move from the current pin (the rule is scripts/bump_moves.py, which
scripts/check-bump.sh calls too): a descendant of it on mathlib's nominated branch
(`descendant`), or, with a strictly newer toolchain, a mathlib `v4.*` release tag (`release`;
`v4.34.1` lives on mathlib's `stable` branch, not on master, and a tag cut after the pin descends
from it while off master, so an off-master descendant qualifies only as a release) or, for a rev
that diverged from the pin, a commit on the nominated branch (`toolchain`; the way back to master
from a patch release). A diverged rev leaves out commits the pin has; they are counted
(`dropped_commits`). The toolchain is always mathlib's own at M.

A new M is only offered once its cache is published, or every downstream build would recompile
mathlib. A master commit needs a successful master-push `build.yml` run (step 2b of
scripts/check-bump.sh); a release tag off master needs a successful `release_cache.yml` run,
which mathlib uses to publish exactly those tags to the same cache (a tag on master gets none from
it: the run skips the build and still succeeds). scripts/mathlib_cache.py answers this for both this
script and check-bump.sh. An M that is otherwise feasible but has no cache yet is blocked by `cache`.

A dependency's candidate commits are its branch tip, the last commit before each change to its
`lean-toolchain` or `lake-manifest.json`, and its current pin: commits after the pin, so a
dependency never moves backward. A candidate FITS M when

  * `exact`: it pins mathlib at M itself (its own CI built exactly this pairing); or
  * `near`:  its toolchain is on M's Lean line (same major.minor) and no newer than M's, and
             its mathlib is an ancestor of M, or has diverged from M and M is a release tag
             on that line. A candidate whose manifest pins no mathlib fits on the toolchain
             line alone.

For each M, each dependency takes its newest fitting candidate. When none fits, it may stay on
its current pin (`carried`) only while M stays on the Lean line main is already on: main builds
that pin now, and a patch release does not change the line. Otherwise M is blocked by that
dependency.

A carried pin is not checked against M: it may already pin a newer toolchain or mathlib than M,
as long as main builds it today.

The chosen set is the feasible one with the newest M (by toolchain, then commit date). The
number of carried dependencies only breaks exact ties, which are rare; ranking it higher would
let one dependency that fits nothing stall mathlib on an older commit. In practice the most conservative dependency ends up
setting mathlib's pace, without the script having to be told which one that is.

## Output

`--json` prints the chosen pins, every pin's fit and lag behind its branch tip, the reasons each
pin is held back, and the ranked feasible sets. `--summary` prints the same as Markdown for a
job summary. Being held back is the normal state of a pin, not an error: an alert belongs to a
feasible set that does not land, not to a set that stays put because nothing newer fits.

## Usage

    resolve_deps.py [--root DIR] [--json | --summary] [--exclude FILE]
    resolve_deps.py --record FILE ...   # also save every upstream answer, for a test fixture
    resolve_deps.py --replay FILE ...   # answer from a saved recording, no network

`--exclude FILE` takes a JSON list of pin sets ({"mathlib": sha, "Physlib": sha, ...}) whose
build already failed inside a dependency, so the next feasible set is offered instead.

## Environment

    GH_TOKEN / GITHUB_TOKEN   authenticates the `gh` CLI (read-only public data)
"""

import argparse
import base64
import json
import sys
from datetime import datetime
from pathlib import Path

import bump_manifest
import bump_moves
import lake_requires
import lean_versions
import mathlib_cache
from lean_versions import parse_toolchain, show_toolchain
from pr_status.core import gh_api

MATHLIB = "mathlib"


# --- upstream facts -----------------------------------------------------------------------------

def gh(path, jq=None, paginate=False):
    """`gh api`, waiting out a rate limit like every other reader here (pr_status.core.gh_api)."""
    return gh_api(path, jq, paginate).strip()


class GitHub:
    """Every upstream fact the resolver uses, each one `gh api` call (memoised per run)."""

    def __init__(self):
        self._memo = {}

    def _once(self, key, fetch):
        if key not in self._memo:
            self._memo[key] = fetch()
        return self._memo[key]

    def tip(self, repo, branch):
        return self._once(("tip", repo, branch), lambda: gh(f"repos/{repo}/commits/{branch}", jq=".sha"))

    def date(self, repo, sha):
        return self._once(("date", repo, sha),
                          lambda: gh(f"repos/{repo}/commits/{sha}", jq=".commit.committer.date"))

    def parent(self, repo, sha):
        return self._once(("parent", repo, sha),
                          lambda: gh(f"repos/{repo}/commits/{sha}", jq=".parents[0].sha"))

    def boundaries(self, repo, branch, base):
        """Commits on `branch`, newest first, that change the toolchain or the manifest and come
        after `base`. The date filter only narrows the listing; `compare` decides."""
        def fetch():
            since = self.date(repo, base)
            dated = {}
            for path in ("lean-toolchain", "lake-manifest.json"):
                out = gh(f"repos/{repo}/commits?sha={branch}&path={path}&since={since}&per_page=100",
                         jq='.[] | .sha + " " + .commit.committer.date', paginate=True)
                for line in out.splitlines():
                    sha, when = line.split()
                    dated[sha] = when
            newest_first = sorted(dated, key=lambda s: dated[s], reverse=True)
            return [s for s in newest_first if self.compare(repo, base, s)[0] == "ahead"]
        return self._once(("boundaries", repo, branch, base), fetch)

    def file(self, repo, sha, path):
        def fetch():
            content = gh(f"repos/{repo}/contents/{path}?ref={sha}", jq=".content")
            return base64.b64decode(content).decode()
        return self._once(("file", repo, sha, path), fetch)

    def compare(self, repo, base, head):
        """[status, ahead_by, behind_by] of head relative to base."""
        def fetch():
            out = gh(f"repos/{repo}/compare/{base}...{head}?per_page=1",
                     jq='[.status, .ahead_by, .behind_by] | @json')
            return json.loads(out)
        return self._once(("compare", repo, base, head), fetch)

    def cached_master_tip(self, repo):
        return self._once(("cached", repo), lambda: mathlib_cache.newest_master_build(gh, repo))

    def cache_published(self, repo, sha, tag):
        """Whether mathlib's cache for `sha` is published (scripts/mathlib_cache.py, which
        check-bump.sh asks too): a successful master-push build, or for a release tag off master,
        a successful release_cache.yml run on it."""
        def on_master():  # the memoised compare, shared with `forward`
            return bump_moves.is_on_branch(self.compare(repo, sha, mathlib_cache.BRANCH)[0])
        return self._once(("cache_published", repo, sha),
                          lambda: mathlib_cache.cache_published(gh, repo, sha, tag, on_master))

    def release_tags(self, repo):
        """{commit sha: tag} for the repository's trusted release tags: the same mapping the guard
        reads (lean_versions.release_tags_by_commit), so both look for a cache under the same tag."""
        return self._once(("tags", repo), lambda: lean_versions.release_tags_by_commit(gh, repo))


class Recorder:
    """Wraps a source and keeps every answer, so a live run can become a test fixture."""

    def __init__(self, inner):
        self.inner, self.answers = inner, {}

    def __getattr__(self, name):
        method = getattr(self.inner, name)

        def call(*args):
            value = method(*args)
            self.answers[json.dumps([name, *args])] = value
            return value
        return call


class Replay:
    """Answers from a recording; a question the recording cannot answer is an error."""

    def __init__(self, answers):
        self.answers = answers

    def __getattr__(self, name):
        def call(*args):
            key = json.dumps([name, *args])
            if key not in self.answers:
                raise RuntimeError(f"recording has no answer for {key}")
            return self.answers[key]
        return call


# --- toolchains -----------------------------------------------------------------------------------

def line_of(tc):
    return tc[:2] if tc else None


def short(sha):
    return (sha or "?")[:7]


def newness(entry):
    """How new a candidate mathlib commit is: its toolchain, then its date. An unrecognised
    toolchain (only possible for the current pin) sorts below every recognised one."""
    return (parse_toolchain(entry["toolchain"]) or (-1, -1, -1, -1), entry["date"])


# --- the project's own configuration --------------------------------------------------------------

def read_project(root):
    """[(name, repo, branch)] for the git requires, plus {name: rev} and the toolchain pinned now."""
    requires = [(r["name"], lake_requires.repo_slug(r["git"]), r.get("rev", "main"))
                for r in lake_requires.parse((root / "lakefile.toml").read_text()) if r.get("git")]
    manifest = json.loads((root / "lake-manifest.json").read_text())
    pins = {name: p["rev"] for name, p in bump_manifest.direct_packages(manifest).items()}
    missing = [name for name, _, _ in requires if name not in pins]
    if missing:
        raise RuntimeError(f"lake-manifest.json has no top-level pin for {missing}")
    if MATHLIB not in pins:
        raise RuntimeError("lakefile.toml does not require mathlib")
    return requires, pins, (root / "lean-toolchain").read_text().strip()


def mathlib_pin_of(manifest_text):
    packages = json.loads(manifest_text).get("packages", [])
    return next((p["rev"] for p in packages if p.get("name") == MATHLIB), None)


# --- the resolution -------------------------------------------------------------------------------

class Resolver:
    def __init__(self, src, requires, pins, toolchain):
        self.src = src
        self.requires = requires
        self.pins = pins
        self.toolchain = toolchain
        mathlib = [(repo, branch) for name, repo, branch in requires if name == MATHLIB]
        if not mathlib:
            raise RuntimeError("lakefile.toml does not require mathlib")
        if parse_toolchain(toolchain) is None:
            raise RuntimeError(f"unrecognised lean-toolchain {toolchain!r}")
        self.mathlib_repo, self.mathlib_branch = mathlib[0]
        if self.mathlib_branch != "master":
            # mathlib publishes its cache only from master pushes (and release tags), which is
            # what cached_master_tip and cache_published ask; another branch would mean two things
            raise RuntimeError(f"mathlib must be required at rev master, not {self.mathlib_branch!r}")
        self.deps = [(name, repo, branch) for name, repo, branch in requires if name != MATHLIB]
        self.tags = src.release_tags(self.mathlib_repo)

    # facts about one commit
    def dep_commit(self, repo, sha):
        return {"rev": sha,
                "toolchain": self.src.file(repo, sha, "lean-toolchain").strip(),
                "mathlib": mathlib_pin_of(self.src.file(repo, sha, "lake-manifest.json"))}

    def mathlib_toolchain(self, sha):
        return self.src.file(self.mathlib_repo, sha, "lean-toolchain").strip()

    def candidates(self, name, repo, branch):
        """A dependency's candidate commits, newest first, ending with its current pin."""
        pin = self.pins[name]
        shas = [self.src.tip(repo, branch)]
        for boundary in self.src.boundaries(repo, branch, pin):
            shas.append(self.src.parent(repo, boundary))
        shas.append(pin)
        seen, out = set(), []
        for sha in shas:
            if sha not in seen:
                seen.add(sha)
                out.append(self.dep_commit(repo, sha))
        return out

    def forward(self, m):
        """Whether pinning mathlib at m moves forward from the current pin, and how."""
        current = self.pins[MATHLIB]
        if m == current:
            return "current"
        order = lean_versions.toolchain_order(self.toolchain, self.mathlib_toolchain(m))
        if order in (None, "older"):
            return None
        status = self.src.compare(self.mathlib_repo, current, m)[0]
        on_branch = bump_moves.is_on_branch(self.src.compare(self.mathlib_repo, m, self.mathlib_branch)[0])
        kind, _ = bump_moves.mathlib_move(status, on_branch, lambda: order, lambda: m in self.tags)
        return kind

    def fit(self, commit, m):
        if commit["mathlib"] == m:
            return "exact"
        tc, tc_m = parse_toolchain(commit["toolchain"]), parse_toolchain(self.mathlib_toolchain(m))
        if tc is None or tc_m is None or line_of(tc) != line_of(tc_m) or tc > tc_m:
            return None
        if commit["mathlib"] is None:
            return "near"
        status = self.src.compare(self.mathlib_repo, commit["mathlib"], m)[0]
        if status in ("ahead", "identical") or (status == "diverged" and m in self.tags):
            return "near"
        return None

    def resolve(self, exclude=()):
        cands = {name: self.candidates(name, repo, branch) for name, repo, branch in self.deps}
        cached = self.src.cached_master_tip(self.mathlib_repo)
        mathlibs = [self.pins[MATHLIB]] + ([cached] if cached else [])
        mathlibs += [c["mathlib"] for name in cands for c in cands[name] if c["mathlib"]]
        mathlibs = list(dict.fromkeys(mathlibs))
        current_line = line_of(parse_toolchain(self.toolchain))

        feasible, blocked = [], []
        for m in mathlibs:
            how = self.forward(m)
            if how is None:
                continue
            tc_m = self.mathlib_toolchain(m)
            dropped = self.src.compare(self.mathlib_repo, self.pins[MATHLIB], m)[2] if how != "current" else 0
            pins = {MATHLIB: {"rev": m, "fit": how, "toolchain": tc_m, "tag": self.tags.get(m),
                              "dropped_commits": dropped}}
            blockers = []
            for name, _, _ in self.deps:
                for index, commit in enumerate(cands[name]):
                    fit = self.fit(commit, m)
                    if fit:
                        pins[name] = dict(commit, fit=fit, index=index)
                        break
                else:
                    if line_of(parse_toolchain(tc_m)) == current_line:
                        pins[name] = dict(cands[name][-1], fit="carried", index=len(cands[name]) - 1)
                    else:
                        newest = cands[name][0]
                        blockers.append({
                            "dependency": name,
                            "reason": (f"no {name} commit since its pin {short(self.pins[name])} is on "
                                       f"Lean {show_toolchain(tc_m)}'s line; its newest "
                                       f"({short(newest['rev'])}) pins Lean {show_toolchain(newest['toolchain'])} "
                                       f"and mathlib {short(newest['mathlib'])}")})
            entry = {"mathlib": m, "toolchain": tc_m, "tag": self.tags.get(m),
                     "date": self.src.date(self.mathlib_repo, m)}
            if not blockers and how != "current" and m != cached \
                    and not self.src.cache_published(self.mathlib_repo, m, self.tags.get(m)):
                blockers.append({"dependency": "cache",
                                 "reason": f"mathlib {short(m)} has no published cache yet"})
            if blockers:
                blocked.append(dict(entry, blockers=blockers))
                continue
            flat = {name: pin["rev"] for name, pin in pins.items()}
            if any(flat == dict(ex) for ex in exclude):
                blocked.append(dict(entry, blockers=[{"dependency": "*", "reason": "excluded: its build failed before"}]))
                continue
            feasible.append(dict(entry, pins=pins))

        def rank(entry):
            carried = sum(1 for p in entry["pins"].values() if p["fit"] == "carried")
            behind = sum(p.get("index", 0) for p in entry["pins"].values())
            return newness(entry) + (-carried, -behind)
        feasible.sort(key=rank, reverse=True)
        if not feasible:
            raise RuntimeError("no feasible pin set, not even the current one; see `blocked`")
        chosen = feasible[0]
        return self.report(chosen, feasible, blocked, cands, cached)

    # what the chosen set leaves behind, and why
    def report(self, chosen, feasible, blocked, cands, cached):
        tips = {MATHLIB: cached or self.pins[MATHLIB]}
        repos = {MATHLIB: self.mathlib_repo}
        branches = {MATHLIB: self.mathlib_branch}
        for name, repo, branch in self.deps:
            tips[name], repos[name], branches[name] = cands[name][0]["rev"], repo, branch

        newer = sorted((b for b in blocked if newness(b) > newness(chosen)), key=newness, reverse=True)
        pins, holds = {}, []
        for name, pin in chosen["pins"].items():
            rev, tip = pin["rev"], tips[name]
            lag = 0 if rev == tip else self.src.compare(repos[name], rev, tip)[1]
            days = 0.0
            if rev != tip:
                delta = (datetime.fromisoformat(self.src.date(repos[name], tip).replace("Z", "+00:00"))
                         - datetime.fromisoformat(self.src.date(repos[name], rev).replace("Z", "+00:00")))
                days = round(delta.total_seconds() / 86400, 1)
            pins[name] = {"rev": rev, "previous": self.pins[name], "branch": branches[name],
                          "tip": tip, "commits_behind_tip": lag, "days_behind_tip": days,
                          "fit": pin["fit"], "toolchain": pin.get("toolchain"),
                          "mathlib": pin.get("mathlib"), "tag": pin.get("tag")}
            if name == MATHLIB:
                pins[name]["dropped_commits"] = pin["dropped_commits"]
            if rev == tip:
                continue
            if name == MATHLIB:
                why = sorted({b["dependency"] for entry in newer for b in entry["blockers"]})
                reasons = [b["reason"] for entry in newer[:1] for b in entry["blockers"]]
                holds.append({"pin": name, "held_by": why,
                              "text": (f"mathlib held at {short(rev)}"
                                       f"{' (' + pin['tag'] + ')' if pin.get('tag') else ''}, "
                                       f"{lag} commits behind its newest cached {branches[name]} commit"
                                       + (f": {'; '.join(reasons)}" if reasons else ""))})
            else:
                # the oldest newer candidate that pins something else: the commit just before a
                # boundary still pins what the held commit does, so it explains nothing
                pinned = (pin.get("toolchain"), pin.get("mathlib"))
                nxt = next((c for c in reversed(cands[name][:pin["index"]])
                            if (c["toolchain"], c["mathlib"]) != pinned), None)
                text = f"{name} held at {short(rev)}, {lag} commits behind {branches[name]}"
                if pin["fit"] == "carried":
                    text += f" and kept on its current pin, which pins Lean {show_toolchain(pin['toolchain'])}"
                if nxt:
                    text += (f"; newer commits pin Lean {show_toolchain(nxt['toolchain'])} and mathlib "
                             f"{short(nxt['mathlib'])}, which do not fit mathlib {short(chosen['mathlib'])}")
                holds.append({"pin": name, "held_by": [MATHLIB], "text": text})

        changed = any(p["rev"] != p["previous"] for p in pins.values()) \
            or chosen["toolchain"] != self.toolchain
        return {
            "changed": changed,
            "toolchain": {"previous": self.toolchain, "chosen": chosen["toolchain"]},
            "pins": pins,
            "holds": holds,
            "feasible": [{"mathlib": f["mathlib"], "toolchain": f["toolchain"], "tag": f["tag"],
                          "pins": {n: p["rev"] for n, p in f["pins"].items()},
                          "fits": {n: p["fit"] for n, p in f["pins"].items()}} for f in feasible],
            "blocked": [{"mathlib": b["mathlib"], "toolchain": b["toolchain"], "tag": b["tag"],
                         "blockers": b["blockers"]} for b in blocked],
        }


# --- presentation ---------------------------------------------------------------------------------

def summary(result):
    tc = result["toolchain"]
    lines = ["## Dependency pins", ""]
    lines.append("A newer compatible set exists." if result["changed"]
                 else "Main is already on the newest compatible set.")
    lines += ["", "| pin | now | chosen | fit | behind its branch tip |", "|---|---|---|---|---|"]
    lines.append(f"| Lean | {show_toolchain(tc['previous'])} | {show_toolchain(tc['chosen'])} | | |")
    for name, p in result["pins"].items():
        tag = f" ({p['tag']})" if p.get("tag") else ""
        behind = "at tip" if p["commits_behind_tip"] == 0 else \
            f"{p['commits_behind_tip']} commits, {p['days_behind_tip']} days"
        lines.append(f"| {name} | {short(p['previous'])} | {short(p['rev'])}{tag} | {p['fit']} | {behind} |")
    ml = result["pins"][MATHLIB]
    if ml["dropped_commits"]:
        tag = f" ({ml['tag']})" if ml.get("tag") else ""
        lines += ["", f"Moving to mathlib {short(ml['rev'])}{tag} leaves out {ml['dropped_commits']} "
                      f"commit(s) that {short(ml['previous'])} has: the two diverged."]
    if result["holds"]:
        lines += ["", "Held back (expected while upstreams move at different speeds; not an error):", ""]
        lines += [f"- {h['text']}" for h in result["holds"]]
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    out = ap.add_mutually_exclusive_group()
    out.add_argument("--json", action="store_true")
    out.add_argument("--summary", action="store_true")
    ap.add_argument("--exclude", type=Path)
    src_group = ap.add_mutually_exclusive_group()
    src_group.add_argument("--record", type=Path)
    src_group.add_argument("--replay", type=Path)
    args = ap.parse_args(argv)

    src = Replay(json.loads(args.replay.read_text())) if args.replay else GitHub()
    if args.record:
        src = Recorder(src)
    exclude = json.loads(args.exclude.read_text()) if args.exclude else []
    try:
        requires, pins, toolchain = read_project(args.root)
        result = Resolver(src, requires, pins, toolchain).resolve(exclude)
    except RuntimeError as exc:
        print(f"resolve_deps: {exc}", file=sys.stderr)
        return 2
    finally:
        if args.record:
            args.record.write_text(json.dumps(src.answers, indent=1, sort_keys=True) + "\n")
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(summary(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
