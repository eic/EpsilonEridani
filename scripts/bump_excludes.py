#!/usr/bin/env python3
"""Remember the pin sets whose bump build failed inside a dependency, for `resolve_deps.py --exclude`.

docs/dependency-bumps.md: the resolver's fit rules only predict, and the bump PR's build is the arbiter. A
set whose build fails inside a dependency (a Physlib module, not EpsilonEridani/) is not something
EpsilonEridani can adapt, so it should be passed back with `--exclude` and the next feasible set tried.
Without this the daily run re-offered the same failing set, or flipped between two.

The list lives in the rolling bump PR's own body, as a hidden marker the update workflow rewrites on
every refresh: no extra branch or store. Each run, before resolving:

  1. read the excluded sets from the open bump PR's marker;
  2. if that PR's head failed its `build` status and every module Lake reports as failed is outside
     EpsilonEridani, add the head's direct pins (its manifest's non-inherited packages) to the list;
  3. write the list for `resolve_deps.py --exclude` and for the next body.

A closed bump PR (main already on the newest set) takes its list with it; a set offered again after
that costs one more failed build before it is excluded again.

    bump_excludes.py --repo eic/EpsilonEridani --branch bump-mathlib/resolved --out exclude.json
"""

import argparse
import base64
import json
import re
import subprocess
import sys

MARKER = re.compile(r"<!--\s*epsiloneridani-bump-excluded:v1\s*(\[.*?\])\s*-->", re.S)
_FAILED = re.compile(r"✖ \[\d+/\d+\] (?:Building|Running|Compiling) ([A-Za-z_][\w.'«»]*)")
_RUN_ID = re.compile(r"/actions/runs/(\d+)")
OWN = "EpsilonEridani"
BOT = "epsiloneridani-review-bot[bot]"


def gh(*args, raw=False):
    """Run `gh`; stop the run on any failure, naming the command and gh's own error. Reading nothing
    is not the same as reading "no failure": a permission, rate-limit or API error treated as empty
    would silently drop the carried list (the refreshed body would lose it) or skip an exclusion, and
    the daily job would keep re-offering a failing set with no signal. A failed job is the signal."""
    r = subprocess.run(["gh", *args], capture_output=True, text=True)
    if r.returncode != 0:
        detail = (r.stderr or r.stdout or "").strip().splitlines()
        raise SystemExit(f"bump_excludes: `gh {' '.join(args)}` failed ({r.returncode}): "
                         f"{detail[-1] if detail else 'no output'}")
    if raw:
        return r.stdout
    try:
        return json.loads(r.stdout or "null")
    except ValueError as e:
        raise SystemExit(f"bump_excludes: `gh {' '.join(args)}` returned unparseable JSON: {e}") from None


def read_marker(body):
    """The excluded sets recorded in a PR body; [] when there is no (valid) marker."""
    m = MARKER.search(body or "")
    if not m:
        return []
    try:
        sets = json.loads(m.group(1))
    except ValueError:
        return []
    return [s for s in sets if isinstance(s, dict) and s and all(isinstance(v, str) for v in s.values())]


def render_marker(sets):
    return f"<!-- epsiloneridani-bump-excluded:v1 {json.dumps(sets, sort_keys=True)} -->"


def failing_modules(log_text):
    seen = {}
    for m in _FAILED.finditer(log_text or ""):
        seen.setdefault(m.group(1), None)
    return list(seen)


def dependency_only(modules):
    return bool(modules) and not any(m == OWN or m.startswith(OWN + ".") for m in modules)


def direct_pins(manifest_text):
    """{name: rev} of the manifest's direct (non-inherited) git packages: the keys resolve_deps uses."""
    try:
        pkgs = json.loads(manifest_text).get("packages", [])
    except (ValueError, AttributeError):
        return {}
    return {p["name"]: p["rev"] for p in pkgs if isinstance(p, dict) and p.get("inherited") is False
            and isinstance(p.get("name"), str) and isinstance(p.get("rev"), str)}


def add_set(sets, pins):
    if pins and pins not in sets:
        return [*sets, pins], True
    return sets, False


def bump_pr(repo, branch):
    owner = repo.split("/")[0]
    prs = gh("api", f"repos/{repo}/pulls?state=open&head={owner}:{branch}") or []
    return next((p for p in prs if p.get("head", {}).get("repo", {}).get("full_name") == repo
                 and p.get("user", {}).get("login") == BOT), None)


def head_failed_in_dependency(repo, head):
    """The failing modules when `head`'s newest `build` status failed only inside dependencies."""
    statuses = gh("api", f"repos/{repo}/commits/{head}/statuses?per_page=100") or []
    build = next((s for s in statuses if s.get("context") == "build"), None)
    if not build or build.get("state") != "failure":
        return None
    m = _RUN_ID.search(build.get("target_url") or "")
    log = gh("run", "view", m.group(1), "--repo", repo, "--log-failed", raw=True) if m else None
    mods = failing_modules(log or "")
    return mods if dependency_only(mods) else None


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", required=True)
    ap.add_argument("--branch", required=True)
    ap.add_argument("--out", required=True, help="the excluded sets, as JSON, for resolve_deps --exclude")
    a = ap.parse_args(argv)
    pr = bump_pr(a.repo, a.branch)
    sets, note = [], "no open bump PR: nothing excluded"
    if pr:
        sets = read_marker(pr.get("body"))
        note = f"bump PR #{pr['number']}: {len(sets)} excluded set(s) carried"
        head = pr["head"]["sha"]
        mods = head_failed_in_dependency(a.repo, head)
        if mods:
            manifest = gh("api", f"repos/{a.repo}/contents/lake-manifest.json?ref={head}")
            pins = direct_pins(base64.b64decode(manifest["content"]).decode()) if manifest else {}
            sets, added = add_set(sets, pins)
            if added:
                note += (f"; added {', '.join(f'{k} {v[:7]}' for k, v in sorted(pins.items()))}, whose build "
                         f"failed only inside dependencies ({', '.join(mods[:3])}{', …' if len(mods) > 3 else ''})")
    with open(a.out, "w") as f:
        json.dump(sets, f, indent=1, sort_keys=True)
    print(note)
    return 0


if __name__ == "__main__":
    sys.exit(main())
