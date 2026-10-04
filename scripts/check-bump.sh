#!/usr/bin/env bash
# check-bump.sh — validate that a PR's proposed Lake-pin / toolchain change is a
# safe, machine-checkable *forward* bump, and nothing else.
#
# This is the trust anchor that lets a PR touching `lake-manifest.json` and/or
# `lean-toolchain` be built and auto-merged without a human.
# the worry is a PR that re-points a dependency at a malicious fork/commit or a
# malicious toolchain and then gets auto-built. We reduce the whole manifest to a
# deterministic function of validated facts — "each direct dependency stayed put or
# moved forward on the branch it nominates" — and require the toolchain to move
# forward and match mathlib's:
#
#   1. lakefile.toml / lakefile.lean are byte-identical to base.
#   2. The direct dependencies are the packages base's manifest does not mark
#      `inherited` (mathlib, Physlib, TauCeti); mathlib must be one of them. Each is
#      the ONLY package of its name in the PR manifest, a `git` package pinned to a
#      40-hex commit SHA, and keeps base's url and inputRev (its nominated branch).
#      A rev that changed must move forward (via the GitHub compare API; the SHA
#      requirement makes the compared revs immutable, so what we validate is exactly
#      what Lake will resolve and build):
#        * any direct dependency: the new rev is a *descendant of the old rev* AND
#          *on the nominated branch's history*;
#        * mathlib only, when the new rev diverged from the old one: mathlib's
#          toolchain at the new rev is strictly newer than base's lean-toolchain, AND
#          the new rev is either a mathlib release tag `vX.Y.Z[-rcN]` (patch releases
#          live on mathlib's `stable` branch; `v4.*` tags are restricted to release
#          managers and immutable by mathlib's tag ruleset) or on the nominated branch
#          (the way back to master from a patch release).
#      2b. A new mathlib rev is one whose oleans are in the cache: a successful
#      master-push build on it, or for a release tag, a successful release_cache.yml
#      run on that tag. scripts/resolve_deps.py offers exactly these moves.
#   3. Everything else in the PR manifest is DERIVED from the direct dependencies'
#      own manifests at their new revs, comparing WHOLE entries (only `inherited` may
#      differ, and must be true): the package set is exactly their union, a package
#      mathlib pins is mathlib's entry, and one only another dependency pins is that
#      dependency's — no package added, removed, renamed, retyped (e.g. a `path`
#      dep), duplicated, re-pointed, or re-configured (`subDir`, `configFile`,
#      `manifestFile`, `scope`) independently of them. Each direct entry differs from
#      base only in `rev`, and every top-level field (`packagesDir`, `lakeDir`, ...)
#      equals base. See scripts/bump_manifest.py.
#   4. lean-toolchain moves monotonically forward on the leanprover/lean4 channel
#      AND equals mathlib's lean-toolchain at the new rev.
#
# It does NO build and runs NONE of the PR's code — only reads/parses text files and
# queries the trusted upstreams via `gh api`. Usage:
#
#   check-bump.sh <base_dir> <merge_base_dir> <pr_dir>
#
# where each dir holds the repo's lean-toolchain, lake-manifest.json, lakefile.toml
# (and optionally lakefile.lean). base_dir is the CURRENT target-branch tip — the
# trusted forward-progress policy anchor a genuine bump is validated against. The exact-head
# build uses the candidate config after separately attesting its lakefile to the merge base.
# merge_base_dir is the PR's merge-base with the target branch, used
# only to decide whether the PR changed these files at all (so a PR that is merely
# behind the tip is not judged as if it had edited them). Exit 0 = safe forward bump
# (or no pin change); exit 1 = not auto-mergeable (route to a human). Reasons printed.
set -uo pipefail

BASE="${1:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"
MERGE_BASE="${2:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"
PR="${3:?usage: check-bump.sh <base_dir> <merge_base_dir> <pr_dir>}"

fail() { echo "::error::bump-guard: $*"; echo "BUMP-GUARD: FAIL — $*"; exit 1; }
ok()   { echo "BUMP-GUARD: PASS — $*"; exit 0; }

# --- 0. is this a pin change at all? (the PR's OWN delta, vs its merge-base) ---
# Validate only what the PR itself changes in the human-owned lakefile and the Lake
# pins. If none of these differ from the merge-base, the PR did not touch them — it is
# not a bump (it may merely be behind the target tip, which has moved them forward
# underneath it), so pass trivially. Only when the PR's own delta touches one of them
# do we judge it, strictly, against the CURRENT base config (steps 1–4 below). This is
# the one fact that needs the merge-base; everything below is relative to BASE (tip).
pin_changed=0
for f in lakefile.toml lakefile.lean lake-manifest.json lean-toolchain; do
  m="$MERGE_BASE/$f"; p="$PR/$f"
  [ -f "$m" ] || m=/dev/null
  [ -f "$p" ] || p=/dev/null
  if ! diff -q "$m" "$p" >/dev/null 2>&1; then pin_changed=1; break; fi
done
[ "$pin_changed" = 0 ] && ok "no lakefile or Lake-pin change relative to the merge-base"

# --- 1. lakefiles are human-owned and never part of an automated bump --------
for f in lakefile.toml lakefile.lean; do
  b="$BASE/$f"; p="$PR/$f"
  # Treat an absent file the same on both sides; a file appearing/vanishing is a change.
  [ -f "$b" ] || b=/dev/null
  [ -f "$p" ] || p=/dev/null
  if ! diff -q "$b" "$p" >/dev/null 2>&1; then
    fail "$f differs from base — lakefile edits are human-owned and never auto-merge"
  fi
done

# --- helpers ------------------------------------------------------------------
# owner/repo slug from a github url
slug() { sed -E 's#^https?://github.com/##; s#/$##; s#\.git$##' <<<"$1"; }

TC_B="$(tr -d '[:space:]' <"$BASE/lean-toolchain" 2>/dev/null)"
TC_P="$(tr -d '[:space:]' <"$PR/lean-toolchain" 2>/dev/null)"
[ -n "$TC_B" ] || fail "cannot read base lean-toolchain"
[ -n "$TC_P" ] || fail "cannot read PR lean-toolchain"

# Exit 0 when toolchain $2 is a strictly newer leanprover/lean4 release than $1; print why not.
# The order is lean_versions.py's, the one resolve_deps.py proposes moves by.
toolchain_newer() { python3 "$(dirname "$0")/lean_versions.py" newer "$1" "$2"; }

# Print one line per direct dependency (a package base's manifest does not mark
# `inherited`): "name<TAB>url<TAB>base rev<TAB>PR rev<TAB>inputRev<TAB>manifest path", after
# asserting: no duplicate names in either manifest, mathlib among them, and each one exactly
# once in the PR, of type git, with a 40-hex commit-SHA rev, base's url and base's inputRev.
# Url, inputRev and manifest path are base's, the trusted side. Any violation prints
# "ERROR: ..." and exits 1 (so the caller can `|| fail`).
direct_deps() {
  python3 - "$1" "$2" <<'PY'
import json,sys,re
def load(path, which):
    try:
        m=json.load(open(path))
    except Exception as e:
        print(f"ERROR: cannot parse {which} manifest: {e}"); sys.exit(1)
    pkgs=m.get("packages") if isinstance(m, dict) else None
    if not isinstance(pkgs, list) or not all(isinstance(p, dict) for p in pkgs):
        print(f"ERROR: {which} manifest has no list of package objects"); sys.exit(1)
    names=[p.get("name") for p in pkgs]
    dups=sorted({str(n) for n in names if names.count(n)>1})
    if dups: print(f"ERROR: duplicate package names in {which} manifest: {dups}"); sys.exit(1)
    return {p.get("name"): p for p in pkgs}
def norm(url): return (url or "").rstrip("/").removesuffix(".git")
base, pr = load(sys.argv[1], "base"), load(sys.argv[2], "PR")
direct=[n for n, p in base.items() if p.get("inherited") is False]
if "mathlib" not in direct: print("ERROR: base manifest has no direct 'mathlib' package"); sys.exit(1)
for n in direct:
    b, p = base[n], pr.get(n)
    if b.get("type")!="git": print(f"ERROR: base {n} package is not type git"); sys.exit(1)
    if p is None: print(f"ERROR: PR manifest has no {n!r} package"); sys.exit(1)
    if p.get("type")!="git": print(f"ERROR: {n} package is not type git (got {p.get('type')!r})"); sys.exit(1)
    for side, e in (("base", b), ("PR", p)):
        if not re.fullmatch(r"[0-9a-f]{40}", str(e.get("rev") or "")):
            print(f"ERROR: {side} {n} rev {e.get('rev')!r} is not a 40-hex commit SHA"); sys.exit(1)
    if norm(p.get("url"))!=norm(b.get("url")):
        print(f"ERROR: {n} url changed ({b.get('url')} -> {p.get('url')}) — repo swap is human-owned"); sys.exit(1)
    if p.get("inputRev")!=b.get("inputRev") or not b.get("inputRev"):
        print(f"ERROR: {n} inputRev (nominated branch) changed ({b.get('inputRev')} -> {p.get('inputRev')}) — human-owned"); sys.exit(1)
    path="/".join(x for x in (b.get("subDir"), b.get("manifestFile") or "lake-manifest.json") if x)
    print("\t".join([n, norm(b["url"]), b["rev"], p["rev"], b["inputRev"], path]))
PY
}

directs="$(direct_deps "$BASE/lake-manifest.json" "$PR/lake-manifest.json")" || fail "${directs#ERROR: }"

# --- 2. each direct dependency stayed put or moved forward --------------------
DEP_NAMES=(); DEP_SLUGS=(); DEP_REVS=(); DEP_MANIFESTS=()
moved=0
while IFS=$'\t' read -r -u 3 NAME URL REV_B REV_P BRANCH MPATH; do
  SLUG="$(slug "$URL")"
  DEP_NAMES+=("$NAME"); DEP_SLUGS+=("$SLUG"); DEP_REVS+=("$REV_P"); DEP_MANIFESTS+=("$MPATH")
  if [ "$NAME" = mathlib ]; then ML_SLUG="$SLUG"; ML_REV_P="$REV_P"; fi
  if [ "$REV_B" = "$REV_P" ]; then
    echo "bump-guard: $NAME pin unchanged."
    continue
  fi
  moved=1
  st_fwd="$(gh api "repos/$SLUG/compare/$REV_B...$REV_P" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $SLUG $REV_B...$REV_P"
  # Membership is checked against the trusted branch nominated by base's manifest.
  st_branch="$(gh api "repos/$SLUG/compare/$REV_P...$BRANCH" --jq '.status' 2>/dev/null)" \
    || fail "compare API failed for $SLUG $REV_P...$BRANCH"
  on_branch=0
  case "$st_branch" in ahead|identical) on_branch=1 ;; esac  # the branch tip is at-or-ahead of new
  TAG=""
  if [ "$st_fwd" = ahead ]; then
    [ "$on_branch" = 1 ] \
      || fail "$NAME new rev $REV_P is not on branch '$BRANCH' (compare status: ${st_branch:-unknown})"
    echo "bump-guard: $NAME $REV_B -> $REV_P is a forward move on '$BRANCH'."
  elif [ "$NAME" = mathlib ] && [ "$st_fwd" = diverged ]; then
    # Diverged: forward only onto a strictly newer toolchain, at a release tag or on the branch.
    ML_TC_NEW="$(gh api "repos/$SLUG/contents/lean-toolchain?ref=$REV_P" --jq '.content' 2>/dev/null | base64 -d | tr -d '[:space:]')" \
      || fail "cannot fetch mathlib lean-toolchain at $REV_P"
    newer="$(toolchain_newer "$TC_B" "$ML_TC_NEW")" \
      || fail "mathlib rev is not a forward move from base: it diverged from $REV_B and its toolchain is not newer than base's ($newer)"
    TAG="$(gh api "repos/$SLUG/tags?per_page=100" --paginate --jq ".[] | select(.commit.sha == \"$REV_P\") | .name" 2>/dev/null \
      | grep -E '^v[0-9]+\.[0-9]+\.[0-9]+(-rc[0-9]+)?$' | head -n1)"
    if [ -n "$TAG" ]; then
      echo "bump-guard: mathlib $REV_B -> $REV_P is release $TAG, on newer toolchain $ML_TC_NEW."
    elif [ "$on_branch" = 1 ]; then
      echo "bump-guard: mathlib $REV_B -> $REV_P is on '$BRANCH', on newer toolchain $ML_TC_NEW."
    else
      fail "mathlib new rev $REV_P diverged from $REV_B and is neither a release tag nor on branch '$BRANCH' (compare status: ${st_branch:-unknown})"
    fi
  else
    fail "$NAME rev is not a forward move from base (compare status: ${st_fwd:-unknown}); old=$REV_B new=$REV_P"
  fi
  [ "$NAME" = mathlib ] || continue

  # --- 2b. the new mathlib rev is one whose cache was actually published --------
  # Being on master is not enough. Mathlib lands in batches: bors tests a batch and
  # fast-forwards master over all of its commits, but only the resulting master tip is
  # built by the push-triggered CI run, and that run is the one that publishes to the
  # `mathlib4-master` cache container (its `upload_cache` job gets the master writer when
  # `ref_name == 'master'`; asking for `event=push` is this check's own narrowing, to the
  # build of the batch's final commit). A batch's intermediate commits
  # are ordinary ancestors whose oleans were never uploaded, so pinning to one costs every
  # downstream build a full recompile of whatever that commit invalidated: a rename in a
  # core algebra file is ~1400 modules and about an hour, on every CI run and every
  # pr-build, until the pin moves again.
  #
  # We require that publishing run to have COMPLETED successfully on this exact rev. That
  # is both narrower and better timed than asking bors: bors reports success on the batch
  # commit before the master build has uploaded anything, so a very fresh tip can carry a
  # green bors status while its cache is still hours away. Coupling to upstream's workflow
  # file name is deliberate. If it is renamed this check fails closed and the bump routes
  # to a human, which is the safe direction for a trust anchor.
  # The question itself lives in mathlib_cache.py, which resolve_deps.py asks too: the resolver must
  # not propose a rev this step would refuse.
  #
  # A patch release is committed off master, so no master-push build ever covers it;
  # mathlib's release_cache.yml rebuilds each `v4.*` tag off master and publishes it to
  # the same container. For a release tag off master we accept that run, on that tag,
  # instead. For a tag ON master it proves nothing (the workflow skips the build and
  # still succeeds), so only the master-push build counts there.
  pub_rc=0
  pub_msg="$(python3 - "$(dirname "$0")" "$SLUG" "$REV_P" "$TAG" <<'PY' 2>&1
import sys
sys.path.insert(0, sys.argv.pop(1))
from mathlib_cache import master_build_published, release_cache_published
from pr_status.core import gh_api
slug, rev, tag = sys.argv[1:4]
try:
    if master_build_published(gh_api, slug, rev):
        print("master"); sys.exit(0)
    if tag and release_cache_published(gh_api, slug, rev, tag):
        print("release"); sys.exit(0)
except Exception as exc:
    print(f"workflow-runs API failed for {slug} {rev}: {exc}")
    sys.exit(2)
sys.exit(1)
PY
  )" || pub_rc=$?
  [ "$pub_rc" -ne 2 ] || fail "$pub_msg"
  if [ "$pub_rc" -eq 0 ]; then
    if [ "$pub_msg" = release ]; then
      echo "bump-guard: mathlib $TAG has a successful release_cache.yml run, so its cache is published."
    else
      echo "bump-guard: mathlib $REV_P has a successful master-push build, so its cache is published."
    fi
    continue
  fi
  if [ -n "$TAG" ]; then
    fail "mathlib release $TAG ($REV_P) has no published cache: no completed, successful master-push build and, for a tag off master, no completed, successful release_cache.yml run on it; wait for it"
  fi
  fail "mathlib rev $REV_P has no completed, successful master-push build, so its oleans were never published to the cache; bump to the built tip of that batch, or wait for its build to finish"
done 3<<<"$directs"

if [ "$moved" = 0 ]; then
  # No direct dependency moved: then NOTHING in the manifest may change (the rest is derived).
  diff -q "$BASE/lake-manifest.json" "$PR/lake-manifest.json" >/dev/null 2>&1 \
    || fail "no direct dependency rev changed but the manifest changed — not a derived bump"
fi

# --- 3. the rest of the manifest is EXACTLY derived from the direct dependencies
DEP_TMP="$(mktemp -d)"; trap 'rm -rf "$DEP_TMP"' EXIT
DEP_ARGS=()
for i in "${!DEP_NAMES[@]}"; do
  n="${DEP_NAMES[$i]}"; f="$DEP_TMP/$i.json"
  gh api "repos/${DEP_SLUGS[$i]}/contents/${DEP_MANIFESTS[$i]}?ref=${DEP_REVS[$i]}" --jq '.content' 2>/dev/null | base64 -d >"$f" \
    && [ -s "$f" ] || fail "cannot fetch $n ${DEP_MANIFESTS[$i]} at ${DEP_REVS[$i]}"
  DEP_ARGS+=("$n=$f")
done

derived_msg="$(python3 "$(dirname "$0")/bump_manifest.py" "$PR/lake-manifest.json" "$BASE/lake-manifest.json" "${DEP_ARGS[@]}")" \
  || fail "${derived_msg:-transitive pins do not match the direct dependencies at their new revs}"
echo "bump-guard: the manifest is derived from ${DEP_NAMES[*]} at their new revs and matches base in every other field."

# --- 4. toolchain: monotonic forward AND consistent with mathlib --------------
if [ "$TC_B" != "$TC_P" ]; then
  tc_msg="$(toolchain_newer "$TC_B" "$TC_P")" || fail "${tc_msg:-toolchain is not a monotonic forward release}"
fi

ML_TC="$(gh api "repos/$ML_SLUG/contents/lean-toolchain?ref=$ML_REV_P" --jq '.content' 2>/dev/null | base64 -d | tr -d '[:space:]')" \
  || fail "cannot fetch mathlib lean-toolchain at $ML_REV_P"
[ "$TC_P" = "$ML_TC" ] || fail "PR lean-toolchain ($TC_P) != mathlib@$ML_REV_P's ($ML_TC)"
echo "bump-guard: toolchain $TC_B -> $TC_P is forward and matches mathlib@$ML_REV_P."

ok "forward-only bump validated (${DEP_NAMES[*]} forward on their branches, derived transitive pins, toolchain consistent)"
