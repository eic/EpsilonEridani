# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Mathlib download cache (GitHub Actions)

The main `ci.yml` workflow maintains a narrow snapshot of Mathlib's compressed download store:
`$MATHLIB_CACHE_DIR/*.ltar`. The `.ltar` files are content-addressed; cache-tool scratch files,
executables, and the unpacked `.lake` tree are not included. The local
`.github/actions/restore-mathlib-ltars` action sets `MATHLIB_CACHE_DIR` job-wide through
`$GITHUB_ENV`, defaulting to `$GITHUB_WORKSPACE/.mathlib-ltar-cache`; its `cache-dir` input can
override that location. Main publishes only after a non-exact restore: an exact key is immutable
and already contains this pin's snapshot. Before publishing, main runs `lake exe cache clean` so
the snapshot contains only files needed by the current pin; if pruning fails, it skips publication
instead of saving an unpruned snapshot. PR and merge-group jobs in `pr-build.yml` may restore this
trusted snapshot but never publish one. `pages.yml` and
`pr-profile.yml` are intentionally outside this initial rollout: `ci.yml` is included as the sole
publisher and `pr-build.yml` as the highest-volume consumer. `pr-profile.yml` has comparable
per-PR fetch volume but remains outside as a rollout control. Both excluded workflows continue
fetching into Mathlib's default cache directory.

Keys have the shape
`mathlib-ltar-v1-<os>-<arch>-<lean-toolchain hash>-<lake-manifest hash>`. An exact match reuses the
current pin. The restore prefix omits the manifest hash, so a Mathlib-only pin bump can start from
the newest snapshot for the same Lean toolchain and fetch only missing files. A toolchain bump has
no prefix match. In every case, `lake exe cache get` remains authoritative and downloads whatever
the snapshot lacks. This design mirrors Mathlib's own cache-snapshot warming in
`.github/workflows/build_template.yml` and `.github/actions/get-cache`, using `actions/cache`
instead of per-run artifacts.

GitHub Actions cache entries are immutable. If an entry is poisoned or the format becomes
incompatible, bump `mathlib-ltar-v1` once in
`.github/actions/restore-mathlib-ltars/action.yml`. To discard a single entry instead, find it with
`gh cache list --repo eic/EpsilonEridani` and delete its exact key with
`gh cache delete <key> --repo eic/EpsilonEridani`. A failed fetch also retries once with
`lake exe cache get!`, which forces every linked file to be downloaded and unpacked again.

Downloads go to the cache tool's default read endpoint. The escape hatch is a repository
variable. Every workflow that runs `lake exe cache get` (`ci.yml`, `pr-build.yml`,
`pr-profile.yml`, `nightly-verify.yml`, `pages.yml`) exports
`MATHLIB_CACHE_DEBUG_USE_LEGACY` from `vars.MATHLIB_CACHE_DEBUG_USE_LEGACY`. An operator
sets the variable to `1` to send reads back to the legacy storage endpoint, and clears it
to return to the default endpoint. Both changes apply on the next run, with no code
change: the tool treats unset, empty, `0`, and `false` alike as off. Local and radar runs
need no wiring; the cache tool reads the variable from the caller's environment.

The flag is temporary. It exists only for an easy rollback during the transition to the
default endpoint that leanprover-community/mathlib4@03616a12 introduced, and upstream
plans to retire it together with direct reads from the storage account. Remove this
wiring when the pinned cache tool drops the flag.

## Dependency build cache (GitHub Actions)

Mathlib's cache tool restores Mathlib and the packages Mathlib itself depends on, nothing else.
Every other dependency in `lake-manifest.json` (Physlib, TauCeti, and any added later) used to be
compiled from source on every build; Physlib alone was about 1,500 CPU-seconds of each PR build.

`ci.yml` on main therefore saves those packages' `.lake/build` trees after its build, and
`pr-build.yml` (PRs and the merge queue) restores them before the sandboxed build:

- `scripts/dependency_builds.py` decides the packages (the manifest minus `mathlib` and minus
  Mathlib's own manifest, so new dependencies are covered automatically), packs them into one
  archive, and validates the archive before unpacking: every member must be a regular file or
  directory under `<package>/.lake/build/`, or nothing is extracted. Members of a package no
  longer in the manifest are skipped.
- `.github/actions/restore-dependency-builds` restores the archive and unpacks it with the
  script next to it (`gate/scripts/` in `pr-build.yml`).
- The archive sits at `$RUNNER_TEMP/dependency-builds.tar`, a path identical in both workflows,
  because `actions/cache` hashes the `path` input into the entry's version and the two workflows
  build in different directories (`.` and `pr/`).

Keys have the shape
`dependency-builds-v1-<os>-<arch>-<lean-toolchain hash>-<lake-manifest hash>`, with the same
toolchain-prefix fallback as the Mathlib snapshot. Only main writes: `pr-build.yml` never saves,
so a PR cannot plant outputs a later build reuses. Lake still compares every module's trace, so
after a pin bump the stale outputs a prefix restore brings in are rebuilt, not trusted. Every
step is best-effort (`continue-on-error`): a miss or a refused archive means compiling the
dependencies from source, as before. To abandon a poisoned or incompatible entry, bump
`dependency-builds-v1` in the action and in nothing else.

## Bucket

The Lake artifact cache lives in a bucket on the National Research Platform's Nautilus Ceph
object store, which speaks the S3 API. It holds only this cache; the account that owns it owns
nothing else.

| | |
|---|---|
| S3 endpoint | `https://s3-central.nrp-nautilus.io` |
| Bucket | `epsiloneridani-cache` |
| Owner | the EIC EpsilonEridani account on Nautilus (`~/.s3cfg` on the operators' machines) |

The bucket is created and administered with `s3cmd`. The on-disk copy of the bucket policy
lives with the operator; the effective policy is readable with `s3cmd info s3://epsiloneridani-cache`.

## Bucket policy

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no
way to sign them, so the two Lake prefixes must be publicly readable; only uploads use a key.
The policy grants two things to everyone:

- `s3:GetObject` on `artifacts/*` and `revisions/*`;
- `s3:ListBucket` on the bucket, unconditionally.

The second grant is not about listing. S3 answers a GET of a missing key with 403 unless the
caller may list the bucket, and only then with 404. Lake backtracks to an ancestor's revision
map only on a 404; any other status is a failed lookup, after which `scripts/lake-cache-get.sh`
discards the cache and the build starts from scratch. A `ListBucket` grant conditioned on
`s3:prefix` does not help: the 404-or-403 decision is made without a prefix in the request
context, so the condition never matches. The cost of the unconditional grant is that anyone can
list the bucket, which exposes nothing beyond the content-hashed artifacts the public GETs
already serve.

```json
{
  "Version": "2012-10-17",
  "Statement": [
    {
      "Sid": "LakeCacheAnonymousRead",
      "Effect": "Allow",
      "Principal": "*",
      "Action": ["s3:GetObject"],
      "Resource": [
        "arn:aws:s3:::epsiloneridani-cache/artifacts/*",
        "arn:aws:s3:::epsiloneridani-cache/revisions/*"
      ]
    },
    {
      "Sid": "LakeCacheMissIs404",
      "Effect": "Allow",
      "Principal": "*",
      "Action": ["s3:ListBucket"],
      "Resource": ["arn:aws:s3:::epsiloneridani-cache"]
    }
  ]
}
```

Apply it with `s3cmd setpolicy <file> s3://epsiloneridani-cache`. To check it, an anonymous GET
of an unpublished revision map must answer 404, not 403:

```bash
curl -s -o /dev/null -w "%{http_code}\n" \
  https://s3-central.nrp-nautilus.io/epsiloneridani-cache/revisions/eic/EpsilonEridani/tc/leanprover--lean4---v4.34.1/0000000000000000000000000000000000000000.jsonl
```

## Endpoints

There is no separate public domain: reads and uploads use the same S3 host, reads anonymously
and uploads with the key. The variables hold only the prefix; Lake appends the scope.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://s3-central.nrp-nautilus.io/epsiloneridani-cache/artifacts` | `pr-build.yml`, `ci.yml`, `lint-full.yml`, `nightly-verify.yml`, `pages.yml`, `pr-profile.yml` reads |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://s3-central.nrp-nautilus.io/epsiloneridani-cache/revisions` | the same reads |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://s3-central.nrp-nautilus.io/epsiloneridani-cache/artifacts` | `publish-lake-cache` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://s3-central.nrp-nautilus.io/epsiloneridani-cache/revisions` | `publish-lake-cache` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `publish-lake-cache` job only |

Lake service names: `epsiloneridani-public` for reads, `epsiloneridani-s3` for uploads. Object
keys are `artifacts/eic/EpsilonEridani/<hash>.art` and
`revisions/eic/EpsilonEridani/tc/<toolchain>/<revision>.jsonl`, where the toolchain is the elan
name with `/` written as `--` and `:` as `---`.

Lake signs uploads with curl's `--aws-sigv4 aws:amz:auto:s3`, so the SigV4 region is the
literal `auto` and cannot be configured. Ceph accepts that; a plain AWS S3 bucket would not, so
moving this cache to AWS would also mean replacing the `lake cache put-staged` step with a
copy of the staged tree.

## Publisher credential

The GitHub Actions secret `LAKE_CACHE_KEY` contains the S3 access-key pair of a dedicated
Nautilus application key with object read/write access to `epsiloneridani-cache`. It is not an
operator's personal key.

When rotating it, create the replacement key, install the new
`<ACCESS_KEY_ID>:<SECRET_ACCESS_KEY>` pair as `LAKE_CACHE_KEY`, and let an isolated
`publish-lake-cache` job publish an exact revision before revoking the old key. Do not put the
key value in a repository variable or expose it to the build job.

## Contributors

The read endpoints above are anonymous and are not secrets, so `scripts/lake-cache-get.sh` defaults
to them and a contributor needs no configuration:

```bash
bash scripts/lake-cache-get.sh .
```

This is the second half of a working local build and the README documents it as such. Skipping it
does not fail anything; it compiles the whole library from source instead, which is why its absence
went unnoticed for as long as it did. CI keeps passing the endpoints explicitly from the
`LAKE_CACHE_*_PUBLIC` repo variables and reaches the script only when those are set, so the defaults
never decide what CI does.

## Why the upload is its own job

`ci.yml` publishes in two jobs. `build` compiles main and *stages* the artifacts; the separate
`publish-lake-cache` job holds `LAKE_CACHE_KEY` and uploads them. The split is a trust boundary,
not a convenience.

`build` runs `lake build` unsandboxed, as the runner user, on whatever landed on main, and Lean
executes code at elaboration time. `run_cmd`, `initialize` and macro-time IO are all unrestricted:
the scope, import-boundary and `set_option` guards are textual scans, and a file that writes
during elaboration exits 0 with no diagnostic. Such code runs with the runner user's privileges,
so it can rewrite `$HOME/.elan/bin/lake`, prepend a directory to every later step's `PATH` through
`$GITHUB_PATH`, or set `LD_PRELOAD` or `BASH_ENV` for every later step through `$GITHUB_ENV`.
Hardening the individual commands that touch the key does not help: any secret placed in a later
step of that job is a secret placed in reach of code that landed on main. (This is not reachable
from an unmerged PR, which compiles only under bwrap in `pr-build.yml`, with writes confined to
`base/.lake` and no secret in the sandbox's `--env` allowlist.)

So `build` runs `lake cache stage`, which needs no credential and touches no network, and hands
the staging directory to `publish-lake-cache` as a workflow artifact: about 60 MB, one flat
directory of `.ltar` files plus the mappings. That job checks out exactly one file and has no Lake
workspace and no dependencies, so no code from this repository or from Mathlib runs anywhere in
it, and it takes no `GITHUB_TOKEN` scopes. `lake cache put-staged` is the command for exactly
this: it does not configure the workspace and so does not execute arbitrary user code.

Nothing the build job reports is trusted there. The one file `publish-lake-cache` checks out is
`lean-toolchain`, because which toolchain it installs decides which `lake` binary handles the key,
and `elan toolchain install owner/repo:tag` fetches from that repository's releases. Taking that
name from the build job would hand the choice straight back to code that landed on `main`, which
can rewrite `lean-toolchain` on disk or poison the reporting step through `$GITHUB_ENV`. The pin
is read from the repository instead, its shape is re-checked against `leanprover/lean4:` releases,
and it must equal what the build job reports it built with.

Because it does not configure the workspace, `put-staged` cannot derive the toolchain and platform
halves of the upload scope, so the job passes `--rev` and `--toolchain` explicitly and relies on
the default of no platform. That reproduces the scope `lake cache put` derived, verified by
comparing the revision URLs the two commands emit, which are identical:
`revisions/eic/EpsilonEridani/tc/leanprover--lean4---<version>/<rev>.jsonl`. The platform is
absent because `lakefile.toml` sets `platformIndependent = true`; the staging step fails loudly if
that ever stops being true, since a silent mismatch would publish under a scope `pr-build` never
reads.

The staged tree arrives from a job that ran code that landed on main, so `publish-lake-cache`
checks it before pointing Lake at it: the tree must be a flat directory of regular files, and
every string in the mappings must be a plain `<hash>.<ext>` artifact name. Lake parses an artifact
name as everything after the first dot and joins it to the staging directory without checking that
the result stays inside, so an unchecked name like `0.art/../../../proc/self/environ` would
otherwise have Lake read the publishing job's environment and `PUT` it into a publicly readable
bucket.

## Cost

Nautilus object storage is allocated to the project rather than metered per request, so there
is no per-read bill to estimate. Each build fetches one map plus one artifact per module it
reuses, a few hundred small objects, and each publication writes about the same. Keep an eye on
the bucket's size if the allocation is ever tightened; artifacts are immutable and nothing
prunes them, so the bucket grows with every published revision.

## Related

- `scripts/lake-cache-get.sh` keeps hash-verified artifacts while retrying only
  missing downloads. If all three attempts remain incomplete, it discards the
  partial cache rather than handing it to the offline sandbox.
- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` exit status was
  unreliable. Ships in v4.34.0, not backported to v4.33.0.
