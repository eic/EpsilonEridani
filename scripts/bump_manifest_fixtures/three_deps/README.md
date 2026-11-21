Real manifests for a bump that moves a direct dependency other than mathlib:

- `pr.json`: EpsilonEridani af23eb2791 ("build: Update TauCeti dependency pin", a `lake update`
  moving TauCeti cd742d8 -> a1fff14);
- `base.json`: its parent 2a2b8dc42d;
- `mathlib.json`, `Physlib.json`, `TauCeti.json`: each direct dependency's own
  lake-manifest.json at the rev `pr.json` pins (mathlib db1c574, Physlib 35d1bb4,
  TauCeti a1fff14).

The files are stored compact (one line each, same content as the real manifests; `python3 -m json.tool FILE`
reads them), to keep the PR under the repository's diff-size cap.

Used by test_bump_manifest.py and test_check_bump.py.
