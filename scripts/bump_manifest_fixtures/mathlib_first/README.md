Evidence for the rule "a package pinned by several dependencies is the entry of the one the lakefile
requires LAST", which bump_manifest.py applies: Lake takes the pins of the last require that pins a
package, and `lakefile.toml` declares mathlib last.

- `root.json`: EpsilonEridani 749caa977 ("feat: Add Physlib and TauCeti as dependencies"), a real
  `lake update` with the requires in the order mathlib, Physlib, TauCeti.

Its upstream manifests are `../three_deps/`'s: mathlib db1c574, Physlib 35d1bb4, and TauCeti, whose
manifest is byte-identical at 85e8005e (what `root.json` pins) and at a1fff14 (what `three_deps/pr.json`
pins). `three_deps/base.json` (2a2b8dc42, "Reorder dependencies to prioritize Mathlib versions", requires
in the order Physlib, TauCeti, mathlib) is the same project after moving mathlib to the bottom.

The eight packages that TauCeti pins differently from mathlib and Physlib (Cli, LeanSearchClient, Qq,
aesop, batteries, importGraph, plausible, proofwidgets) are TauCeti's in `root.json` and mathlib's
(= Physlib's) in `three_deps/base.json`. Only the order of the requires differs.

`root.json` is stored compact (one line, same content as the file Lake writes; `python3 -m json.tool FILE`
reads it), to keep the PR under the repository's diff-size cap.

Used by test_bump_manifest.py (`LastRequireWins`). bump_manifest.py derives each shared package from the
dependency the lakefile requires last, and reproduces both manifests: `root.json` with the order
mathlib, Physlib, TauCeti, and `three_deps/pr.json` with Physlib, TauCeti, mathlib. In `root.json` TauCeti
also beats Physlib, which pins the same eight packages as mathlib, so the rule covers a package only
Physlib and TauCeti pin as well.
