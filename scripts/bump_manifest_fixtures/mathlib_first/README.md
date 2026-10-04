Evidence for the rule "a package mathlib pins is mathlib's entry", which bump_manifest.py applies:
`lakefile.toml` declares mathlib LAST, and Lake takes the pins of the LAST require that pins a package.

- `root.json`: EpsilonEridani 749caa977 ("feat: Add Physlib and TauCeti as dependencies"), a real
  `lake update` with the requires in the order mathlib, Physlib, TauCeti;
- `TauCeti.json`: TauCeti's own lake-manifest.json at the rev `root.json` pins (85e8005e);
- mathlib db1c574 and Physlib 35d1bb4 are the same revs as in `../three_deps/`, whose `base.json`
  (2a2b8dc42, "Reorder dependencies to prioritize Mathlib versions", requires in the order Physlib,
  TauCeti, mathlib) is the same project after moving mathlib to the bottom.

The eight packages that TauCeti pins differently from mathlib and Physlib (Cli, LeanSearchClient,
Qq, aesop, batteries, importGraph, plausible, proofwidgets) are TauCeti's in `root.json` and mathlib's
(= Physlib's) in `../three_deps/base.json`. Only the order of the requires differs.

Used by test_bump_manifest.py (`LastRequireWins`). bump_manifest.py derives each shared package from the
dependency the lakefile requires last, and reproduces both manifests: `root.json` with the order
mathlib, Physlib, TauCeti, and `../three_deps/pr.json` with Physlib, TauCeti, mathlib. In `root.json`
TauCeti also beats Physlib, which pins the same eight packages as mathlib, so the rule covers a package
only Physlib and TauCeti pin as well.
