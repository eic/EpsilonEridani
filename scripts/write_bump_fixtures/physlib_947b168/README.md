Real manifests for the Physlib bump of #141, where Physlib dropped doc-gen4 and with it five
inherited packages (`«doc-gen4»`, `leansqlite`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`):

- `base.json`: EpsilonEridani e199f68, the parent of the bump (Physlib bae4db6);
- `mathlib.json`, `Physlib.json`, `TauCeti.json`: each direct dependency's own lake-manifest.json
  at the rev the bump pins (mathlib d13f23b, Physlib 947b168, TauCeti a1fff14);
- `expected.json`: EpsilonEridani 67f9163's lake-manifest.json, the bump as merged and accepted by
  the bump guard, in Lake's own layout.

The inputs are stored compact (one line each, same content); `expected.json` is byte-for-byte the
merged file, so the test also checks the rendering.

Used by test_write_bump.py.
