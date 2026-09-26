import Physlib.Mathematics.Distribution.Basic

set_option linter.style.longLine false

/-

set_option linter.style.longLine false

TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0001-feat-Physlib-QFT-Scattering-DIS-initial-import.patch
@@ -129,7 +129,7 @@ on the size of `u` applied to `η`.
 
 /-- The construction of a distribution from the following data:
 1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
-2. We take a linear map `u` that evaluates the given Schwartz function `η`. At this stage we don't
+2. We take a linear map `u` that evaluates the given Schwartz function `η`. At this point we don't
   need `u` to be continuous.
 3. Recall that a Schwartz function `η` satisfies a bound
   `‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
diff --git a/EpsilonEridani/Particles/Fragmentation/Basic.lean b/EpsilonEridani/Particles/Fragmentation/Basic.lean
new file mode 100644
index 00000000..6e313d83
--- /dev/null
-/

