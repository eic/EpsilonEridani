/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Relativity.Fermions.Weyl.Unit


/-


TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0100-fix-Weyl-discharge-the-determinant-side-goal-in-dual.patch
@@ -103,8 +103,19 @@ def dualLeftLeftUnit :
     simp only [dualLeftLeftUnitVal]
     rw [dualLeftLeftToMatrix_ρ_symm]
     apply congrArg
-    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
-      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]
+    -- `dualLeftLeftToMatrix_ρ_symm` states its conclusion with the raw subtype projection
+    -- `M.1`, whereas `Matrix.SpecialLinearGroup.det_coe` is stated about the coercion `↑ₘM`.
+    -- The two are definitionally equal but not syntactically so, and `simp` matches
+    -- syntactically, so it could never discharge the `IsUnit _.det` side goal of
+    -- `Matrix.mul_nonsing_inv` -- leaving `1 = (↑M * (↑M)⁻¹)ᵀ` unsolved. Establishing the
+    -- determinant fact through an explicit `show`, which elaborates at default transparency
+    -- where the two spellings agree, and then passing it to `mul_nonsing_inv` by hand, avoids
+    -- the mismatch. Do not fold this back into the `simp only`.
+    have hdet : IsUnit (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det := by
+      rw [show (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 from M.2]
+      exact isUnit_one
+    simp only [mul_one, ← transpose_mul]
+    rw [Matrix.mul_nonsing_inv _ hdet, Matrix.transpose_one]

 /-- Applying the morphism `dualLeftLeftUnit` to `1` returns `dualLeftLeftUnitVal`. -/
 lemma dualLeftLeftUnit_apply_one : dualLeftLeftUnit (1 : ℂ) = dualLeftLeftUnitVal := by
--
2.55.0

-/

/-
-- Patch: 0102-docs-review-drop-the-notation-from-the-explanatory-c.patch
@@ -104,13 +104,14 @@ def dualLeftLeftUnit :
     rw [dualLeftLeftToMatrix_ρ_symm]
     apply congrArg
     -- `dualLeftLeftToMatrix_ρ_symm` states its conclusion with the raw subtype projection
-    -- `M.1`, whereas `Matrix.SpecialLinearGroup.det_coe` is stated about the coercion `↑ₘM`.
-    -- The two are definitionally equal but not syntactically so, and `simp` matches
-    -- syntactically, so it could never discharge the `IsUnit _.det` side goal of
-    -- `Matrix.mul_nonsing_inv` -- leaving `1 = (↑M * (↑M)⁻¹)ᵀ` unsolved. Establishing the
-    -- determinant fact through an explicit `show`, which elaborates at default transparency
-    -- where the two spellings agree, and then passing it to `mul_nonsing_inv` by hand, avoids
-    -- the mismatch. Do not fold this back into the `simp only`.
+    -- `M.1`, whereas `Matrix.SpecialLinearGroup.det_coe` is stated about the coercion
+    -- `(M : Matrix (Fin 2) (Fin 2) ℂ)`. The two are definitionally equal but not
+    -- syntactically so, and `simp` matches syntactically, so it could never discharge the
+    -- `IsUnit _.det` side goal of `Matrix.mul_nonsing_inv`; the goal was left as
+    -- `1 = (↑M * (↑M)⁻¹)ᵀ`, in the compiler's own printing. Establishing the determinant
+    -- fact through an explicit `show`, which elaborates at default transparency where the
+    -- two spellings agree, and then passing it to `mul_nonsing_inv` by hand, avoids the
+    -- mismatch. Do not fold this back into the `simp only`.
     have hdet : IsUnit (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det := by
       rw [show (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 from M.2]
       exact isUnit_one
--
2.55.0

-/

