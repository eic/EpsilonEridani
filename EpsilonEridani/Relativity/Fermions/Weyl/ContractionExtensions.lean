import Physlib.Relativity.Fermions.Weyl.Contraction

set_option linter.style.longLine false

/-

set_option linter.style.longLine false

TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0005-refactor-Relativity-adapt-SL-2-C-and-Weyl-proofs-to-.patch
@@ -205,8 +205,9 @@ def rightDualContraction : (RightHandedWeyl.rep.tprod DualRightHandedWeyl.rep).I
       rw [transpose_mul]
       change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
       rw [← @conjTranspose_mul]
-      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
-        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
+      have hInv : (M.1)⁻¹ * M.1 = 1 := by
+        exact Matrix.nonsing_inv_mul (A := M.1) (by simp)
+      simp [hInv]
     rw [h2]
     simp only [one_mulVec, vec2_dotProduct, Fin.isValue, RightHandedWeyl.toFin2ℂEquiv_apply,
       DualRightHandedWeyl.toFin2ℂEquiv_apply]
@@ -247,8 +248,9 @@ def dualRightContraction : (DualRightHandedWeyl.rep.tprod RightHandedWeyl.rep).I
       rw [transpose_mul]
       change M.1.conjTranspose * (M.1)⁻¹.conjTranspose = 1ᵀ
       rw [← @conjTranspose_mul]
-      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
-        not_false_eq_true, nonsing_inv_mul, conjTranspose_one, transpose_one]
+      have hInv : (M.1)⁻¹ * M.1 = 1 := by
+        exact Matrix.nonsing_inv_mul (A := M.1) (by simp)
+      simp [hInv]
     rw [h2]
     simp only [vecMul_one, vec2_dotProduct, Fin.isValue, DualRightHandedWeyl.toFin2ℂEquiv_apply,
       RightHandedWeyl.toFin2ℂEquiv_apply]
diff --git a/EpsilonEridani/Relativity/SL2C/Basic.lean b/EpsilonEridani/Relativity/SL2C/Basic.lean
index f6a87276..1d94d75f 100644
--- a/EpsilonEridani/Relativity/SL2C/Basic.lean
-/

