import Physlib.Relativity.Fermions.Weyl.Metric

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0146-fix-Weyl-repair-Metric.lean-against-the-coercion-vs-.patch
@@ -30,44 +30,64 @@ open CategoryTheory.MonoidalCategory
 /-- The raw `2x2` matrix corresponding to the metric for fermions. -/
 def metricRaw : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]
 
+/-- The determinant of the underlying matrix of an element of `SL(2, ℂ)` is a unit.
+
+  Everything in this file is phrased in terms of the raw subtype projection `M.1`, whereas
+  `Matrix.SpecialLinearGroup.det_coe` is stated about the coercion
+  `(M : Matrix (Fin 2) (Fin 2) ℂ)`. The two spellings are definitionally equal but not
+  syntactically so, and `simp` matches syntactically, so `det_coe` can never discharge the
+  `IsUnit _.det` side goal of `Matrix.mul_nonsing_inv` on a goal phrased with `M.1`.
+  Establishing the determinant fact through an explicit `show`, which elaborates at default
+  transparency where the two spellings agree, and then passing it to `mul_nonsing_inv` by hand,
+  avoids the mismatch. This mirrors the fix in `Physlib/Relativity/Fermions/Weyl/Unit.lean`;
+  do not fold it back into a `simp only`. -/
+lemma isUnit_det_coe (M : SL(2,ℂ)) : IsUnit (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det := by
+  rw [show (M.1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 from M.2]
+  exact isUnit_one
+
+/-- The inverse of the underlying matrix of an element of `SL(2, ℂ)`, written out explicitly.
+
+  Again this is phrased with the raw subtype projection `M.1`, whereas
+  `Matrix.SpecialLinearGroup.coe_inv` is stated about the coercion. Here the mismatch is worse
+  than for `det_coe`: the left-hand side of `coe_inv` is `↑ₘ(?A⁻¹)` whose `?A` carries a
+  metavariable type `SpecialLinearGroup ?n ?R`, so the pattern is not type-correct at the
+  `implicit` transparency level at which `rw` matches, and `rw [SpecialLinearGroup.coe_inv]`
+  reports `Did not find an occurrence of the pattern ↑?A⁻¹` however the goal is phrased.
+  Going through the repository's own `Lorentz.SL2C.inverse_coe` (stated with `.1`) and then
+  a `rfl` at default transparency avoids the pattern entirely. -/
+lemma inv_coe_fin_two (M : SL(2,ℂ)) : (M.1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
+    !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0] := by
+  have h : (M.1 : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ =
+      Matrix.adjugate (M.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
+    rw [Lorentz.SL2C.inverse_coe]
+    rfl
+  rw [h, Matrix.adjugate_fin_two]
+
 /-- Multiplying an element of `SL(2, ℂ)` on the left with the metric `𝓔` is equivalent
   to multiplying the inverse-transpose of that element on the right with the metric. -/
 lemma comm_metricRaw (M : SL(2,ℂ)) : M.1 * metricRaw = metricRaw * (M.1⁻¹)ᵀ := by
-  rw [metricRaw]
-  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
-  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
-  simp only [Fin.isValue, mul_zero, mul_neg, mul_one, zero_add, add_zero, transpose_apply, of_apply,
-    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
-    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, zero_smul, tail_cons, one_smul,
-    empty_vecMul, neg_smul, neg_cons, neg_neg, neg_empty, empty_mul, Equiv.symm_apply_apply]
+  rw [metricRaw, inv_coe_fin_two]
+  ext i j
+  fin_cases i <;> fin_cases j <;>
+    simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 lemma metricRaw_comm (M : SL(2,ℂ)) : metricRaw * M.1 = (M.1⁻¹)ᵀ * metricRaw := by
-  rw [metricRaw]
-  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
-  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
-  simp only [Fin.isValue, zero_mul, one_mul, zero_add, neg_mul, add_zero, transpose_apply, of_apply,
-    cons_val', cons_val_zero, empty_val', cons_val_fin_one, cons_val_one, cons_mul,
-    Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons, smul_eq_mul, mul_zero,
-    mul_one, smul_empty, tail_cons, neg_smul, mul_neg, neg_cons, neg_neg, neg_zero, neg_empty,
-    empty_vecMul, add_cons, empty_add_empty, empty_mul, Equiv.symm_apply_apply]
+  rw [metricRaw, inv_coe_fin_two]
+  ext i j
+  fin_cases i <;> fin_cases j <;>
+    simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 lemma star_comm_metricRaw (M : SL(2,ℂ)) : M.1.map star * metricRaw = metricRaw * ((M.1)⁻¹)ᴴ := by
-  rw [metricRaw]
-  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
-  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
-  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
-  simp
+  rw [metricRaw, inv_coe_fin_two]
+  ext i j
+  fin_cases i <;> fin_cases j <;>
+    simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 lemma metricRaw_comm_star (M : SL(2,ℂ)) : metricRaw * M.1.map star = ((M.1)⁻¹)ᴴ * metricRaw := by
-  rw [metricRaw]
-  rw [Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
-  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᴴ]
-  rw [eta_fin_two (!![M.1 0 0, M.1 0 1; M.1 1 0, M.1 1 1].map star)]
-  simp
+  rw [metricRaw, inv_coe_fin_two]
+  ext i j
+  fin_cases i <;> fin_cases j <;>
+    simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 /-- The metric `εᵃᵃ` as an element of `(leftHanded ⊗ leftHanded).V`. -/
 def leftMetricVal : LeftHandedWeyl ⊗[ℂ] LeftHandedWeyl :=
@@ -110,8 +130,7 @@ def leftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
     rw [leftLeftToMatrix_ρ_symm]
     apply congrArg
     rw [comm_metricRaw, mul_assoc, ← @transpose_mul]
-    simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
-      not_false_eq_true, mul_nonsing_inv, transpose_one, mul_one]
+    rw [Matrix.mul_nonsing_inv _ (isUnit_det_coe M), Matrix.transpose_one, mul_one]
 
 lemma leftMetric_apply_one : leftMetric (1 : ℂ) = leftMetricVal := by
   change (1 : ℂ) • leftMetricVal = leftMetricVal
@@ -154,8 +173,7 @@ def dualLeftMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
       rw [dualLeftdualLeftToMatrix_ρ_symm]
       apply congrArg
       rw [← metricRaw_comm, mul_assoc]
-      simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
-        not_false_eq_true, mul_nonsing_inv, mul_one]
+      rw [Matrix.mul_nonsing_inv _ (isUnit_det_coe M), mul_one]
 
 lemma dualLeftMetric_apply_one : dualLeftMetric (1 : ℂ) = dualLeftMetricVal := by
   change (1 : ℂ) • dualLeftMetricVal = dualLeftMetricVal
@@ -208,8 +226,7 @@ def rightMetric : (Representation.trivial ℂ SL(2,ℂ) ℂ).IntertwiningMap
         trans (M.1)⁻¹ᴴ * ((M.1))ᴴ
         · rfl
         rw [← @conjTranspose_mul]
-        simp only [SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq, one_ne_zero,
-          not_false_eq_true, mul_nonsing_inv, conjTranspose_one]
+        rw [Matrix.mul_nonsing_inv _ (isUnit_det_coe M), Matrix.conjTranspose_one]
       rw [h1]
       simp
     · rw [← rightRightToMatrix_ρ_symm metricRaw M]
-- 
2.55.0

-/

