import Physlib.Relativity.PauliMatrices.AsTensor

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0101-fix-PauliMatrices-keep-Lorentz-matrix-scalars-in-in-.patch
@@ -135,43 +135,52 @@ def asConsTensor :
             refine Finset.sum_congr rfl (fun i _ => ?_)
             rw [tmul_sum]
             rfl
-        _ = ∑ x, ∑ i, ∑ j, ((SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
+        -- The scalars here are entries of a *real* Lorentz matrix, while the modules are
+        -- complex.  An `ℝ`-action on `M ⊗[ℂ] N` is `TensorProduct.leftHasSMul` (restriction of
+        -- scalars on the left factor), whereas every Mathlib lemma about `ℝ`-actions on a
+        -- `ℂ`-module is phrased through `Module.complexToReal`.  Those two agree only at default
+        -- transparency, so reconciling them inside `rw`/`simp` overruns the typeclass heartbeat
+        -- budget.  Coercing each scalar to `ℂ` before it reaches the tensor product keeps every
+        -- action a base-ring action and avoids the reconciliation entirely.  Do not push these
+        -- casts back to `ℝ`.
+        _ = ∑ x, ∑ i, ∑ j, (((SL2C.toLorentzGroup M).1 i x *
+            (SL2C.toLorentzGroup M⁻¹).1 x j : ℝ) : ℂ)
             • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
             refine Finset.sum_congr rfl (fun x _ => (Finset.sum_congr rfl (fun i _ =>
               (Finset.sum_congr rfl (fun j _ => ?_)))))
             simp only [SL2C.toLorentzGroup_apply_coe, map_inv, LorentzGroup.inv_eq_dual,
-              LinearMap.map_smul_of_tower, LinearEquiv.coe_coe]
-            rw [smul_tmul, smul_smul, ← tmul_smul]
-        _ = ∑ i, ∑ j, ∑ x, ((SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j)
+              LinearEquiv.coe_coe]
+            rw [← Complex.coe_smul, ← Complex.coe_smul, map_smul, tmul_smul, smul_tmul',
+              smul_smul, ← Complex.ofReal_mul, mul_comm, smul_tmul']
+        _ = ∑ i, ∑ j, ∑ x, (((SL2C.toLorentzGroup M).1 i x *
+            (SL2C.toLorentzGroup M⁻¹).1 x j : ℝ) : ℂ)
             • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
             rw [Finset.sum_comm]
             exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
-        _ = ∑ i, ∑ j, ∑ x, (((SL2C.toLorentzGroup M).1 i x *
-            (SL2C.toLorentzGroup M⁻¹).1 x j : ℝ) : ℂ)
-            • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := rfl
         _ = ∑ i, ∑ j, (∑ x, (SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j : ℂ)
             • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
             refine Finset.sum_congr rfl (fun i _ => (Finset.sum_congr rfl (fun j _ => ?_)))
             rw [← Finset.sum_smul]
             simp
-        _ = ∑ i, ∑ j, (∑ x, (SL2C.toLorentzGroup M).1 i x * (SL2C.toLorentzGroup M⁻¹).1 x j : ℝ)
+        _ = ∑ i, ∑ j, ((∑ x, (SL2C.toLorentzGroup M).1 i x *
+            (SL2C.toLorentzGroup M⁻¹).1 x j : ℝ) : ℂ)
             • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
             refine Finset.sum_congr rfl (fun i _ => (Finset.sum_congr rfl (fun j _ => ?_)))
-            congr
-            simp
-        _ = ∑ i, ∑ j, ((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) i j : ℝ)
+            congr 1
+            push_cast
+            rfl
+        _ = ∑ i, ∑ j, (((1 : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) i j : ℝ) : ℂ)
           • ((complexContrBasis i)) ⊗ₜ[ℂ] leftRightToMatrix.symm ((pauliBasis j)) := by
             refine Finset.sum_congr rfl (fun i _ => (Finset.sum_congr rfl (fun j _ => ?_)))
-            congr
+            congr 2
             change ((SL2C.toLorentzGroup M) * (SL2C.toLorentzGroup M⁻¹)).1 i j = _
             rw [← SL2C.toLorentzGroup.map_mul]
             simp only [mul_inv_cancel, _root_.map_one, lorentzGroupIsGroup_one_coe]
         _ = asTensor := by
           refine Finset.sum_congr rfl (fun i _ => ?_)
           rw [Finset.sum_eq_single i (fun b _ hb => ?_) (fun hb => ?_)]
-          · simp only [one_apply_eq, one_smul]
-          · simp [one_apply_ne' hb]
-            module
+          · simp only [one_apply_eq, Complex.ofReal_one, one_smul]
+          · simp only [one_apply_ne' hb, Complex.ofReal_zero, zero_smul]
           · simp only [Finset.mem_univ, not_true_eq_false] at hb
 
 /-- The map `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ leftHanded ⊗ rightHanded` corresponding
-- 
2.55.0

-/

