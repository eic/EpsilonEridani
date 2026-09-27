import Physlib.Relativity.SL2C.Basic


/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0005-refactor-Relativity-adapt-SL-2-C-and-Weyl-proofs-to-.patch
@@ -34,8 +34,11 @@ Possibly to be moved to mathlib at some point.
  /
 
 lemma inverse_coe (M : SL(2, ℂ)) : M.1⁻¹ = (M⁻¹).1 := by
-  rw [SpecialLinearGroup.coe_inv, Matrix.inv_def, SpecialLinearGroup.det_coe]
-  simp
+  have hdet : IsUnit M.1.det := by simp
+  calc
+    M.1⁻¹ = (↑hdet.unit⁻¹ : ℂ) • M.1.adjugate := Matrix.nonsing_inv_apply _ hdet
+    _ = M.1.adjugate := by simp
+    _ = (M⁻¹).1 := by simp
 
 lemma transpose_coe (M : SL(2, ℂ)) : M.1ᵀ = (M.transpose).1 := rfl
  /-!
@@ -52,7 +55,7 @@ we can define a representation a representation of `SL(2, ℂ)` on spacetime.
 @[simps!]
 noncomputable def toSelfAdjointMap (M : SL(2, ℂ)) :
     selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) →ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
-  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M,
+  toFun A := ⟨M.1 * A.1 * Matrix.conjTranspose M.1,
     by
       noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
         conjTranspose_mul, conjTranspose_conjTranspose,
@@ -124,18 +127,16 @@ lemma toSelfAdjointMap_apply_pauliBasis'_inl (M : SL(2, ℂ)) :
 def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
   toFun M := LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap
   M)
   map_one' := by
-    simp only [toSelfAdjointMap, SpecialLinearGroup.coe_one, one_mul, conjTranspose_one,
-      mul_one, Subtype.coe_eta]
-    erw [LinearMap.toMatrix_one]
+    change LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap 1)
= 1
+    have hId : toSelfAdjointMap (1 : SL(2, ℂ)) = 1 := by
+      ext A
+      simp [toSelfAdjointMap]
+    rw [hId, LinearMap.toMatrix_one]
   map_mul' M N := by
     rw [← LinearMap.toMatrix_mul]
     apply congrArg
-    ext1 x
-    erw [Module.End.mul_apply]
-    simp only [toSelfAdjointMap_apply, SpecialLinearGroup.coe_mul, conjTranspose_mul,
-      Subtype.mk.injEq]
-    ext1
-    noncomm_ring
+    ext A
+    simp [toSelfAdjointMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
 
 open Lorentz in
 lemma toMatrix_apply_contrMod (M : SL(2, ℂ)) (v : ContrMod 3) :
@@ -175,7 +176,7 @@ def toLorentzGroup : SL(2, ℂ) →* LorentzGroup 3 where
     simp only [_root_.map_mul, lorentzGroupIsGroup_mul_coe]
 
 lemma toLorentzGroup_eq_pauliBasis' (M : SL(2, ℂ)) :
-    toLorentzGroup M = LinearMap.toMatrix
+    (toLorentzGroup M).1 = LinearMap.toMatrix
     PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap M) := by
   rfl
 
@@ -283,7 +284,7 @@ lemma toLorentzGroup_det_one (M : SL(2, ℂ)) : det (toLorentzGroup M).val = 1 :
   have h : M.val = U * N * star U := M.val.schur_triangulation
   haveI : Invertible U.val := ⟨star U.val, U.property.left, U.property.right⟩
   calc det (toLorentzGroup M).val
-    _ = LinearMap.det (toSelfAdjointMap' M) := LinearMap.det_toMatrix ..
+    _ = LinearMap.det (toSelfAdjointMap' M.1) := LinearMap.det_toMatrix ..
     _ = LinearMap.det (toSelfAdjointMap' (U * N * U.val⁻¹)) :=
       suffices star U = U.val⁻¹ by rw [h, this]
       calc star U.val
-- 
2.55.0

-/

/-
-- Patch: 0077-style-fix-all-22-style-linter-errors-and-complete-th.patch
@@ -127,7 +127,8 @@ lemma toSelfAdjointMap_apply_pauliBasis'_inl (M : SL(2, ℂ)) :
 def toMatrix : SL(2, ℂ) →* Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ where
   toFun M := LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap
   M)
   map_one' := by
-    change LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis' (toSelfAdjointMap 1)
= 1
+    change LinearMap.toMatrix PauliMatrix.pauliBasis' PauliMatrix.pauliBasis'
+      (toSelfAdjointMap 1) = 1
     have hId : toSelfAdjointMap (1 : SL(2, ℂ)) = 1 := by
       ext A
       simp [toSelfAdjointMap]
diff --git a/EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/LeviCivita.lean
b/EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/LeviCivita.lean
index 0454235a..b7f5be0f 100644
--- a/EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/LeviCivita.lean
-/

