import Physlib.QFT.PerturbationTheory.WickAlgebra.NormalOrder.Basic

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0090-fix-WickAlgebra-disambiguate-mulLinearMap-in-NormalO.patch
@@ -80,9 +80,9 @@ lemma ι_normalOrderF_superCommuteF_ofCrAnOpF_eq_zero_mul (φa φa' : 𝓕.CrAnF
       ([ofCrAnOpF φa, ofCrAnOpF φa']ₛF * b) = 0 := by
     apply ofCrAnListFBasis.ext
     intro l
-    simp only [mulLinearMap, FieldOpFreeAlgebra.ofListBasis_eq_ofList, LinearMap.coe_comp,
-      Function.comp_apply, LinearMap.flip_apply, LinearMap.coe_mk, AddHom.coe_mk,
-      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
+    simp only [FieldOpFreeAlgebra.mulLinearMap, FieldOpFreeAlgebra.ofListBasis_eq_ofList,
+      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, LinearMap.coe_mk,
+      AddHom.coe_mk, AlgHom.toLinearMap_apply, LinearMap.zero_apply]
     rw [← mul_assoc]
     exact ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero φa φa' _ _
   rw [hf]
@@ -130,9 +130,9 @@ lemma ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero_mul
     mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF (ofCrAnListF φs)) = 0 := by
     apply ofCrAnListFBasis.ext
     intro φs'
-    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
-      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
-      LinearMap.zero_apply]
+    simp only [FieldOpFreeAlgebra.mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
+      ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
+      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
     rw [ι_normalOrderF_superCommuteF_ofCrAnListF_ofCrAnListF_eq_zero_mul]
   rw [hf]
   simp
@@ -146,9 +146,9 @@ lemma ι_normalOrderF_superCommuteF_eq_zero_mul
     mulLinearMap.flip b ∘ₗ mulLinearMap a ∘ₗ superCommuteF.flip c) = 0 := by
     apply ofCrAnListFBasis.ext
     intro φs
-    simp only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, ofListBasis_eq_ofList,
-      LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply, AlgHom.toLinearMap_apply,
-      LinearMap.zero_apply]
+    simp only [FieldOpFreeAlgebra.mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
+      ofListBasis_eq_ofList, LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
+      AlgHom.toLinearMap_apply, LinearMap.zero_apply]
     rw [ι_normalOrderF_superCommuteF_ofCrAnListF_eq_zero_mul]
   rw [hf]
   simp
-- 
2.55.0

-/

