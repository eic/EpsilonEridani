import Physlib.Particles.StandardModel.Fermions.LeptonDoublet

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0147-fix-StandardModel-drop-mul_comm-from-the-repGaugeGro.patch
@@ -154,7 +154,7 @@ noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI LeptonDoublet
     simp [valLinEquiv_symm_apply]
   map_mul' g₁ g₂ := by
     ext l
-    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
+    simp [smul_smul, TensorProduct.map_map, valLinEquiv_symm_apply]
     ring_nf
 
 /-- The gauge action on a pure spinor–weak tensor. -/
-- 
2.55.0

-/

