import Physlib.Particles.StandardModel.Fermions.DownSinglet

set_option linter.style.longLine false

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0147-fix-StandardModel-drop-mul_comm-from-the-repGaugeGro.patch
@@ -154,7 +154,7 @@ noncomputable def repGaugeGroupI : Representation ℂ GaugeGroupI DownSinglet wh
     simp [valLinEquiv_symm_apply]
   map_mul' g₁ g₂ := by
     ext d
-    simp [smul_smul, mul_comm, TensorProduct.map_map, valLinEquiv_symm_apply]
+    simp [smul_smul, TensorProduct.map_map, valLinEquiv_symm_apply]
     ring_nf
 
 /-- The gauge action on a pure spinor–colour tensor. -/
diff --git a/EpsilonEridani/Particles/StandardModel/Fermions/LeptonDoublet.lean b/EpsilonEridani/Particles/StandardModel/Fermions/LeptonDoublet.lean
index 1c85c5e0..9c89601d 100644
--- a/EpsilonEridani/Particles/StandardModel/Fermions/LeptonDoublet.lean
-/

