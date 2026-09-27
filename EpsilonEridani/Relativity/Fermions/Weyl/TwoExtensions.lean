import Physlib.Relativity.Fermions.Weyl.Two


/-


TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0098-fix-Weyl-stop-relying-on-SpecialLinearGroup.coe_inv-.patch
@@ -797,16 +797,20 @@ lemma dualLeftDualRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2)
     dualLeftDualRightToMatrix.symm (SL2C.toSelfAdjointMap (M.transpose⁻¹) ⟨v, hv⟩) := by
   rw [dualLeftDualRightToMatrix_ρ_symm]
   apply congrArg
-  simp only [SL2C.toSelfAdjointMap_apply_coe, SpecialLinearGroup.coe_inv,
-    SpecialLinearGroup.coe_transpose]
-  congr 1
-  · rw [SL2C.inverse_coe]
-    simp only [SpecialLinearGroup.coe_inv]
-    rw [@adjugate_transpose]
-  · rw [SL2C.inverse_coe]
-    simp only [SpecialLinearGroup.coe_inv]
-    rw [← @adjugate_transpose]
-    rfl
+  -- `Matrix.SpecialLinearGroup` is a semireducible `def` for a subtype, so `M.1⁻¹` and
+  -- `(M.transpose⁻¹).1` are only type-correct at default transparency, and `simp only
+  -- [SpecialLinearGroup.coe_inv]` (which matches at reducible transparency) silently makes no
+  -- progress on them.  Both coercion facts are established here as *terms*, which elaborate at
+  -- default transparency, and only then used as rewrites.  `Matrix.` must stay explicit:
+  -- a bare `SpecialLinearGroup.coe_inv` resolves to `_root_.SpecialLinearGroup` in term position.
+  have hadj : (M.1)⁻¹ = Matrix.adjugate M.1 :=
+    (SL2C.inverse_coe M).trans (Matrix.SpecialLinearGroup.coe_inv M)
+  have hT : ((M.1)⁻¹)ᵀ = (M.transpose⁻¹).1 := by
+    rw [hadj, Matrix.adjugate_transpose]
+    exact (Matrix.SpecialLinearGroup.coe_inv M.transpose).symm
+  have hTH : (((M.1)⁻¹)ᴴ)ᵀ = ((M.transpose⁻¹).1)ᴴ := congrArg Matrix.conjTranspose hT
+  simp only [SL2C.toSelfAdjointMap_apply_coe]
+  rw [hT, hTH]
 
 lemma leftRightToMatrix_ρ_symm_selfAdjoint (v : Matrix (Fin 2) (Fin 2) ℂ)
     (hv : IsSelfAdjoint v) (M : SL(2,ℂ)) :
-- 
2.55.0

-/

