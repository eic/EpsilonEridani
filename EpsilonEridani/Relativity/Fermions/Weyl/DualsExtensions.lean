import Physlib.Relativity.Fermions.Weyl.Duals

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0098-fix-Weyl-stop-relying-on-SpecialLinearGroup.coe_inv-.patch
@@ -55,11 +55,17 @@ def LeftHandedWeyl.dual : LeftHandedWeyl.rep.IntertwiningMap DualLeftHandedWeyl.
     change DualLeftHandedWeyl.toFin2ℂEquiv.symm (!![0, 1; -1, 0] *ᵥ M.1 *ᵥ ψ.val) =
       DualLeftHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹)ᵀ *ᵥ !![0, 1; -1, 0] *ᵥ ψ.val)
     apply congrArg
-    rw [mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe, eta_fin_two M.1]
+    rw [mulVec_mulVec, mulVec_mulVec]
     refine congrFun (congrArg _ ?_) _
-    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
-    simp
+    -- `Matrix.SpecialLinearGroup` is a semireducible `def` for a subtype, so `M.1⁻¹` is only
+    -- type-correct at default transparency.  `rw`/`simp only` match at reducible transparency
+    -- and `SpecialLinearGroup.coe_inv` therefore never fires on it.  Supplying the coercion
+    -- fact as a *term* elaborates it at default transparency instead; the componentwise
+    -- `ext`/`fin_cases` finish then needs no `eta_fin_two`/`mul_fin_two` massaging.
+    rw [(Lorentz.SL2C.inverse_coe M).trans (Matrix.SpecialLinearGroup.coe_inv M),
+      Matrix.adjugate_fin_two]
+    ext i j
+    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 lemma LeftHandedWeyl.dual_hom_apply (ψ : LeftHandedWeyl) :
     LeftHandedWeyl.dual ψ =
@@ -85,12 +91,17 @@ def DualLeftHandedWeyl.dual : DualLeftHandedWeyl.rep.IntertwiningMap LeftHandedW
     refine LinearMap.ext (fun ψ => ?_)
     change LeftHandedWeyl.toFin2ℂEquiv.symm (!![0, -1; 1, 0] *ᵥ (M.1⁻¹)ᵀ *ᵥ ψ.val) =
       LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ !![0, -1; 1, 0] *ᵥ ψ.val)
-    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec, Lorentz.SL2C.inverse_coe,
-      eta_fin_two M.1]
+    rw [EquivLike.apply_eq_iff_eq, mulVec_mulVec, mulVec_mulVec]
     refine congrFun (congrArg _ ?_) _
-    rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
-      Matrix.mul_fin_two, eta_fin_two !![M.1 1 1, -M.1 0 1; -M.1 1 0, M.1 0 0]ᵀ]
-    simp
+    -- `Matrix.SpecialLinearGroup` is a semireducible `def` for a subtype, so `M.1⁻¹` is only
+    -- type-correct at default transparency.  `rw`/`simp only` match at reducible transparency
+    -- and `SpecialLinearGroup.coe_inv` therefore never fires on it.  Supplying the coercion
+    -- fact as a *term* elaborates it at default transparency instead; the componentwise
+    -- `ext`/`fin_cases` finish then needs no `eta_fin_two`/`mul_fin_two` massaging.
+    rw [(Lorentz.SL2C.inverse_coe M).trans (Matrix.SpecialLinearGroup.coe_inv M),
+      Matrix.adjugate_fin_two]
+    ext i j
+    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
 
 lemma DualLeftHandedWeyl.dual_hom_apply (ψ : DualLeftHandedWeyl) :
     DualLeftHandedWeyl.dual ψ =
diff --git a/EpsilonEridani/Relativity/Fermions/Weyl/Two.lean b/EpsilonEridani/Relativity/Fermions/Weyl/Two.lean
index 5dd1e724..ccd13099 100644
--- a/EpsilonEridani/Relativity/Fermions/Weyl/Two.lean
-/

