import Physlib.Relativity.Fermions.Weyl.DualRightHanded


/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0094-fix-Weyl-repair-the-four-Weyl-rep-definitions.patch
@@ -122,18 +122,19 @@ def rep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
       DualRightHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
     map_add' := by
       intro ψ ψ'
-      simp [mulVec_add]
+      simp only [toFin2ℂ, map_add, mulVec_add]
     map_smul' := by
       intro r ψ
-      simp [mulVec_smul]}
+      simp only [toFin2ℂ, map_smul, mulVec_smul, RingHom.id_apply]}
   map_one' := by
     ext i
     simp
   map_mul' := fun M N => by
     ext1 x
-    simp only [SpecialLinearGroup.coe_mul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
+    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
       LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
     refine (congrFun (congrArg _ ?_) _)
+    show ((M.1 * N.1)⁻¹).conjTranspose = _
     rw [Matrix.mul_inv_rev]
     exact conjTranspose_mul _ _
 
diff --git a/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
b/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
index c7136388..5ab09bf3 100644
--- a/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
-/

/-
-- Patch: 0095-docs-Weyl-record-why-the-simp-sets-are-restricted-an.patch
@@ -120,6 +120,11 @@ def rep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
   toFun := fun M => {
     toFun := fun (ψ : DualRightHandedWeyl) =>
       DualRightHandedWeyl.toFin2ℂEquiv.symm ((M.1⁻¹).conjTranspose *ᵥ ψ.toFin2ℂ),
+    -- `simp only` rather than `simp` in both fields below. `Matrix.mulVec_fin_two` is a global
+    -- `@[simp]` lemma (Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean) that
+    -- rewrites `*ᵥ` on any `Fin 2` matrix into an explicit `![…]` literal. It fires before
+    -- `mulVec_add`/`mulVec_smul` can, leaving a componentwise goal the default simp set cannot
+    -- close. Do not relax these to `simp`.
     map_add' := by
       intro ψ ψ'
       simp only [toFin2ℂ, map_add, mulVec_add]
@@ -134,6 +139,10 @@ def rep : Representation ℂ SL(2,ℂ) DualRightHandedWeyl where
     simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
       LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
     refine (congrFun (congrArg _ ?_) _)
+    -- The explicit `show` is load-bearing, not cosmetic. `Matrix.SpecialLinearGroup` is a
+    -- semireducible `def` for a subtype, so `(M * N).1` is type-correct only at default
+    -- transparency; `simp only [SpecialLinearGroup.coe_mul]` therefore silently fails to
+    -- fire on it. Stating the equation directly sidesteps that coercion.
     show ((M.1 * N.1)⁻¹).conjTranspose = _
     rw [Matrix.mul_inv_rev]
     exact conjTranspose_mul _ _
diff --git a/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
b/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
index 5ab09bf3..5de71230 100644
--- a/EpsilonEridani/Relativity/Fermions/Weyl/LeftHanded.lean
-/

