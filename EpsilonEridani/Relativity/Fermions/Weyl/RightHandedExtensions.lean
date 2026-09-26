import Physlib.Relativity.Fermions.Weyl.RightHanded

/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0094-fix-Weyl-repair-the-four-Weyl-rep-definitions.patch
@@ -118,17 +118,20 @@ def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
       RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
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
-    simp only [SpecialLinearGroup.coe_mul, RCLike.star_def, Matrix.map_mul, LinearMap.coe_mk,
-      AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply, mulVec_mulVec]
+    simp only [RCLike.star_def, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
+      LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
+    refine congrFun (congrArg _ ?_) _
+    show (M.1 * N.1).map ⇑(starRingEnd ℂ) = _
+    exact Matrix.map_mul
 
 lemma rep_apply (M : SL(2,ℂ)) (ψ : RightHandedWeyl) : rep M ψ = ⟨M.1.map star *ᵥ ψ.1⟩ := rfl
 
-- 
2.55.0

-/

/-
-- Patch: 0095-docs-Weyl-record-why-the-simp-sets-are-restricted-an.patch
@@ -116,6 +116,11 @@ def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
   toFun := fun M => {
     toFun := fun (ψ : RightHandedWeyl) =>
       RightHandedWeyl.toFin2ℂEquiv.symm (M.1.map star *ᵥ ψ.toFin2ℂ),
+    -- `simp only` rather than `simp` in both fields below. `Matrix.mulVec_fin_two` is a global
+    -- `@[simp]` lemma (Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean) that
+    -- rewrites `*ᵥ` on any `Fin 2` matrix into an explicit `![…]` literal. It fires before
+    -- `mulVec_add`/`mulVec_smul` can, leaving a componentwise goal the default simp set cannot
+    -- close. Do not relax these to `simp`.
     map_add' := by
       intro ψ ψ'
       simp only [toFin2ℂ, map_add, mulVec_add]
@@ -130,6 +135,10 @@ def rep : Representation ℂ SL(2,ℂ) RightHandedWeyl where
     simp only [RCLike.star_def, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
       LinearEquiv.apply_symm_apply, mulVec_mulVec, EmbeddingLike.apply_eq_iff_eq]
     refine congrFun (congrArg _ ?_) _
+    -- The explicit `show` is load-bearing, not cosmetic. `Matrix.SpecialLinearGroup` is a
+    -- semireducible `def` for a subtype, so `(M * N).1` is type-correct only at default
+    -- transparency; `simp only [SpecialLinearGroup.coe_mul]` therefore silently fails to
+    -- fire on it. Stating the equation directly sidesteps that coercion.
     show (M.1 * N.1).map ⇑(starRingEnd ℂ) = _
     exact Matrix.map_mul
 
-- 
2.55.0

-/

