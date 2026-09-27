/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Relativity.Fermions.Weyl.LeftHanded


/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0094-fix-Weyl-repair-the-four-Weyl-rep-definitions.patch
@@ -120,18 +120,18 @@ def rep : Representation ℂ SL(2,ℂ) LeftHandedWeyl where
       LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
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
-    simp only [SpecialLinearGroup.coe_mul]
     ext1 x
     simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearEquiv.apply_symm_apply,
       mulVec_mulVec]
+    rfl

 lemma rep_apply (M : SL(2,ℂ)) (ψ : LeftHandedWeyl) : rep M ψ = ⟨M.1 *ᵥ ψ.1⟩ := rfl

diff --git a/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
b/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
index 6a3f1eaf..43f06dcf 100644
--- a/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
-/

/-
-- Patch: 0095-docs-Weyl-record-why-the-simp-sets-are-restricted-an.patch
@@ -118,6 +118,11 @@ def rep : Representation ℂ SL(2,ℂ) LeftHandedWeyl where
   toFun := fun M => {
     toFun := fun (ψ : LeftHandedWeyl) =>
       LeftHandedWeyl.toFin2ℂEquiv.symm (M.1 *ᵥ ψ.toFin2ℂ),
+    -- `simp only` rather than `simp` in both fields below. `Matrix.mulVec_fin_two` is a global
+    -- `@[simp]` lemma (Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean) that
+    -- rewrites `*ᵥ` on any `Fin 2` matrix into an explicit `![…]` literal. It fires before
+    -- `mulVec_add`/`mulVec_smul` can, leaving a componentwise goal the default simp set cannot
+    -- close. Do not relax these to `simp`.
     map_add' := by
       intro ψ ψ'
       simp only [toFin2ℂ, map_add, mulVec_add]
diff --git a/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
b/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
index 43f06dcf..e61188b9 100644
--- a/EpsilonEridani/Relativity/Fermions/Weyl/RightHanded.lean
-/

