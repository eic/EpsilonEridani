import Physlib.Particles.StandardModel.HiggsBoson.Basic


/-
TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0087-fix-StandardModel-make-repGaugeGroupI-compile-agains.patch
@@ -170,14 +170,22 @@ The gauge group of the Standard Model acts on `HiggsVec` by matrix
multiplicatio
 def repGaugeGroupI : Representation ℂ GaugeGroupI HiggsVec where
   toFun g :=
     { toFun φ := WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)
-      map_add' φ ψ := by simp [mulVec_add, smul_add]
-      map_smul' c φ := by simp [mulVec_smul, smul_comm c] }
+      -- `simp only` rather than `simp` here and in `map_mul'` below: the ambient simp set
+      -- contains `Matrix.mulVec_fin_two`, which rewrites `*ᵥ` on `Fin 2` into an explicit
+      -- `![…]` literal before the structural `WithLp`/`mulVec` lemmas can fire.
+      map_add' φ ψ := by
+        simp only [WithLp.ofLp_add, mulVec_add, smul_add, WithLp.toLp_add]
+      map_smul' c φ := by
+        simp only [RingHom.id_apply, WithLp.ofLp_smul, mulVec_smul,
+          smul_comm (g.toU1 ^ 3) c, WithLp.toLp_smul] }
   map_one' := by
     ext φ
     simp
   map_mul' g₁ g₂ := by
-    ext φ
-    simp [Module.End.mul_apply, smul_smul, mulVec_mulVec, mul_pow, mul_comm]
+    refine LinearMap.ext fun φ => ?_
+    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
+      Submonoid.coe_mul, WithLp.ofLp_toLp, mulVec_smul, smul_smul, mulVec_mulVec,
+      mul_pow, mul_comm]
 
 lemma repGaugeGroupI_apply (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
     repGaugeGroupI g φ = (WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)) := rfl
-- 
2.55.0

-/

/-
-- Patch: 0088-style-StandardModel-drop-two-simp-arguments-the-unus.patch
@@ -184,8 +184,7 @@ def repGaugeGroupI : Representation ℂ GaugeGroupI HiggsVec where
   map_mul' g₁ g₂ := by
     refine LinearMap.ext fun φ => ?_
     simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
-      Submonoid.coe_mul, WithLp.ofLp_toLp, mulVec_smul, smul_smul, mulVec_mulVec,
-      mul_pow, mul_comm]
+      Submonoid.coe_mul, mulVec_smul, smul_smul, mulVec_mulVec, mul_pow]
 
 lemma repGaugeGroupI_apply (g : StandardModel.GaugeGroupI) (φ : HiggsVec) :
     repGaugeGroupI g φ = (WithLp.toLp 2 <| g.toU1 ^ 3 • (g.toSU2.1 *ᵥ φ.ofLp)) := rfl
-- 
2.55.0

-/

