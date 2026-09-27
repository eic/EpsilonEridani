import Physlib.Relativity.LorentzGroup.Restricted.FromBoostRotation


/-


TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0093-fix-Relativity-pin-d-and-the-coercion-in-toRotation_.patch
@@ -59,7 +59,8 @@ def toRotation {d} (Λ : LorentzGroup.restricted d) : Rotations d :=
 lemma toRotation_continuous {d} :
     Continuous (toRotation : LorentzGroup.restricted d → Rotations d) := by
   apply Continuous.subtype_mk
-  change Continuous (fun Λ => (generalizedBoost 0 (toVelocity Λ))⁻¹ * Λ)
+  change Continuous (fun Λ : LorentzGroup.restricted d =>
+    (generalizedBoost 0 (toVelocity Λ))⁻¹ * (Λ : LorentzGroup d))
   fun_prop
 
 /-- The homeomorphism from the restricted Lorentz group to the product of
-- 
2.55.0

-/

