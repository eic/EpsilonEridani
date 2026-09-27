import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic


/-


TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0007-feat-Mathematics-Relativity-generalized-Kronecker-de.patch
@@ -6,6 +6,9 @@ Authors: Robert Sneiderman, Joseph Tooby-Smith
 module
 
 public import EpsilonEridani.Relativity.Tensors.RealTensor.Contraction.CrossToEnd
+public import EpsilonEridani.Relativity.Tensors.RealTensor.Basic
+public import EpsilonEridani.Relativity.Tensors.MetricTensor
+public import EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita
  /-!
 
 ## Metrics as real Lorentz tensors
@@ -18,11 +21,15 @@ open Module
 open Matrix
 open MatrixGroups
 open TensorProduct
+open Equiv
+open TensorSpecies Tensor
 
 noncomputable section
 
 namespace realLorentzTensor
 
+open realLorentzTensor
+
  /-!
 
 ## Definitions.
@@ -30,12 +37,17 @@ namespace realLorentzTensor
  /
 
 /-- The metric `ηᵢᵢ` as a complex Lorentz tensor. -/
-abbrev coMetric (d : ℕ := 3) : ℝT[d, .down, .down] :=
-  (realLorentzTensor d).metricTensor .down
+abbrev coMetric (d : ℕ := 3) : ℝT[d, Color.down, Color.down] :=
+  (realLorentzTensor d).metricTensor Color.down
 
 /-- The metric `ηⁱⁱ` as a complex Lorentz tensor. -/
-abbrev contrMetric (d : ℕ := 3) : ℝT[d, .up, .up] :=
-  (realLorentzTensor d).metricTensor .up
+abbrev contrMetric (d : ℕ := 3) : ℝT[d, Color.up, Color.up] :=
+  (realLorentzTensor d).metricTensor Color.up
+
+/-- The mixed Kronecker delta (identity tensor) `δ^ρ_σ = η^{ρλ} η_{λσ}`.
+This is 1 when ρ = σ and 0 otherwise. -/
+def kroneckerDelta (d : ℕ := 3) : ℝT[d, Color.up, Color.down] :=
+  fromConstPair ((realLorentzTensor d).unit Color.down)
 
  /-!
 
@@ -57,6 +69,26 @@ scoped[realLorentzTensor] notation "η" => @contrMetric
 open TensorSpecies
 open Tensor
 
+/- The covariant rank-4 Levi-Civita tensor in 3+1 dimensions. -/
+/-
+noncomputable def leviCivita4Co : ℝT[.down, .down, .down, .down] :=
+  (Tensor.basis (S := realLorentzTensor 3)
+      ![Color.down, Color.down, Color.down, Color.down]).repr.symm <|
+    (Finsupp.linearEquivFunOnFinite ℝ ℝ ((j : Fin 4) → Fin 1 ⊕ Fin 3)).symm <|
+      fun j => (leviCivita4Int (finSumFinEquiv (j 0)) (finSumFinEquiv (j 1))
+        (finSumFinEquiv (j 2)) (finSumFinEquiv (j 3)) : ℝ)
+
+@[simp]
+lemma leviCivita4Co_basis_repr_apply
+    (b : ComponentIdx (S := realLorentzTensor 3)
+      ![Color.down, Color.down, Color.down, Color.down]) :
+    (Tensor.basis (S := realLorentzTensor 3)
+      ![Color.down, Color.down, Color.down, Color.down]).repr leviCivita4Co b =
+      (leviCivita4Int (finSumFinEquiv (b 0)) (finSumFinEquiv (b 1))
+        (finSumFinEquiv (b 2)) (finSumFinEquiv (b 3)) : ℝ) := by
+  simp [leviCivita4Co]
+-/
+
 lemma coMetric_eq_fromConstPair {d : ℕ} :
     η' d = fromConstPair (S := realLorentzTensor d) (c1 := .down) (c2 := .down)
       (Lorentz.preCoMetric d) := by
diff --git a/EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/LeviCivita.lean
b/EpsilonEridani/Relativity/Tensors/RealTensor/Metrics/LeviCivita.lean
new file mode 100644
index 00000000..0454235a
--- /dev/null
-/

