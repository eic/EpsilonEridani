import Physlib.Relativity.Tensors.LeviCivita.Contractions

set_option linter.style.longLine false

/-

set_option linter.style.longLine false

TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0092-fix-Relativity-LeviCivita-disambiguate-kroneckerDelt.patch
@@ -207,7 +207,10 @@ lemma leviCivita_basis_contract_three (a b : Fin 1 ⊕ Fin 3) :
           (generalizedKroneckerDelta (Fin.snoc g (finSumFinEquiv b)) id : ℝ) :=
       Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 3))
         (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ fun _ => rfl
-    _ = 6 * ((kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) : ℕ) : ℝ) :=
+    -- `KroneckerDelta.` is required: inside `namespace realLorentzTensor` the bare name resolves
+    -- to `realLorentzTensor.kroneckerDelta`, the mixed-index unit *tensor*, not this `ℕ`-valued
+    -- symbol, and the current namespace wins over the `open KroneckerDelta` above.
+    _ = 6 * ((KroneckerDelta.kroneckerDelta (finSumFinEquiv a) (finSumFinEquiv b) : ℕ) : ℝ) :=
       euclidLeviCivita_symbol_contract_one_last _ _
     _ = 6 * (if a = b then 1 else 0) := by
       by_cases hab : a = b
-- 
2.55.0

-/

