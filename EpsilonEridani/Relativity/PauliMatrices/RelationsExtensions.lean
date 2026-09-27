/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Relativity.PauliMatrices.Relations


/-


TODO: The following diffs represent upstream modifications to Physlib.
Port these additions as standalone lemmas/extensions in this file.
-/

/-
-- Patch: 0148-fix-pauli-use-simp-only-for-the-neg-I-rewrite-in-the.patch
@@ -214,7 +214,7 @@ lemma pauliContrDown_mul_pauliContr_mul_pauliContrDown : ({
   simp only [map_add, Finsupp.coe_add, Pi.add_apply]
   simp only [permT_basis_repr_symm_apply, map_neg, Finsupp.coe_neg, Pi.neg_apply,
     map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, ofRat_basis_repr_apply]
-  rw [Physlib.RatComplexNum.neg_I_mul_toComplexNum]
+  simp only [Physlib.RatComplexNum.neg_I_mul_toComplexNum]
   apply Physlib.RatComplexNum.toComplexNum_eq_add_neg_add_add_iff.mpr
   decide +revert +kernel

--
2.55.0

-/

