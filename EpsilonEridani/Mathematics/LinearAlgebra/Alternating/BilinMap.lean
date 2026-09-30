/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The bilinear map of an alternating map with all but two arguments fixed

Fixing the last `n` arguments `m` of an alternating map `f` in `n + 2` variables leaves the
bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`. It inherits alternation from `f`, and it
vanishes as soon as either argument is one of the fixed vectors.

For `n = 2` and `f` a volume form `ε` on a four-dimensional space this is the contraction
`ε_{μναβ} a^α b^β` of the Levi-Civita tensor with two momenta, the tensor structure of the
parity-odd parts of the leptonic and hadronic tensors of deep-inelastic scattering. On a space
of dimension less than four every alternating map in four variables vanishes, so that structure
needs four dimensions.

## Main definitions

- `AlternatingMap.bilinMap`: the bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`.

## Main results

- `AlternatingMap.isAlt_bilinMap`: `f.bilinMap m` is alternating.
- `AlternatingMap.bilinMap_swap`: consequently it is antisymmetric.
- `AlternatingMap.bilinMap_apply_left_eq_zero`, `AlternatingMap.bilinMap_apply_right_eq_zero`:
  it vanishes when either argument is one of the fixed vectors `m i`.
- `AlternatingMap.eq_zero_of_finrank_lt_card`: an alternating map in more variables than the
  dimension of its domain is zero.
-/

public section

namespace AlternatingMap

section CommSemiring

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {n : ℕ}

/-- The bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))` obtained from an alternating map
`f` in `n + 2` variables by fixing its last `n` arguments to `m`. -/
def bilinMap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) : LinearMap.BilinMap R M N :=
  LinearMap.mk₂ R (fun v w => f (Matrix.vecCons v (Matrix.vecCons w m)))
    (fun _ _ _ => f.map_vecCons_add _ _ _)
    (fun _ _ _ => f.map_vecCons_smul _ _ _)
    (fun v _ _ => (f.curryLeft v).map_vecCons_add m _ _)
    (fun _ v _ => (f.curryLeft v).map_vecCons_smul m _ _)

/-- Pointwise value of `f.bilinMap m`. -/
theorem bilinMap_apply (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (v w : M) :
    f.bilinMap m v w = f (Matrix.vecCons v (Matrix.vecCons w m)) :=
  (rfl)

/-- `f.bilinMap m` vanishes on the diagonal. -/
@[simp]
theorem bilinMap_apply_self (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (v : M) :
    f.bilinMap m v v = 0 :=
  f.map_eq_zero_of_eq _ (i := 0) (j := 1) (by simp) Fin.zero_ne_one

/-- `f.bilinMap m` is alternating. -/
theorem isAlt_bilinMap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) :
    (f.bilinMap m).IsAlt :=
  f.bilinMap_apply_self m

/-- `f.bilinMap m` vanishes when its first argument is one of the fixed vectors. -/
theorem bilinMap_apply_left_eq_zero (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M)
    (i : Fin n) (w : M) : f.bilinMap m (m i) w = 0 :=
  f.map_eq_zero_of_eq _ (i := 0) (j := i.succ.succ) (by simp) (Fin.succ_ne_zero _).symm

/-- `f.bilinMap m` vanishes when its second argument is one of the fixed vectors. -/
theorem bilinMap_apply_right_eq_zero (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M)
    (i : Fin n) (v : M) : f.bilinMap m v (m i) = 0 :=
  f.map_eq_zero_of_eq _ (i := 1) (j := i.succ.succ) (by simp)
    (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero _).symm)

/-- The zero alternating map gives the zero bilinear map. -/
@[simp]
theorem bilinMap_zero (m : Fin n → M) : (0 : M [⋀^Fin (n + 2)]→ₗ[R] N).bilinMap m = 0 := by
  ext
  rfl

/-- `AlternatingMap.bilinMap` is additive in the alternating map. -/
@[simp]
theorem bilinMap_add (f g : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) :
    (f + g).bilinMap m = f.bilinMap m + g.bilinMap m := by
  ext
  rfl

/-- `AlternatingMap.bilinMap` commutes with scalar multiplication of the alternating map. -/
@[simp]
theorem bilinMap_smul (c : R) (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) :
    (c • f).bilinMap m = c • f.bilinMap m := by
  ext
  rfl

end CommSemiring

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- `f.bilinMap m` is antisymmetric. -/
theorem bilinMap_swap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (v w : M) :
    f.bilinMap m w v = -f.bilinMap m v w :=
  ((f.isAlt_bilinMap m).neg v w).symm

end CommRing

section DivisionRing

variable {K M N ι : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [Fintype ι]

/-- An alternating map in more variables than the dimension of its domain is zero: its
arguments are always linearly dependent. -/
theorem eq_zero_of_finrank_lt_card [Module.Finite K M] (f : M [⋀^ι]→ₗ[K] N)
    (h : Module.finrank K M < Fintype.card ι) : f = 0 := by
  ext v
  exact f.map_linearDependent v fun hv => (hv.fintype_card_le_finrank.trans_lt h).false

end DivisionRing

end AlternatingMap
