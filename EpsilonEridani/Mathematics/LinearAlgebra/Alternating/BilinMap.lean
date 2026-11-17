/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The bilinear map of an alternating map with all but two arguments fixed

Fixing the last `n` arguments `m` of an alternating map `f` in `n + 2` variables leaves the
bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`. It inherits alternation from `f`, and it
vanishes as soon as either argument is one of the fixed vectors.

For `n = 2` and `f` a volume form `ε` on a four-dimensional space this is the contraction
`ε_{μναβ} a^α b^β` of the Levi-Civita tensor with two momenta, the tensor structure of the
parity-odd parts of the leptonic and hadronic tensors of deep-inelastic scattering.

## Main definitions

- `AlternatingMap.bilinMap`: the bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`.

## Main results

- `AlternatingMap.isAlt_bilinMap`: `f.bilinMap m` is alternating.
- `AlternatingMap.bilinMap_apply_left_eq_zero`, `AlternatingMap.bilinMap_apply_right_eq_zero`:
  it vanishes when either argument is one of the fixed vectors `m i`.
- `AlternatingMap.neg_bilinMap`, `AlternatingMap.bilinMap_update_neg`,
  `AlternatingMap.bilinMap_pair_neg_snd`: it changes sign when `f` or one fixed vector is negated.
- `AlternatingMap.bilinMap_update_smul`, `AlternatingMap.bilinMap_update_add`,
  `AlternatingMap.bilinMap_update_sub`, `AlternatingMap.bilinMap_pair_smul_snd`,
  `AlternatingMap.bilinMap_pair_add_snd`, `AlternatingMap.bilinMap_pair_sub_snd`: it is linear in
  each fixed vector.
-/

public section

namespace AlternatingMap

/-- `Fin.cons_update` for `Matrix.vecCons`: an update of the tail moves out through `vecCons`. -/
private theorem vecCons_update {α : Type*} {n : ℕ} (x : α) (p : Fin n → α) (i : Fin n) (y : α) :
    Matrix.vecCons x (Function.update p i y) = Function.update (Matrix.vecCons x p) i.succ y :=
  Fin.cons_update (α := fun _ => α) x p i y

/-- A pair with a replaced second entry is an update of the original pair. -/
private theorem vecCons_pair_eq_update {α : Type*} (a b x : α) :
    ![a, x] = Function.update ![a, b] 1 x := by
  ext i
  fin_cases i <;> simp

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
    f.bilinMap m v v = 0 := by
  rw [bilinMap_apply, ← curryLeft_apply_apply, ← curryLeft_apply_apply]
  exact DFunLike.congr_fun (f.curryLeft_same v) m

/-- `f.bilinMap m` is alternating. -/
theorem isAlt_bilinMap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) :
    (f.bilinMap m).IsAlt :=
  f.bilinMap_apply_self m

/-- `f.bilinMap m` vanishes when its first argument is one of the fixed vectors. -/
@[simp]
theorem bilinMap_apply_left_eq_zero (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M)
    (i : Fin n) (w : M) : f.bilinMap m (m i) w = 0 :=
  f.map_eq_zero_of_eq _ (i := 0) (j := i.succ.succ) (by simp) (Fin.succ_ne_zero _).symm

/-- `f.bilinMap m` vanishes when its second argument is one of the fixed vectors. -/
@[simp]
theorem bilinMap_apply_right_eq_zero (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M)
    (i : Fin n) (v : M) : f.bilinMap m v (m i) = 0 :=
  f.map_eq_zero_of_eq _ (i := 1) (j := i.succ.succ) (by simp)
    (Fin.succ_zero_eq_one ▸ (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero _).symm))

/-- Scaling one fixed vector scales the bilinear map. -/
theorem bilinMap_update_smul (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (i : Fin n)
    (r : R) (x : M) :
    f.bilinMap (Function.update m i (r • x)) = r • f.bilinMap (Function.update m i x) := by
  ext v w
  simp only [bilinMap_apply, LinearMap.smul_apply, vecCons_update, f.map_update_smul]

/-- Adding in one fixed vector adds the bilinear maps. -/
theorem bilinMap_update_add (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (i : Fin n)
    (x y : M) :
    f.bilinMap (Function.update m i (x + y)) =
      f.bilinMap (Function.update m i x) + f.bilinMap (Function.update m i y) := by
  ext v w
  simp only [bilinMap_apply, LinearMap.add_apply, vecCons_update, f.map_update_add]

/-- Scaling the second of two fixed vectors scales the bilinear map. -/
@[simp]
theorem bilinMap_pair_smul_snd (f : M [⋀^Fin 4]→ₗ[R] N) (a b : M) (r : R) :
    f.bilinMap ![a, r • b] = r • f.bilinMap ![a, b] := by
  rw [vecCons_pair_eq_update a b (r • b), bilinMap_update_smul, ← vecCons_pair_eq_update]

/-- Adding in the second of two fixed vectors adds the bilinear maps. -/
@[simp]
theorem bilinMap_pair_add_snd (f : M [⋀^Fin 4]→ₗ[R] N) (a b c : M) :
    f.bilinMap ![a, b + c] = f.bilinMap ![a, b] + f.bilinMap ![a, c] := by
  rw [vecCons_pair_eq_update a b (b + c), bilinMap_update_add, ← vecCons_pair_eq_update,
    ← vecCons_pair_eq_update]

end CommSemiring

section AddCommGroupCodomain

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- Negating the alternating map negates its bilinear map. -/
@[simp]
theorem neg_bilinMap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) :
    (-f).bilinMap m = -f.bilinMap m :=
  LinearMap.ext₂ fun v w => by
    simp only [bilinMap_apply, neg_apply, LinearMap.neg_apply]

end AddCommGroupCodomain

section AddCommGroupDomain

variable {R M N : Type*} [CommSemiring R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- Negating one fixed vector negates the bilinear map. -/
theorem bilinMap_update_neg (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (i : Fin n) :
    f.bilinMap (Function.update m i (-m i)) = -f.bilinMap m := by
  ext v w
  -- Write `m` as `update m i (m i)` so that both sides carry the update.
  conv_rhs => rw [← Function.update_eq_self i m]
  simp only [bilinMap_apply, LinearMap.neg_apply, vecCons_update, f.map_update_neg]

/-- Negating the second of two fixed vectors negates the bilinear map. -/
@[simp]
theorem bilinMap_pair_neg_snd (f : M [⋀^Fin 4]→ₗ[R] N) (a b : M) :
    f.bilinMap ![a, -b] = -f.bilinMap ![a, b] := by
  rw [vecCons_pair_eq_update a b (-b)]
  exact f.bilinMap_update_neg ![a, b] 1

/-- Subtracting in one fixed vector subtracts the bilinear maps. -/
theorem bilinMap_update_sub (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (i : Fin n)
    (x y : M) :
    f.bilinMap (Function.update m i (x - y)) =
      f.bilinMap (Function.update m i x) - f.bilinMap (Function.update m i y) := by
  ext v w
  simp only [bilinMap_apply, LinearMap.sub_apply, vecCons_update, f.map_update_sub]

/-- Subtracting in the second of two fixed vectors subtracts the bilinear maps. -/
@[simp]
theorem bilinMap_pair_sub_snd (f : M [⋀^Fin 4]→ₗ[R] N) (a b c : M) :
    f.bilinMap ![a, b - c] = f.bilinMap ![a, b] - f.bilinMap ![a, c] := by
  rw [vecCons_pair_eq_update a b (b - c), bilinMap_update_sub, ← vecCons_pair_eq_update,
    ← vecCons_pair_eq_update]

end AddCommGroupDomain

end AlternatingMap
