/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.Nondegenerate
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# The bilinear map of an alternating map with all but two arguments fixed

Fixing the last `n` arguments `m` of an alternating map `f` in `n + 2` variables leaves the
bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`. It inherits alternation from `f`, it
vanishes as soon as either argument is one of the fixed vectors, and it is antisymmetric in the
fixed vectors.

When `f` is scalar-valued on a finite-dimensional space over a field and `B` is a nondegenerate
bilinear form, the second index of `f.bilinMap m` can be raised with `B`
(`LinearMap.BilinForm.symmCompOfNondegenerate`): this is the endomorphism `f.bilinMapRaise m hB`,
the `E` with `B (E v) w = f (v, w, m 0, …, m (n - 1))`.

For `n = 2` and `f` a volume form `ε` on a four-dimensional space this is the contraction
`ε_{μναβ} a^α b^β` of the Levi-Civita tensor with two momenta, the tensor structure of the
parity-odd parts of the leptonic and hadronic tensors of deep-inelastic scattering.

## Main definitions

- `AlternatingMap.bilinMap`: the bilinear map `(v, w) ↦ f (v, w, m 0, …, m (n - 1))`.
- `AlternatingMap.bilinMapRaise`: its second index raised by a nondegenerate bilinear form.

## Main results

- `AlternatingMap.isAlt_bilinMap`: `f.bilinMap m` is alternating.
- `AlternatingMap.bilinMap_apply_left_eq_zero`, `AlternatingMap.bilinMap_apply_right_eq_zero`:
  it vanishes when either argument is one of the fixed vectors `m i`.
- `AlternatingMap.bilinMap_eq_zero_of_eq`, `AlternatingMap.bilinMap_comp_swap`: it vanishes when
  two fixed vectors coincide, and changes sign when two fixed vectors are exchanged.
- `AlternatingMap.bilinMap_smul`: it is homogeneous in `f`.
- `AlternatingMap.bilinForm_bilinMapRaise_apply`, `AlternatingMap.eq_bilinMapRaise_iff`: the
  characteristic property `B (f.bilinMapRaise m hB v) w = f.bilinMap m v w` of the raised map,
  which determines it.
- `AlternatingMap.bilinMapRaise_apply_eq_zero`: the raised map kills the fixed vectors.
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

/-- `f.bilinMap m` vanishes when two of the fixed vectors coincide. -/
theorem bilinMap_eq_zero_of_eq (f : M [⋀^Fin (n + 2)]→ₗ[R] N) {m : Fin n → M} {i j : Fin n}
    (h : m i = m j) (hij : i ≠ j) : f.bilinMap m = 0 := by
  ext v w
  exact f.map_eq_zero_of_eq _ (i := i.succ.succ) (j := j.succ.succ) (by simpa using h)
    (by simpa using hij)

/-- `f.bilinMap m` is homogeneous in `f`: scaling the alternating map scales the bilinear map. -/
theorem bilinMap_smul (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) (c : R) :
    (c • f).bilinMap m = c • f.bilinMap m := by
  ext v w
  simp [bilinMap_apply]

end CommSemiring

section AddCommGroup

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

/-- `f.bilinMap m` changes sign when two of the fixed vectors are exchanged. -/
theorem bilinMap_comp_swap (f : M [⋀^Fin (n + 2)]→ₗ[R] N) (m : Fin n → M) {i j : Fin n}
    (hij : i ≠ j) : f.bilinMap (m ∘ Equiv.swap i j) = -f.bilinMap m := by
  ext v w
  have h : Matrix.vecCons v (Matrix.vecCons w (m ∘ Equiv.swap i j)) =
      Matrix.vecCons v (Matrix.vecCons w m) ∘ Equiv.swap i.succ.succ j.succ.succ := by
    funext k
    refine Fin.cases ?_ (Fin.cases ?_ fun k => ?_) k
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm
        (Fin.succ_ne_zero _).symm]
      rfl
    · rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne
        ((Fin.succ_injective _).ne (Fin.succ_ne_zero _)).symm
        ((Fin.succ_injective _).ne (Fin.succ_ne_zero _)).symm]
      rfl
    · rw [Function.comp_apply, (Fin.succ_injective _).swap_apply,
        (Fin.succ_injective _).swap_apply]
      simp
  rw [bilinMap_apply, h, f.map_swap _ (by simpa using hij), LinearMap.neg_apply,
    LinearMap.neg_apply, bilinMap_apply]

end AddCommGroup

section Field

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M] {n : ℕ}
  {B : LinearMap.BilinForm K M}

/-- The bilinear form `f.bilinMap m` with its second index raised by a nondegenerate bilinear form
`B`: the endomorphism `E` with `B (E v) w = f (v, w, m 0, …, m (n - 1))`. -/
noncomputable def bilinMapRaise (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) : M →ₗ[K] M :=
  LinearMap.BilinForm.symmCompOfNondegenerate (f.bilinMap m) B hB

/-- Unfolding lemma for `bilinMapRaise`, whose body is not exposed. -/
theorem bilinMapRaise_def (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) :
    f.bilinMapRaise m hB = LinearMap.BilinForm.symmCompOfNondegenerate (f.bilinMap m) B hB :=
  (rfl)

/-- The characteristic property of `f.bilinMapRaise m hB`: `B (E v) w = f.bilinMap m v w`. -/
@[simp]
theorem bilinForm_bilinMapRaise_apply (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) (v w : M) : B (f.bilinMapRaise m hB v) w = f.bilinMap m v w :=
  LinearMap.BilinForm.symmCompOfNondegenerate_left_apply _ hB w v

/-- `f.bilinMapRaise m hB v` is the unique vector `u` with `B u w = f.bilinMap m v w` for all
`w`. -/
theorem eq_bilinMapRaise_iff (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) {u v : M} :
    u = f.bilinMapRaise m hB v ↔ ∀ w, B u w = f.bilinMap m v w :=
  LinearMap.BilinForm.eq_symmCompOfNondegenerate_iff _ hB

/-- The raised map kills the fixed vectors. -/
@[simp]
theorem bilinMapRaise_apply_eq_zero (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) (i : Fin n) : f.bilinMapRaise m hB (m i) = 0 :=
  ((f.eq_bilinMapRaise_iff m hB).2 fun w => by simp).symm

/-- The raised map vanishes when two of the fixed vectors coincide. -/
theorem bilinMapRaise_eq_zero_of_eq (f : M [⋀^Fin (n + 2)]→ₗ[K] K) {m : Fin n → M}
    (hB : B.Nondegenerate) {i j : Fin n} (h : m i = m j) (hij : i ≠ j) :
    f.bilinMapRaise m hB = 0 := by
  ext v
  refine ((f.eq_bilinMapRaise_iff m hB).2 fun w => ?_).symm
  simp [f.bilinMap_eq_zero_of_eq h hij]

/-- The raised map changes sign when two of the fixed vectors are exchanged. -/
theorem bilinMapRaise_comp_swap (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) {i j : Fin n} (hij : i ≠ j) :
    f.bilinMapRaise (m ∘ Equiv.swap i j) hB = -f.bilinMapRaise m hB := by
  ext v
  refine ((f.eq_bilinMapRaise_iff _ hB).2 fun w => ?_).symm
  simp [f.bilinMap_comp_swap m hij]

/-- The raised map is homogeneous in `f`. -/
theorem bilinMapRaise_smul (f : M [⋀^Fin (n + 2)]→ₗ[K] K) (m : Fin n → M)
    (hB : B.Nondegenerate) (c : K) :
    (c • f).bilinMapRaise m hB = c • f.bilinMapRaise m hB := by
  ext v
  refine ((eq_bilinMapRaise_iff _ m hB).2 fun w => ?_).symm
  simp [bilinMap_smul]

end Field

end AlternatingMap
