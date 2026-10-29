/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Extensions of the Minkowski product on Lorentz vectors

Facts about `Physlib`'s Minkowski product that the kinematics of an emission process uses: the
expansion of the square of a difference, `⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`,
companion to `Lorentz.Vector.minkowskiProduct_add_self`; the length of the spatial part of a
vector, `√((p⁰)² - ⟪p, p⟫ₘ)`, which is `√((p⁰)² - m²)` on the mass shell `⟪p, p⟫ₘ = m²`; and,
in at least two spatial dimensions, the existence of two vectors on the mass shell with prescribed
energies above the mass and a prescribed angle between their spatial parts.

It also records the symmetry of the Minkowski product as a bilinear form
(`isSymm_toBilinForm_minkowskiProduct`), the witness that supplies the `IsRefl` hypothesis of
the reflexive-form results about light-cone bases in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.

* The Minkowski orthogonal complement of a non-zero causal (time-like or light-like) vector `n`
  contains no time-like vector: every `w` with `⟪n, w⟫ₘ = 0` has `⟪w, w⟫ₘ ≤ 0`
  (`minkowskiProduct_self_nonpos_of_orthogonal_causal`). For light-like `n`, in light-cone
  coordinates adapted to `n` the condition `⟪n, w⟫ₘ = 0` says that one light-cone component of
  `w` vanishes, so that `⟪w, w⟫ₘ = -‖w⊥‖²` is minus the square of the transverse part. This is
  the inequality behind lower bounds on momentum transfers at fixed light-cone momentum
  fractions, such as the minimal momentum transfer of off-forward parton kinematics.
* For two distinct spatial directions `i ≠ j`, the vectors `ofTimeAndTwoSpatial i j x y z =
  x e₀ + y eᵢ + z eⱼ` span a three-dimensional Minkowski subspace on which the Minkowski product
  is the diagonal form `x x' - y y' - z z'` (`minkowskiProduct_ofTimeAndTwoSpatial_eq`). This
  gives explicit configurations, such as light-cone frames, in any spacetime with at least two
  spatial dimensions.
-/

public section

noncomputable section

namespace Lorentz
namespace Vector

open Real InnerProductGeometry
open scoped InnerProductSpace Lorentz.Vector

/-- `⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`. -/
lemma minkowskiProduct_sub_self {d : ℕ} (u v : Vector d) :
    ⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 * ⟪u, v⟫ₘ + ⟪v, v⟫ₘ := by
  simp only [map_sub, _root_.sub_apply]
  rw [minkowskiProduct_symm v u]
  ring

/-- The spatial part of `p` has length `√((p⁰)² - ⟪p, p⟫ₘ)`; on the mass shell `⟪p, p⟫ₘ = m²`
this is `√((p⁰)² - m²)`. -/
lemma norm_spatialPart_eq_sqrt_sq_sub_minkowskiProduct_self {d : ℕ} (p : Vector d) :
    ‖p.spatialPart‖ = √(p.timeComponent ^ 2 - ⟪p, p⟫ₘ) := by
  rw [minkowskiProduct_self_eq_sq_sub, sub_sub_cancel, Real.sqrt_sq (norm_nonneg _)]

end Vector
end Lorentz

namespace EpsilonEridani

open Real InnerProductGeometry Lorentz.Vector
open scoped InnerProductSpace Lorentz.Vector

/-- The vector `x e₀ + y eᵢ + z eⱼ` built from the time direction and the spatial directions
`i` and `j`. -/
def ofTimeAndTwoSpatial {d : ℕ} (i j : Fin d) (x y z : ℝ) : Lorentz.Vector d :=
  x • Lorentz.Vector.basis (Sum.inl 0) + y • Lorentz.Vector.basis (Sum.inr i) +
  z • Lorentz.Vector.basis (Sum.inr j)

lemma ofTimeAndTwoSpatial_def {d : ℕ} (i j : Fin d) (x y z : ℝ) :
    ofTimeAndTwoSpatial i j x y z =
      x • Lorentz.Vector.basis (Sum.inl 0) + y • Lorentz.Vector.basis (Sum.inr i) +
      z • Lorentz.Vector.basis (Sum.inr j) := (rfl)

@[simp]
lemma timeComponent_ofTimeAndTwoSpatial_eq {d : ℕ} (i j : Fin d) (x y z : ℝ) :
    (ofTimeAndTwoSpatial i j x y z).timeComponent = x := by
  simp [ofTimeAndTwoSpatial_def]

@[simp]
lemma spatialPart_ofTimeAndTwoSpatial_eq {d : ℕ} (i j : Fin d) (x y z : ℝ) :
    (ofTimeAndTwoSpatial i j x y z).spatialPart =
      y • EuclideanSpace.basisFun (Fin d) ℝ i + z • EuclideanSpace.basisFun (Fin d) ℝ j := by
  ext k
  simp [ofTimeAndTwoSpatial_def, basis_apply, eq_comm]

/-- For distinct spatial directions the Minkowski product of two vectors
`x e₀ + y eᵢ + z eⱼ` and `x' e₀ + y' eᵢ + z' eⱼ` is `x x' - y y' - z z'`. -/
@[simp]
lemma minkowskiProduct_ofTimeAndTwoSpatial_eq {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (x y z x' y' z' : ℝ) :
    ⟪ofTimeAndTwoSpatial i j x y z, ofTimeAndTwoSpatial i j x' y' z'⟫ₘ =
      x * x' - y * y' - z * z' := by
  simp only [ofTimeAndTwoSpatial_def, map_add, map_smul, add_apply, smul_apply,
    minkowskiProduct_basis_left, minkowskiMatrix.inl_0_inl_0, basis_apply, ↓reduceIte, mul_one,
    reduceCtorEq, mul_zero, add_zero, smul_eq_mul, minkowskiMatrix.inr_i_inr_i, zero_add,
    Sum.inr.injEq, hij.symm, mul_neg, hij]
  ring

@[simp]
lemma ofTimeAndTwoSpatial_sub_ofTimeAndTwoSpatial_eq {d : ℕ} (i j : Fin d)
    (x y z x' y' z' : ℝ) :
    ofTimeAndTwoSpatial i j x y z - ofTimeAndTwoSpatial i j x' y' z' =
      ofTimeAndTwoSpatial i j (x - x') (y - y') (z - z') := by
  simp only [ofTimeAndTwoSpatial_def, sub_smul]
  abel

/-- In at least two spatial dimensions, for energies `E`, `E'` above `|m|` and an angle
`θ ∈ [0, π]`, there are two vectors on the mass shell `⟪p, p⟫ₘ = m²` with time components `E` and
`E'` whose spatial parts make the angle `θ`. -/
lemma exists_massShell_pair_angle_eq {d : ℕ} (hd : 2 ≤ d) {m E E' θ : ℝ} (hE : |m| < E)
    (hE' : |m| < E') (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    ∃ p p' : Lorentz.Vector d, ⟪p, p⟫ₘ = m ^ 2 ∧ ⟪p', p'⟫ₘ = m ^ 2 ∧ p.timeComponent = E ∧
      p'.timeComponent = E' ∧ angle p.spatialPart p'.spatialPart = θ := by
  -- the spatial parts are `P e₀` and `P' (cos θ e₀ + sin θ e₁)`, with `e₀ ⊥ e₁` unit vectors
  set P := √(E ^ 2 - m ^ 2)
  set P' := √(E' ^ 2 - m ^ 2)
  have hPsq : P ^ 2 = E ^ 2 - m ^ 2 := Real.sq_sqrt (by nlinarith [sq_abs m, abs_nonneg m])
  have hP'sq : P' ^ 2 = E' ^ 2 - m ^ 2 := Real.sq_sqrt (by nlinarith [sq_abs m, abs_nonneg m])
  have hP : 0 < P := Real.sqrt_pos.2 (by nlinarith [sq_abs m, abs_nonneg m])
  have hP' : 0 < P' := Real.sqrt_pos.2 (by nlinarith [sq_abs m, abs_nonneg m])
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let e₀ := b ⟨0, by omega⟩
  let e₁ := b ⟨1, by omega⟩
  let u := cos θ • e₀ + sin θ • e₁
  have he₀ : ‖e₀‖ = 1 := b.orthonormal.1 _
  have he₁ : ‖e₁‖ = 1 := b.orthonormal.1 _
  have he₀₁ : ⟪e₀, e₁⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
  have hu₀ : ⟪e₀, u⟫_ℝ = cos θ := by
    simp [u, inner_add_right, inner_smul_right, he₀, he₀₁]
  have hu : ‖u‖ = 1 := by
    have horth : ⟪cos θ • e₀, sin θ • e₁⟫_ℝ = 0 := by
      simp [inner_smul_left, inner_smul_right, he₀₁]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    simp only [norm_smul, he₀, he₁, Real.norm_eq_abs] at h
    have h1 : ‖u‖ * ‖u‖ = 1 := by
      simp only [u]
      nlinarith [sq_abs (cos θ), sq_abs (sin θ), sin_sq_add_cos_sq θ]
    nlinarith [norm_nonneg u]
  let p := ofTimeAndTwoSpatial (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ E P 0
  let p' := ofTimeAndTwoSpatial (⟨0, by omega⟩ : Fin d) ⟨1, by omega⟩ E' (P' * cos θ) (P' * sin θ)
  have hps : p.spatialPart = P • e₀ := by simp [p, e₀, b]
  have hp's : p'.spatialPart = P' • u := by
    simp only [p', spatialPart_ofTimeAndTwoSpatial_eq, u, e₀, e₁, b]
    module
  have hpt : p.timeComponent = E := timeComponent_ofTimeAndTwoSpatial_eq ..
  have hp't : p'.timeComponent = E' := timeComponent_ofTimeAndTwoSpatial_eq ..
  refine ⟨p, p', ?_, ?_, hpt, hp't, ?_⟩
  · rw [minkowskiProduct_self_eq_sq_sub, hps, hpt]
    simp [norm_smul, he₀, abs_of_pos hP, hPsq]
  · rw [minkowskiProduct_self_eq_sq_sub, hp's, hp't]
    simp [norm_smul, hu, abs_of_pos hP', hP'sq]
  · rw [hps, hp's, angle_smul_left_of_pos _ _ hP, angle_smul_right_of_pos _ _ hP']
    simp [angle, hu₀, he₀, hu, Real.arccos_cos h0 hπ]

/-- The Minkowski product is a symmetric bilinear form; in particular the reflexivity hypothesis
of `LightConeBasis.bilinForm_eq_plus_mul_minus_add` and
`LightConeBasis.isSelfAdjoint_transverseProj` holds for it (via `IsSymm.isRefl`). -/
theorem isSymm_toBilinForm_minkowskiProduct {d : ℕ} :
    (minkowskiProduct (d := d)).toBilinForm.IsSymm :=
  ⟨minkowskiProduct_symm⟩

end EpsilonEridani

namespace Lorentz
namespace Vector

open InnerProductSpace

/-- A vector Minkowski-orthogonal to a non-zero causal vector is space-like or light-like:
if `0 ≤ ⟪n, n⟫ₘ`, `n ≠ 0` and `⟪n, w⟫ₘ = 0`, then `⟪w, w⟫ₘ ≤ 0`. -/
lemma minkowskiProduct_self_nonpos_of_orthogonal_causal {d : ℕ} (n : Vector d) {w : Vector d}
    (hn : 0 ≤ ⟪n, n⟫ₘ) (hn0 : n ≠ 0) (hnw : ⟪n, w⟫ₘ = 0) : ⟪w, w⟫ₘ ≤ 0 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at hn hnw ⊢
  have hs := real_inner_self_nonneg (x := n.spatialPart)
  have ha : n.timeComponent ≠ 0 := by
    intro ha
    refine hn0 (eq_zero_of_timeComponent_of_spatialPart ha ?_)
    simp only [ha, mul_zero, zero_sub, neg_nonneg] at hn
    exact inner_self_eq_zero.mp (le_antisymm hn hs)
  have hcs := real_inner_mul_inner_self_le n.spatialPart w.spatialPart
  have hw := real_inner_self_nonneg (x := w.spatialPart)
  rw [← sub_eq_zero.mp hnw] at hcs
  have ha2 : 0 < n.timeComponent ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn hw]

end Vector
end Lorentz
