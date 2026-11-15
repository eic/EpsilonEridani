/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Extensions of the Minkowski product on Lorentz vectors

General facts about `Physlib`'s Minkowski product on `Lorentz.Vector d`, used downstream by the
kinematics of emission processes and of off-forward (generalized parton) kinematics. In
declaration order, the file contains:

* the expansion of the square of a difference, `⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`
  (`minkowskiProduct_sub_self`), companion to `Lorentz.Vector.minkowskiProduct_add_self`;
* the length of the spatial part of a vector, `√((p⁰)² - ⟪p, p⟫ₘ)`, which is `√((p⁰)² - m²)` on
  the mass shell `⟪p, p⟫ₘ = m²` (`norm_spatialPart_eq_sqrt_sq_sub_minkowskiProduct_self`);
* the Minkowski product of the vector `ofTimeAndSpatial x s` with time component `x` and spatial
  part `s` (defined in `EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions`),
  `⟪ofTimeAndSpatial x s, ofTimeAndSpatial x' s'⟫ₘ = x x' - ⟪s, s'⟫`
  (`minkowskiProduct_ofTimeAndSpatial_eq`);
* the causal-orthogonality bound: the Minkowski orthogonal complement of a non-zero causal
  (time-like or light-like) vector `n` contains no time-like vector, i.e. every `w` with
  `⟪n, w⟫ₘ = 0` has `⟪w, w⟫ₘ ≤ 0` (`minkowskiProduct_self_nonpos_of_causal_of_orthogonal`). For
  light-like `n`, in light-cone coordinates adapted to `n` the condition `⟪n, w⟫ₘ = 0` says that
  one light-cone component of `w` vanishes, so that `⟪w, w⟫ₘ = -‖w⊥‖²` is minus the square of the
  transverse part. This is the inequality behind lower bounds on momentum transfers at fixed
  light-cone momentum fractions, such as the minimal momentum transfer of off-forward parton
  kinematics;
* for a four-vector whose spatial part is `a • n` along a unit vector `n`, the factorisation
  `⟪v, v⟫ₘ = (v⁰ + a) (v⁰ - a)` of its Minkowski square into its light-cone components
  (`minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul`), its nullness when `v⁰ = a`
  (`minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul`), and its form
  `(v⁰)² - ⟪v.spatialPart, n⟫²` in terms of the component along `n`
  (`minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul`);
* the positivity of `√⟪v, v⟫ₘ` inside the forward light cone `‖v.spatialPart‖ < v⁰`
  (`sqrt_minkowskiProduct_self_pos`), so in particular when the spatial part is `a • n` with
  `|a| < v⁰` (`sqrt_minkowskiProduct_self_pos_of_spatialPart_eq_smul`);
* in at least two spatial dimensions, the existence of two vectors on the mass shell with
  prescribed energies above the mass and a prescribed angle between their spatial parts
  (`exists_massShell_pair_angle_eq`);
* the symmetry of the Minkowski product as a bilinear form
  (`isSymm_toBilinForm_minkowskiProduct`), the witness that supplies the `IsRefl` hypothesis of
  the reflexive-form results about light-cone bases in
  `EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.
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

/-- The Minkowski product of two vectors given by their time components and spatial parts is
`x x' - ⟪s, s'⟫`. -/
@[simp]
lemma minkowskiProduct_ofTimeAndSpatial_eq {d : ℕ} (x x' : ℝ) (s s' : EuclideanSpace ℝ (Fin d)) :
    ⟪ofTimeAndSpatial x s, ofTimeAndSpatial x' s'⟫ₘ = x * x' - ⟪s, s'⟫_ℝ := by
  simp [minkowskiProduct_eq_timeComponent_spatialPart]

/-- A vector Minkowski-orthogonal to a non-zero causal vector is space-like or light-like:
if `0 ≤ ⟪n, n⟫ₘ`, `n ≠ 0` and `⟪n, w⟫ₘ = 0`, then `⟪w, w⟫ₘ ≤ 0`. -/
lemma minkowskiProduct_self_nonpos_of_causal_of_orthogonal {d : ℕ} (w : Vector d) {n : Vector d}
    (hn : 0 ≤ ⟪n, n⟫ₘ) (hn0 : n ≠ 0) (hnw : ⟪n, w⟫ₘ = 0) : ⟪w, w⟫ₘ ≤ 0 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at hn hnw ⊢
  have hs := real_inner_self_nonneg (x := n.spatialPart)
  have ha : n.timeComponent ≠ 0 := by
    intro ha
    refine hn0 (eq_zero_of_timeComponent_of_spatialPart ha ?_)
    simp only [ha, mul_zero, zero_sub, neg_nonneg] at hn
    exact inner_self_eq_zero.mp (le_antisymm hn hs)
  -- Cauchy–Schwarz on the spatial parts: writing `s := n.spatialPart` and `t := w.spatialPart`,
  -- `⟪s, t⟫ * ⟪s, t⟫ ≤ ⟪s, s⟫ * ⟪t, t⟫`, where orthogonality `n⁰ w⁰ - ⟪s, t⟫ = 0` lets us
  -- replace `⟪s, t⟫` by `n⁰ w⁰`
  have hcs := real_inner_mul_inner_self_le n.spatialPart w.spatialPart
  have hw := real_inner_self_nonneg (x := w.spatialPart)
  rw [← sub_eq_zero.mp hnw] at hcs
  have ha2 : 0 < n.timeComponent ^ 2 := by positivity
  -- `(n⁰)² (w⁰)² ≤ ⟪s, s⟫ ⟪t, t⟫ ≤ (n⁰)² ⟪t, t⟫` by causality `⟪s, s⟫ ≤ (n⁰)²`; dividing
  -- by `(n⁰)² > 0` gives `(w⁰)² ≤ ⟪t, t⟫`
  nlinarith [mul_le_mul_of_nonneg_right hn hw]

/-- The Minkowski square of a four-vector whose spatial part is `a • n`, for a unit vector `n`, is
the product `(v⁰ + a) (v⁰ - a)` of its light-cone components along `n`. -/
theorem minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul {d : ℕ} {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) :
    ⟪v, v⟫ₘ = (v.timeComponent + a) * (v.timeComponent - a) := by
  rw [minkowskiProduct_self_eq_sq_sub, hv]
  simp only [norm_smul, hn, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- A four-vector of time component `a` whose spatial part is `a • n`, for a unit vector `n`, is
null: `⟪v, v⟫ₘ = 0`. -/
theorem minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul {d : ℕ}
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (ht : v.timeComponent = a)
    (hv : v.spatialPart = a • n) : ⟪v, v⟫ₘ = 0 := by
  rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hv, ht, sub_self, mul_zero]

/-- A four-vector inside the forward light cone, `‖v.spatialPart‖ < v⁰`, has positive invariant
mass: `0 < √⟪v, v⟫ₘ`. -/
theorem sqrt_minkowskiProduct_self_pos {d : ℕ} {v : Vector d}
    (h : ‖v.spatialPart‖ < v.timeComponent) : 0 < √⟪v, v⟫ₘ := by
  rw [Real.sqrt_pos, minkowskiProduct_self_eq_sq_sub, sub_pos]
  exact pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero

/-- A four-vector whose spatial part is `a • n`, for a unit vector `n`, with `|a| < v⁰` has positive
invariant mass: `0 < √⟪v, v⟫ₘ`. -/
theorem sqrt_minkowskiProduct_self_pos_of_spatialPart_eq_smul {d : ℕ} {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) : 0 < √⟪v, v⟫ₘ :=
  sqrt_minkowskiProduct_self_pos (by rwa [hv, norm_smul, hn, mul_one, Real.norm_eq_abs])

/-- The Minkowski square of a four-vector whose spatial part is `a • n`, for a unit vector `n`, is
`(v⁰)² - ⟪v.spatialPart, n⟫²`, the square of its time component minus the square of its
component along `n`. -/
theorem minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul {d : ℕ} {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) :
    ⟪v, v⟫ₘ = v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2 := by
  rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hv,
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hv, sq_sub_sq]

end Vector
end Lorentz

namespace EpsilonEridani

open Real InnerProductGeometry Lorentz.Vector
open scoped InnerProductSpace Lorentz.Vector

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
  let p := ofTimeAndSpatial E (P • e₀)
  let p' := ofTimeAndSpatial E' (P' • u)
  have hps : p.spatialPart = P • e₀ := spatialPart_ofTimeAndSpatial_eq ..
  have hp's : p'.spatialPart = P' • u := spatialPart_ofTimeAndSpatial_eq ..
  have hpt : p.timeComponent = E := timeComponent_ofTimeAndSpatial_eq ..
  have hp't : p'.timeComponent = E' := timeComponent_ofTimeAndSpatial_eq ..
  refine ⟨p, p', ?_, ?_, hpt, hp't, ?_⟩
  · rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul he₀ hps, hpt]
    linear_combination -hPsq
  · rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hu hp's, hp't]
    linear_combination -hP'sq
  · rw [hps, hp's, angle_smul_left_of_pos _ _ hP, angle_smul_right_of_pos _ _ hP']
    simp [angle, hu₀, he₀, hu, Real.arccos_cos h0 hπ]

/-- The Minkowski product is a symmetric bilinear form; in particular the reflexivity hypothesis
of `LightConeBasis.bilinForm_eq_plus_mul_minus_add` and
`LightConeBasis.isSelfAdjoint_transverseProj` holds for it (via `IsSymm.isRefl`). -/
theorem isSymm_toBilinForm_minkowskiProduct {d : ℕ} :
    (minkowskiProduct (d := d)).toBilinForm.IsSymm :=
  ⟨minkowskiProduct_symm⟩

end EpsilonEridani
