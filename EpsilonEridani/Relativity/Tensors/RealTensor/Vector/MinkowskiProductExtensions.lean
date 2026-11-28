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
* the bound of the virtuality of a vector by the square of its spatial momentum,
  `-⟪q, q⟫ₘ ≤ ‖q.spatialPart‖²`, which holds in every frame
  (`neg_minkowskiProduct_self_le_norm_spatialPart_sq`);
* the momentum transfer in the rest frame of the initial particle: if `p` is at rest with mass
  `m ≠ 0` and `p'` lies on the same mass shell, the transfer `q = p - p'` of virtuality
  `Q² = -⟪q, q⟫ₘ` has spatial momentum `‖q.spatialPart‖² = Q² (1 + Q² / (4 m²))`, at least `Q²`
  (`norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell`);
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

/-- The virtuality of a vector is at most the square of its spatial momentum:
`-⟪q, q⟫ₘ = ‖q.spatialPart‖² - (q⁰)² ≤ ‖q.spatialPart‖²`, in every frame. -/
lemma neg_minkowskiProduct_self_le_norm_spatialPart_sq {d : ℕ} (q : Vector d) :
    -⟪q, q⟫ₘ ≤ ‖q.spatialPart‖ ^ 2 := by
  rw [minkowskiProduct_self_eq_sq_sub]
  nlinarith [sq_nonneg q.timeComponent]

/-- **The momentum transfer in the rest frame.** If `p` is at rest (`p.spatialPart = 0`) with
time component `m ≠ 0`, and `p'` lies on the mass shell `⟪p', p'⟫ₘ = m²`, the transfer
`q = p - p'` of virtuality `Q² = -⟪q, q⟫ₘ` carries the spatial momentum
`‖q.spatialPart‖² = Q² (1 + Q² / (4 m²))`. -/
lemma norm_spatialPart_sub_sq_of_spatialPart_eq_zero_of_massShell {d : ℕ}
    {p p' : Vector d} {m : ℝ} (hm : m ≠ 0) (hp : p.spatialPart = 0) (hp0 : p.timeComponent = m)
    (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    ‖(p - p').spatialPart‖ ^ 2 =
      -⟪p - p', p - p'⟫ₘ * (1 + -⟪p - p', p - p'⟫ₘ / (4 * m ^ 2)) := by
  have hpp : ⟪p, p⟫ₘ = m ^ 2 := by
    simp [minkowskiProduct_self_eq_sq_sub, hp, hp0]
  have hpp' : ⟪p, p'⟫ₘ = m * p'.timeComponent := by
    simp [minkowskiProduct_eq_timeComponent_spatialPart, hp, hp0]
  have hs := minkowskiProduct_self_eq_sq_sub (p - p')
  have ht : (p - p').timeComponent = m - p'.timeComponent := by
    simp [hp0]
  rw [ht] at hs
  -- the virtuality fixes the energy transfer: `Q² = 2 m (p'⁰ - m)`
  have hQ : -⟪p - p', p - p'⟫ₘ = 2 * m * (p'.timeComponent - m) := by
    rw [minkowskiProduct_sub_self, hpp, hpp', hp']
    ring
  have h2 : 2 * m * (p'.timeComponent - m) * (2 * m * (p'.timeComponent - m) / (4 * m ^ 2)) =
      (p'.timeComponent - m) ^ 2 := by
    field_simp
    ring
  rw [hQ, mul_add, mul_one, h2]
  linear_combination hs + hQ

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
