/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Extensions of the Minkowski product on Lorentz vectors

Facts about `Physlib`'s Minkowski product that the kinematics of an emission process uses: the
expansion of the square of a difference, `⟪u - v, u - v⟫ₘ = ⟪u, u⟫ₘ - 2 ⟪u, v⟫ₘ + ⟪v, v⟫ₘ`,
companion to `Lorentz.Vector.minkowskiProduct_add_self`; the length of the spatial part of a
vector on the mass shell `⟪p, p⟫ₘ = m²`, which is `√((p⁰)² - m²)`; and, in at least two spatial
dimensions, the existence of two vectors on the mass shell with prescribed energies above the mass
and a prescribed angle between their spatial parts.
-/

public section

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

/-- On the mass shell `⟪p, p⟫ₘ = m²`, the spatial part of `p` has length `√((p⁰)² - m²)`. -/
lemma norm_spatialPart_eq_sqrt {d : ℕ} {p : Vector d} {m : ℝ} (hp : ⟪p, p⟫ₘ = m ^ 2) :
    ‖p.spatialPart‖ = √(p.timeComponent ^ 2 - m ^ 2) := by
  rw [minkowskiProduct_self_eq_sq_sub] at hp
  rw [← Real.sqrt_sq (norm_nonneg p.spatialPart)]
  congr 1
  linarith

/-- In at least two spatial dimensions, for energies `E`, `E'` above `|m|` and an angle
`θ ∈ [0, π]`, there are two vectors on the mass shell `⟪p, p⟫ₘ = m²` with time components `E` and
`E'` whose spatial parts make the angle `θ`. -/
lemma exists_massShell_pair_angle_eq {d : ℕ} (hd : 2 ≤ d) {m E E' θ : ℝ} (hE : |m| < E)
    (hE' : |m| < E') (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    ∃ p p' : Vector d, ⟪p, p⟫ₘ = m ^ 2 ∧ ⟪p', p'⟫ₘ = m ^ 2 ∧ p.timeComponent = E ∧
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
  have he₀₁ : ⟪e₀, e₁⟫_ℝ = 0 := b.orthonormal.2 (by simp [Fin.ext_iff])
  have hu₀ : ⟪e₀, u⟫_ℝ = cos θ := by
    simp [u, inner_add_right, inner_smul_right, he₀, he₀₁]
  have hu : ‖u‖ = 1 := by
    have horth : ⟪cos θ • e₀, sin θ • e₁⟫_ℝ = 0 := by
      simp [inner_smul_left, inner_smul_right, he₀₁]
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
    rw [norm_smul, norm_smul, he₀, b.orthonormal.1, Real.norm_eq_abs, Real.norm_eq_abs] at h
    have h1 : ‖u‖ * ‖u‖ = 1 := by
      simp only [u]
      nlinarith [sq_abs (cos θ), sq_abs (sin θ), sin_sq_add_cos_sq θ]
    nlinarith [norm_nonneg u]
  let p : Vector d := fun μ => Sum.elim (fun _ => E) (fun i => (P • e₀) i) μ
  let p' : Vector d := fun μ => Sum.elim (fun _ => E') (fun i => (P' • u) i) μ
  have hps : p.spatialPart = P • e₀ := rfl
  have hp's : p'.spatialPart = P' • u := rfl
  have hpt : p.timeComponent = E := rfl
  have hp't : p'.timeComponent = E' := rfl
  refine ⟨p, p', ?_, ?_, hpt, hp't, ?_⟩
  · rw [minkowskiProduct_self_eq_sq_sub, hps, hpt, norm_smul, he₀, Real.norm_eq_abs,
      abs_of_pos hP]
    linarith
  · rw [minkowskiProduct_self_eq_sq_sub, hp's, hp't, norm_smul, hu, Real.norm_eq_abs,
      abs_of_pos hP']
    linarith
  · rw [hps, hp's, angle_smul_left_of_pos _ _ hP, angle_smul_right_of_pos _ _ hP', angle, hu₀,
      he₀, hu, mul_one, div_one, Real.arccos_cos h0 hπ]

end Vector
end Lorentz
