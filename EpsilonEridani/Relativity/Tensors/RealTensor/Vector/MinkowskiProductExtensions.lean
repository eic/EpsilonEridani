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
vector, `√((p⁰)² - ⟪p, p⟫ₘ)`, which is `√((p⁰)² - m²)` on the mass shell `⟪p, p⟫ₘ = m²`; and,
in at least two spatial dimensions, the existence of two vectors on the mass shell with prescribed
energies above the mass and a prescribed angle between their spatial parts.
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
  -- `Physlib` has no constructor from a time component and a spatial part with
  -- `timeComponent`/`spatialPart` lemmas, so `p` and `p'` are built as raw functions on
  -- `Fin 1 ⊕ Fin d`; `timeComponent` and `spatialPart` are the `abbrev`s `v (Sum.inl 0)` and
  -- `toLp (fun i => v (Sum.inr i))`, so the four component equations below hold by `rfl`.
  let p : Lorentz.Vector d := fun μ => Sum.elim (fun _ => E) (fun i => (P • e₀) i) μ
  let p' : Lorentz.Vector d := fun μ => Sum.elim (fun _ => E') (fun i => (P' • u) i) μ
  have hps : p.spatialPart = P • e₀ := rfl
  have hp's : p'.spatialPart = P' • u := rfl
  have hpt : p.timeComponent = E := rfl
  have hp't : p'.timeComponent = E' := rfl
  refine ⟨p, p', ?_, ?_, hpt, hp't, ?_⟩
  · rw [minkowskiProduct_self_eq_sq_sub, hps, hpt]
    simp [norm_smul, he₀, abs_of_pos hP, hPsq]
  · rw [minkowskiProduct_self_eq_sq_sub, hp's, hp't]
    simp [norm_smul, hu, abs_of_pos hP', hP'sq]
  · rw [hps, hp's, angle_smul_left_of_pos _ _ hP, angle_smul_right_of_pos _ _ hP']
    simp [angle, hu₀, he₀, hu, Real.arccos_cos h0 hπ]

end EpsilonEridani
